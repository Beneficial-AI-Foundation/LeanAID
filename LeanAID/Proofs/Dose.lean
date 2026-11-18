/-
  LeanAID.Proofs.Dose — the rates issued by the dosing decision (determine-basal.js
  lines 905-1188).
-/
import LeanAID.Proofs.Prelude

namespace LeanAID.Proofs

open JsNum

/-- A result issues no finite rate except within `[0, bound]`, or the rate `base`
    that the object already had. -/
def RateOk (bound : Rat) (res : Result) (base : Option JsNum) : Prop :=
  ∀ r, res.rate = some (.fin r) → base = some (.fin r) ∨ (0 ≤ r ∧ r ≤ bound)

theorem rateOk_of_stb {rate dur : JsNum} {p : Profile} {rT : Result} {ct : Option CurrentTemp} {M bound : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) (hb : rbR M p.model ≤ bound) :
    RateOk bound (setTempBasal rate dur p rT ct) rT.rate := by
  intro r h
  rcases setTempBasal_rate_bound hM hM0 h with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, Rat.le_trans h2 hb⟩

theorem rateOk_self (bound : Rat) (rT : Result) : RateOk bound rT rT.rate := fun _ h => Or.inl h

theorem rateOk_mono {b1 b2 : Rat} {res : Result} {base : Option JsNum} (h : RateOk b1 res base) (hb : b1 ≤ b2) :
    RateOk b2 res base := by
  intro r hr; rcases h r hr with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, Rat.le_trans h2 hb⟩

/-- The standing hypotheses of this file about a context `c` of the dose phase:
    `maxSafeBasal` is a non-negative number `M`, and the adjusted basal is a
    multiple of 0.025 between 0 and `round_basal(M)`. -/
structure DoseHyp (c : Ctx) (M b : Rat) : Prop where
  hM : getMaxSafeBasal c.p = .fin M
  hM0 : 0 ≤ M
  hb : c.basal = .fin b
  hb0 : 0 ≤ b
  hbgrid : ∃ k : Int, 0 ≤ k ∧ b = (k : Rat) / 40
  hbM : b ≤ rbR M c.p.model

theorem neutralTemp_rateOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) :
    RateOk (rbR M c.p.model) (neutralTemp c rT) rT.rate := by
  unfold neutralTemp
  split
  · exact rateOk_self _ _
  · exact rateOk_of_stb H.hM H.hM0 Rat.le_refl

/-- Close a `RateOk` goal for a result built from `setTempBasal`, `neutralTemp`,
    `addReason` and `if`s. -/
macro "rate_ok" H:term : tactic => `(tactic| (
  repeat' split
  all_goals first
    | exact rateOk_self _ _
    | exact rateOk_of_stb ($H).hM ($H).hM0 Rat.le_refl
    | exact neutralTemp_rateOk $H _))

theorem lowEventualBG_rateOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) :
    RateOk (rbR M c.p.model) (lowEventualBG c rT) rT.rate := by
  unfold lowEventualBG
  simp only
  rate_ok H

/-! ### The SMB low temp -/

theorem rnd_fin (x : Rat) (d : Nat) : JsNum.round (.fin x) d = .fin (rts x (pow10 d)) := rfl

theorem pow10_two : pow10 2 = 100 := by decide +kernel

/-- Rounding to 0.01 a value strictly below a multiple of 0.025 does not exceed it. -/
theorem rts100_le_grid {x : Rat} {k : Int} (hk : 0 ≤ k) (hx : x < (k : Rat) / 40) :
    rts x 100 ≤ (k : Rat) / 40 := by
  have hq1 : 2 * ((5 * k) / 2) ≤ 5 * k := by omega
  have hq2 : 5 * k - 1 ≤ 2 * ((5 * k) / 2) := by omega
  have hq1' : (2 : Rat) * (((5 * k) / 2 : Int) : Rat) ≤ 5 * (k : Rat) := by exact_mod_cast hq1
  have hq2' : 5 * (k : Rat) - 1 ≤ (2 : Rat) * (((5 * k) / 2 : Int) : Rat) := by exact_mod_cast hq2
  have h1 : rts x 100 ≤ (((5 * k) / 2 : Int) : Rat) / 100 := by
    apply rts_le_of_lt (by decide)
    have : x * 100 < (k : Rat) / 40 * 100 := Rat.mul_lt_mul_of_pos_right hx (by decide)
    have e : (k : Rat) / 40 * 100 = 5 * (k : Rat) / 2 := by grind
    grind
  have h2 : (((5 * k) / 2 : Int) : Rat) / 100 ≤ (k : Rat) / 40 := by
    rw [div_le_iff_le_mul (by decide)]; grind
  exact Rat.le_trans h1 h2

/-- The SMB low temp `round(basal * durationReq / 30, 2)` (line 1120) for
    `0 < durationReq < 30` is between 0 and the basal. -/
theorem smbLowTemp_bound {b d : Rat} {k : Int} (hk : 0 ≤ k) (hb : b = (k : Rat) / 40)
    (hd0 : 0 < d) (hd30 : d < 30) :
    0 ≤ rts (b * d / 30) 100 ∧ rts (b * d / 30) 100 ≤ b := by
  have hb0 : 0 ≤ b := by rw [hb]; exact div_nonneg' (by decide) (by exact_mod_cast hk)
  have hx0 : 0 ≤ b * d / 30 := div_nonneg' (by decide) (Rat.mul_nonneg hb0 (Rat.le_of_lt hd0))
  refine ⟨rts_nonneg (by decide) hx0, ?_⟩
  by_cases hbz : b = 0
  · have : b * d / 30 = 0 := by rw [hbz]; grind
    rw [this, hbz]
    have := rts_le_of_lt (x := 0) (s := 100) (n := 0) (by decide) (by decide +kernel)
    have e : ((0 : Int) : Rat) / 100 = 0 := by decide +kernel
    rw [e] at this; exact this
  · have hbpos : 0 < b := by grind
    rw [hb]; apply rts100_le_grid hk; rw [← hb]
    have : b * d < b * 30 := Rat.mul_lt_mul_of_pos_left hd30 hbpos
    rw [Rat.div_lt_iff (by decide)]; grind

/-- The SMB low temp (lines 1111-1122) is 0 or `round(basal · d / 30, 2)` with
    `0 < d < 30`; for a basal on the 0.025 grid it lies between 0 and the basal. -/
theorem smbLowTemp_rate {b : Rat} {k : Int} (hk : 0 ≤ k) (hbk : b = (k : Rat) / 40) (d : JsNum) {r : Rat}
    (h : (smbLowTemp (.fin b) d).2 = .fin r) : 0 ≤ r ∧ r ≤ b := by
  have hb0 : 0 ≤ b := by rw [hbk]; exact div_nonneg' (by decide) (by exact_mod_cast hk)
  unfold smbLowTemp at h
  split at h
  · simp at h; subst h; exact ⟨Rat.le_refl, hb0⟩
  · split at h
    · simp at h; subst h; exact ⟨Rat.le_refl, hb0⟩
    · rename_i hle hge
      simp only at h
      cases d with
      | nan =>
        have e : (JsNum.fin b * JsNum.nan / 30) = JsNum.nan := rfl
        rw [rnd, e] at h; simp [JsNum.round] at h
      | fin d =>
        simp only [JsNum.le, JsNum.ge, decide_eq_true_eq] at hle hge
        have hd0 : 0 < d := by grind
        have hd30 : d < 30 := by grind
        have e : (JsNum.fin b * .fin d / 30) = .fin (b * d / 30) := by
          show JsNum.div (JsNum.mul (.fin b) (.fin d)) (.fin 30) = _
          simp [JsNum.mul, JsNum.div]
        rw [e, rnd, rnd_fin, pow10_two] at h
        injection h with h; subst h
        exact smbLowTemp_bound hk hbk hd0 hd30

/-- The reason and units step of the SMB block does not change the rate. -/
theorem smbReasonUnits_rate (c : Ctx) (rT : Result) (ir : JsNum) (lt : JsNum × JsNum) :
    (smbReasonUnits c rT ir lt).rate = rT.rate := rfl

/-- `smbBlock` (lines 1076-1160) either returns with the SMB low temp, which is
    between 0 and the adjusted basal, or continues with the rate unchanged. -/
theorem smbBlock_rate {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) (ir : JsNum) :
    (∀ res, smbBlock c rT ir = .inl res → RateOk b res rT.rate) ∧
    (∀ res, smbBlock c rT ir = .inr res → res.rate = rT.rate) := by
  obtain ⟨k, hk, hbk⟩ := H.hbgrid
  unfold smbBlock smbFinish
  constructor
  · intro res h
    split at h
    · injection h with h; subst h
      intro r hr
      right
      simp only [Option.some.injEq] at hr
      rw [H.hb] at hr
      exact smbLowTemp_rate hk hbk _ hr
    · cases h
  · intro res h
    split at h
    · cases h
    · injection h with h; subst h
      exact smbReasonUnits_rate _ _ _ _

theorem highTempSet_rateOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) (rate ir : JsNum) :
    RateOk (rbR M c.p.model) (highTempSet c rT rate ir) rT.rate := by
  unfold highTempSet
  simp only
  rate_ok H

theorem highTemp_rateOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) :
    RateOk (rbR M c.p.model) (highTemp c rT) rT.rate := by
  unfold highTemp
  simp only
  generalize hs : (if (c.microBolusAllowed && c.enableSMB && c.bg >ʲ c.threshold) = true then _ else _) = s
  have hsm := smbBlock_rate H
  cases s with
  | inl res =>
    split at hs
    · have := (hsm _ _).1 res hs
      exact rateOk_mono (by
        intro r hr; rcases this r hr with h1 | h1
        · left; simpa [apply_ite] using h1
        · right; exact h1) H.hbM
    · cases hs
  | inr rT' =>
    have hr : rT'.rate = rT.rate := by
      split at hs
      · have := (hsm _ _).2 rT' hs; simpa [apply_ite] using this
      · injection hs with hs; subst hs; simp [apply_ite]
    simp only
    repeat' split
    all_goals
      intro r h
      rcases highTempSet_rateOk H _ _ _ r h with h1 | h1
      · left; rw [← hr]; simpa using h1
      · right; exact h1

theorem dbDoseRest_rateOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) :
    RateOk (rbR M c.p.model) (dbDose.dbDoseRest c rT) rT.rate := by
  unfold dbDose.dbDoseRest
  simp only
  repeat' split
  all_goals first
    | exact rateOk_self _ _
    | exact rateOk_of_stb H.hM H.hM0 Rat.le_refl
    | exact neutralTemp_rateOk H _
    | exact lowEventualBG_rateOk H _
    | exact highTemp_rateOk H _

/-- **The dosing decision issues rates within `[0, round_basal(maxSafeBasal)]`.** -/
theorem dbDose_rateOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) :
    RateOk (rbR M c.p.model) (dbDose c) c.rT.rate := by
  unfold dbDose
  simp only
  repeat' split
  all_goals first
    | exact rateOk_self _ _
    | exact rateOk_of_stb H.hM H.hM0 Rat.le_refl
    | exact dbDoseRest_rateOk H _

end LeanAID.Proofs
