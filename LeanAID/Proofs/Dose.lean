/-
  LeanAID.Proofs.Dose — the rates issued by the dosing decision (determine-basal.js
  lines 905-1188).
-/
import LeanAID.Proofs.Prelude

namespace LeanAID.Proofs

open JsNum
open Binary64 (rd rd_mono rd_nonneg rd_intCast)

@[simp] theorem addReasonIf_rate (r : Result) (b : Bool) (s : String) : (r.addReasonIf b s).rate = r.rate := by
  unfold Result.addReasonIf; cases b <;> rfl
@[simp] theorem addReasonIf_units (r : Result) (b : Bool) (s : String) : (r.addReasonIf b s).units = r.units := by
  unfold Result.addReasonIf; cases b <;> rfl

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
    `maxSafeBasal` is a non-negative number `M`, and the adjusted basal is an output
    of `round_basal` (the double nearest to `n/s`, `s ∈ {10, 20, 40}`) between 0 and
    `round_basal(M)`. -/
structure DoseHyp (c : Ctx) (M b : Rat) : Prop where
  hM : getMaxSafeBasal c.p = .fin M
  hM0 : 0 ≤ M
  hb : c.basal = .fin b
  hb0 : 0 ≤ b
  hbgrid : ∃ n : Int, ∃ s : Rat, 0 ≤ n ∧ (s = 10 ∨ s = 20 ∨ s = 40) ∧ b = rd ((n : Rat) / s)
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

theorem pow10_pos (d : Nat) : 0 < pow10 d := by
  induction d with
  | zero => decide
  | succ d ih => simp only [pow10]; grind

theorem rnd_fin (x : Rat) (d : Nat) : JsNum.round (.fin x) d = .fin (rts x (pow10 d)) := by
  have := pow10_pos d
  simp only [JsNum.round, JsNum.mul, JsNum.mathRound, JsNum.div, rts]
  split
  · grind
  · rfl

theorem pow10_two : pow10 2 = 100 := by decide +kernel
theorem pow10_zero : pow10 0 = 1 := rfl

/-- `rnd(y)` (to an integer) of a finite value is the double nearest an integer. -/
theorem rnd0_int (y : Rat) : ∃ N : Int, JsNum.round (.fin y) 0 = .fin (rd (N : Rat)) := by
  rw [rnd_fin, pow10_zero]
  exact ⟨roundInt (rd (y * 1)), by unfold rts; rw [show ((roundInt (rd (y * 1)) : Int) : Rat) / 1 = (roundInt (rd (y * 1)) : Rat) by grind]⟩

/-- **The SMB low temp stays at or below the basal.** For a basal `b = rd(n/s)`
    (an output of `round_basal`) and an integer duration `0 < N < 30`,
    `round(b · N / 30, 2) ≤ b`, in double arithmetic. -/
theorem smbLowTemp_bound {b : Rat} {n N : Int} {s : Rat} (hn : 0 ≤ n) (hs : s = 10 ∨ s = 20 ∨ s = 40)
    (hb : b = rd ((n : Rat) / s)) (hN0 : 0 < N) (hN : N < 30) :
    0 ≤ rts (rd (rd (b * N) / 30)) 100 ∧ rts (rd (rd (b * N) / 30)) 100 ≤ b := by
  have ht := tiny_pos; have ht' := tiny_le
  have hspos : 0 < s := by rcases hs with h | h | h <;> rw [h] <;> decide
  have hnR : (0 : Rat) ≤ n := by exact_mod_cast hn
  have hq0 : 0 ≤ (n : Rat) / s := div_nonneg' hspos hnR
  have hb0 : 0 ≤ b := by rw [hb]; exact rd_nonneg hq0
  have hNR : (1 : Rat) ≤ N := by exact_mod_cast hN0
  have hNR' : (N : Rat) ≤ 29 := by have : N ≤ 29 := by omega
                                   exact_mod_cast this
  -- the chain of roundings
  have hp1 : 0 ≤ b * N := Rat.mul_nonneg hb0 (by grind)
  have hbN : b * N ≤ b * 29 := Rat.mul_le_mul_of_nonneg_left hNR' hb0
  obtain ⟨-, b2⟩ := rd_close hq0
  rw [← hb] at b2
  obtain ⟨-, p1⟩ := rd_close hp1
  generalize hr1 : rd (b * N) = q1 at p1
  have hq1 : 0 ≤ q1 := by rw [← hr1]; exact rd_nonneg hp1
  have hq1' : 0 ≤ q1 / 30 := div_nonneg' (by decide) hq1
  obtain ⟨-, p2⟩ := rd_close hq1'
  generalize hr2 : rd (q1 / 30) = q2 at p2
  have hq2 : 0 ≤ q2 := by rw [← hr2]; exact rd_nonneg hq1'
  refine ⟨rts_nonneg (by decide) hq2, ?_⟩
  have hq3 : 0 ≤ q2 * 100 := Rat.mul_nonneg hq2 (by decide)
  obtain ⟨-, p3⟩ := rd_close hq3
  unfold rts
  have hK := roundInt_le (rd (q2 * 100))
  generalize roundInt (rd (q2 * 100)) = K at hK ⊢
  rw [hb]
  apply rd_mono
  rw [div_le_iff_le_mul (by decide)]
  -- K ≤ 100 · n / s; work with 2K ≤ 2 · 100 · n / s, an integer comparison
  rcases hs with h | h | h <;> subst h
  · have : (K : Rat) ≤ (n : Rat) * 10 := by
      have hlt : K < n * 10 + 1 := by
        have : (K : Rat) < (n : Rat) * 10 + 1 := by grind
        exact_mod_cast this
      have : K ≤ n * 10 := by omega
      exact_mod_cast this
    grind
  · have : (K : Rat) ≤ (n : Rat) * 5 := by
      have hlt : K < n * 5 + 1 := by
        have : (K : Rat) < (n : Rat) * 5 + 1 := by grind
        exact_mod_cast this
      have : K ≤ n * 5 := by omega
      exact_mod_cast this
    grind
  · -- s = 40: 100 n / 40 = 5n/2
    have : 2 * (K : Rat) ≤ (n : Rat) * 5 := by
      have hlt : 2 * K < n * 5 + 1 := by
        by_cases hn0 : n = 0
        · subst hn0
          have : (K : Rat) < 1 / 2 + 1 / 2 := by simp at b2; grind
          have : K < 1 := by exact_mod_cast (show (K : Rat) < 1 by grind)
          omega
        · have hn1 : (1 : Rat) ≤ n := by have : 1 ≤ n := by omega
                                         exact_mod_cast this
          have : 2 * (K : Rat) < (n : Rat) * 5 + 1 := by grind
          exact_mod_cast this
      have : 2 * K ≤ n * 5 := by omega
      exact_mod_cast this
    grind

/-- The SMB low temp (lines 1111-1122) is 0 or `round(basal · d / 30, 2)` for an
    integer duration `0 < d < 30`; it lies between 0 and the basal. -/
theorem smbLowTemp_rate {b : Rat} {n : Int} {s : Rat} (hn : 0 ≤ n) (hs : s = 10 ∨ s = 20 ∨ s = 40)
    (hbk : b = rd ((n : Rat) / s)) (d : JsNum) (hd : d = .nan ∨ ∃ N : Int, d = .fin (rd (N : Rat))) {r : Rat}
    (h : (smbLowTemp (.fin b) d).2 = .fin r) : 0 ≤ r ∧ r ≤ b := by
  have hspos : 0 < s := by rcases hs with h | h | h <;> rw [h] <;> decide
  have hb0 : 0 ≤ b := by rw [hbk]; exact rd_nonneg (div_nonneg' hspos (by exact_mod_cast hn))
  unfold smbLowTemp at h
  split at h
  · simp at h; subst h; exact ⟨Rat.le_refl, hb0⟩
  · split at h
    · simp at h; subst h; exact ⟨Rat.le_refl, hb0⟩
    · rename_i hle hge
      simp only at h
      rcases hd with hd | ⟨N, hd⟩
      · subst hd
        have e : (JsNum.fin b * JsNum.nan / 30) = JsNum.nan := rfl
        rw [rnd, e] at h; simp [JsNum.round] at h
      · subst hd
        simp only [JsNum.le, JsNum.ge, decide_eq_true_eq] at hle hge
        -- rd N is in (0, 30), so N is an integer in [1, 29] and rd N = N
        have hN30 : N < 30 := by
          by_cases hc : N < 30
          · exact hc
          · have := rd_mono (show ((30 : Int) : Rat) ≤ (N : Rat) by exact_mod_cast (show (30 : Int) ≤ N by omega))
            rw [rd_intCast (n := 30) (by decide)] at this; simp at this; grind
        have hN0 : 0 < N := by
          by_cases hc : 0 < N
          · exact hc
          · have := rd_mono (show (N : Rat) ≤ ((0 : Int) : Rat) by exact_mod_cast (show N ≤ 0 by omega))
            rw [rd_intCast (n := 0) (by decide)] at this; simp at this; grind
        have hNe : rd (N : Rat) = N := rd_intCast (by omega)
        rw [hNe] at h
        have e : (JsNum.fin b * .fin (N : Rat) / 30) = .fin (rd (rd (b * N) / 30)) := by
          show JsNum.div (JsNum.mul (.fin b) (.fin (N : Rat))) (.fin 30) = _
          simp [JsNum.mul, JsNum.div]
        rw [e, rnd, rnd_fin, pow10_two] at h
        injection h with h; subst h
        exact smbLowTemp_bound hn hs hbk hN0 hN30

/-- The SMB duration (lines 1111-1116) is `0`, `NaN`, or an integer rounded to a double. -/
theorem smbDurationReq_int (c : Ctx) (ir : JsNum) :
    smbDurationReq c ir = .nan ∨ ∃ N : Int, smbDurationReq c ir = .fin (rd (N : Rat)) := by
  unfold smbDurationReq
  simp only
  split
  · right; exact ⟨0, by simp [Binary64.rd_zero]⟩
  · generalize (60 * _ / c.p.current_basal.js) = y
    cases y with
    | nan => left; rfl
    | fin y => right; exact rnd0_int y

/-- The reason and units step of the SMB block does not change the rate. -/
theorem smbReasonUnits_rate (c : Ctx) (rT : Result) (ir : JsNum) (lt : JsNum × JsNum) :
    (smbReasonUnits c rT ir lt).rate = rT.rate := rfl

/-- `smbBlock` (lines 1076-1160) either returns with the SMB low temp, which is
    between 0 and the adjusted basal, or continues with the rate unchanged. -/
theorem smbBlock_rate {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) (ir : JsNum) :
    (∀ res, smbBlock c rT ir = .inl res → RateOk b res rT.rate) ∧
    (∀ res, smbBlock c rT ir = .inr res → res.rate = rT.rate) := by
  obtain ⟨n, s, hn, hs, hbk⟩ := H.hbgrid
  unfold smbBlock smbFinish
  constructor
  · intro res h
    split at h
    · injection h with h; subst h
      intro r hr
      right
      simp only [Option.some.injEq] at hr
      rw [H.hb] at hr
      exact smbLowTemp_rate hn hs hbk _ (smbDurationReq_int _ _) hr
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
