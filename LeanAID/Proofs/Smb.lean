/-
  LeanAID.Proofs.Smb — microboluses (SMB): where `units` can be set, and the
  limits it obeys (H2), and the "no microbolus" half of H4.
-/
import LeanAID.Proofs.MaxIob

namespace LeanAID.Proofs

open JsNum
open Binary64 (rd rd_mono rd_nonneg)

/-- The insulinReq the SMB block receives (lines 1058-1068), for a dose context. -/
def smbInsulinReq (c : Ctx) : JsNum :=
  JsNum.round (capInsulinReq (JsNum.round ((JsNum.min c.minPredBG c.eventualBG' - c.target_bg) / c.sens) 2)
    (c.max_iob - c.iobd.iob.js)) 3

/-- A microbolus `u` was decided by the SMB block. -/
def SmbBolus (c : Ctx) (u : JsNum) : Prop :=
  smbGivesBolus c (smbInsulinReq c) = true ∧ u = smbMicroBolus c (smbInsulinReq c)

/-- `units` is unchanged, or set by the SMB block. -/
def UnitsOk (c : Ctx) (res : Result) (base : Option JsNum) : Prop :=
  ∀ u, res.units = some u → base = some u ∨ SmbBolus c u

theorem unitsOk_eq {c : Ctx} {res rT : Result} (h : res.units = rT.units) : UnitsOk c res rT.units :=
  fun u hu => Or.inl (h ▸ hu)

theorem neutralTemp_units (c : Ctx) (rT : Result) : (neutralTemp c rT).units = rT.units := by
  unfold neutralTemp; split <;> simp

theorem lowEventualBG_units (c : Ctx) (rT : Result) : (lowEventualBG c rT).units = rT.units := by
  unfold lowEventualBG
  simp only
  repeat' split
  all_goals first | rfl | simp | exact neutralTemp_units _ _ | (rw [neutralTemp_units]; rfl)

theorem highTempSet_units (c : Ctx) (rT : Result) (rate ir : JsNum) :
    (highTempSet c rT rate ir).units = rT.units := by
  unfold highTempSet
  simp only
  repeat' split
  all_goals first | rfl | simp

theorem smbReasonUnits_units (c : Ctx) (rT : Result) (ir : JsNum) (lt : JsNum × JsNum) :
    (smbReasonUnits c rT ir lt).units =
      if smbGivesBolus c ir then some (smbMicroBolus c ir) else rT.units := rfl

theorem highTemp_units (c : Ctx) (rT : Result) : UnitsOk c (highTemp c rT) rT.units := by
  unfold highTemp
  simp only
  generalize hs : (if (c.microBolusAllowed && c.enableSMB && c.bg >ʲ c.threshold) = true then _ else _) = s
  intro u hu
  -- the units after the SMB block, whichever way it exits
  have key : ∀ rT0 : Result, rT0.units = rT.units →
      ∀ r : Result, (r = smbReasonUnits c rT0 (smbInsulinReq c)
        (smbLowTemp c.basal (smbDurationReq c (smbInsulinReq c)))) → r.units = some u →
      rT.units = some u ∨ SmbBolus c u := by
    intro rT0 h0 r hr hru
    subst hr
    rw [smbReasonUnits_units] at hru
    split at hru
    · right; rename_i hg; injection hru with hru; exact ⟨hg, hru.symm⟩
    · left; rw [← h0]; exact hru
  cases s with
  | inl res =>
    split at hs
    · unfold smbBlock smbFinish at hs
      split at hs
      · injection hs with hs; subst hs
        exact key _ (by simp) _ rfl hu
      · cases hs
    · cases hs
  | inr rT' =>
    simp only at hu
    have hu' : rT'.units = some u := by
      split at hu <;> (rw [highTempSet_units] at hu; first | exact hu | simpa using hu)
    split at hs
    · unfold smbBlock smbFinish at hs
      split at hs
      · cases hs
      · injection hs with hs; subst hs
        exact key _ (by simp) _ rfl hu'
    · injection hs with hs; subst hs
      left; simpa using hu'

theorem dbDose_units (c : Ctx) : UnitsOk c (dbDose c) c.rT.units := by
  have rest : ∀ rT : Result, rT.units = c.rT.units → UnitsOk c (dbDose.dbDoseRest c rT) c.rT.units := by
    intro rT h0
    unfold dbDose.dbDoseRest
    simp only
    repeat' split
    all_goals first
      | exact unitsOk_eq (by simp [h0])
      | exact unitsOk_eq (by rw [neutralTemp_units]; simp [h0])
      | exact unitsOk_eq (by rw [lowEventualBG_units]; simp [h0])
      | (intro u hu; rcases highTemp_units c _ u hu with h | h
         · left; rw [← h0]; simpa using h
         · right; exact h)
  unfold dbDose
  simp only
  split
  · exact rest _ (by simp)
  · split
    · exact unitsOk_eq (by simp)
    · exact rest _ rfl

/-! ### Arithmetic of the microbolus -/

theorem floor_div_le {z k : Rat} (hk : 0 < k) : ((z * k).floor : Rat) / k ≤ z := by
  rw [div_le_iff_le_mul hk]; exact Rat.floor_le _

/-- The bolus increment is positive (for a valid profile). -/
theorem smbBolusIncrement_pos {p : Profile} (h : ∀ x : Rat, p.bolus_increment = some (.fin x) → 0 < x) :
    ∃ x, smbBolusIncrement p = .fin x ∧ 0 < x := by
  unfold smbBolusIncrement
  cases hb : p.bolus_increment with
  | none => exact ⟨_, rfl, by decide +kernel⟩
  | some v =>
    cases v with
    | nan => exact ⟨_, rfl, by decide +kernel⟩
    | fin x =>
      have hx := h x hb
      have : x ≠ 0 := by grind
      simp [this]; exact hx

/-- **The microbolus is at most half the insulinReq and at most maxBolus**, up to
    double rounding: `u ≤ X + X/2^50 + 2^-90` for `X` = `insulinReq/2` and `X` =
    `maxBolus`. (In doubles `floor(y·k)/k` can round one ulp above `y`.) A positive
    microbolus also needs a positive insulinReq and a positive maxBolus. -/
theorem smbMicroBolus_le {c : Ctx} {ir u : Rat} (hinc : ∀ x : Rat, c.p.bolus_increment = some (.fin x) → 0 < x)
    (h : smbMicroBolus c (.fin ir) = .fin u) (hu0 : 0 < u) :
    0 < ir ∧ u ≤ ir / 2 + ir / 2 ^ 50 + 1 / 2 ^ 90 ∧
      ∀ mb, smbMaxBolus c = .fin mb → 0 < mb ∧ u ≤ mb + mb / 2 ^ 50 + 1 / 2 ^ 90 := by
  have ht := tiny_pos; have ht' := tiny_le
  obtain ⟨x, hx, hx0⟩ := smbBolusIncrement_pos hinc
  unfold smbMicroBolus at h
  rw [hx] at h
  rw [show (1 : JsNum) = .fin 1 from rfl, JsNum.fin_div (by grind : x ≠ 0)] at h
  have hk0 : 0 ≤ rd (1 / x) := rd_nonneg (Rat.le_of_lt (by rw [Rat.lt_div_iff hx0]; grind))
  generalize rd (1 / x) = k at h hk0
  cases hmb : smbMaxBolus c with
  | nan => rw [hmb] at h; simp at h
  | fin mb =>
    rw [hmb] at h
    rw [show (2 : JsNum) = .fin 2 from rfl, JsNum.fin_div (by decide : (2 : Rat) ≠ 0)] at h
    simp only [JsNum.min_fin, JsNum.fin_mul, JsNum.mathFloor] at h
    by_cases hk : k = 0
    · subst hk
      rw [show ∀ a : Rat, (JsNum.fin a / JsNum.fin 0) = JsNum.nan from
        fun a => by show JsNum.div _ _ = _; simp [JsNum.div]] at h
      cases h
    rw [JsNum.fin_div hk] at h
    injection h with h
    have hkpos : 0 < k := by grind
    have hy : (if rd (ir / 2) ≤ mb then rd (ir / 2) else mb) ≤ rd (ir / 2) ∧
        (if rd (ir / 2) ≤ mb then rd (ir / 2) else mb) ≤ mb := by split <;> grind
    generalize (if rd (ir / 2) ≤ mb then rd (ir / 2) else mb) = y at h hy
    -- u = rd (f / k), f = ⌊rd (y·k)⌋
    have hf : (0 : Rat) < ((rd (y * k)).floor : Rat) / k := by
      by_cases hc : (0 : Rat) < ((rd (y * k)).floor : Rat) / k
      · exact hc
      · have := Binary64.rd_nonpos (show ((rd (y * k)).floor : Rat) / k ≤ 0 by grind)
        grind
    have hf1 : (1 : Rat) ≤ ((rd (y * k)).floor : Rat) := by
      have h0 : (0 : Rat) < ((rd (y * k)).floor : Rat) := by
        rw [Rat.lt_div_iff hkpos] at hf; grind
      have : 0 < (rd (y * k)).floor := by exact_mod_cast h0
      exact_mod_cast (show 1 ≤ (rd (y * k)).floor by omega)
    have hzf := Rat.floor_le (rd (y * k))
    have hyk : 0 < y * k := by
      by_cases hc : 0 < y * k
      · exact hc
      · have := Binary64.rd_nonpos (show y * k ≤ 0 by grind); grind
    have hypos : 0 < y := by
      by_cases hc : 0 < y
      · exact hc
      · have : y * k ≤ 0 * k := Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hkpos); grind
    obtain ⟨-, z2⟩ := rd_close (Rat.le_of_lt hyk)
    -- y·k ≥ 1/2, so the absolute error is small relative to y·k
    have hyk2 : 1 / 2 ≤ y * k := by grind
    have hfk : ((rd (y * k)).floor : Rat) ≤ y * k + y * k / 2 ^ 52 := by grind
    have hfk' : ((rd (y * k)).floor : Rat) / k ≤ y + y / 2 ^ 52 := by
      rw [div_le_iff_le_mul hkpos]
      have : (y + y / 2 ^ 52) * k = y * k + y * k / 2 ^ 52 := by grind
      grind
    obtain ⟨-, u2⟩ := rd_close (Rat.le_of_lt hf)
    rw [h] at u2
    have hu : u ≤ y + y / 2 ^ 51 + tiny := by grind
    -- the two bounds on y
    have hir2 : 0 < rd (ir / 2) := by grind
    have hir : 0 < ir := by
      by_cases hc : 0 < ir
      · exact hc
      · have := Binary64.rd_nonpos (show ir / 2 ≤ 0 by grind); grind
    obtain ⟨-, r2⟩ := rd_close (show 0 ≤ ir / 2 by grind)
    refine ⟨hir, by grind, ?_⟩
    intro mb' hmb'; injection hmb' with hmb'; subst hmb'
    exact ⟨by grind, by grind⟩

/-- `round(x, 3)` is positive only if `rd(1000·x) ≥ 1/2`, and then
    `round(x, 3) ≤ x + 1/2000` up to double rounding. -/
theorem rts1000_facts {x : Rat} (h : 0 < rts x 1000) :
    1 / 2 ≤ rd (x * 1000) ∧ (0 ≤ x → rts x 1000 * 1000 ≤
      (x * 1000 + x * 1000 / 9007199254740992 + tiny + 1/2) * (1 + 1 / 9007199254740992) + tiny * 1000) := by
  constructor
  · by_cases hx : rd (x * 1000) < 1/2
    · exfalso
      have := rts_le_of_lt (x := x) (s := 1000) (n := 0) (by decide) (by grind)
      rw [show ((0 : Int) : Rat) / 1000 = 0 by decide +kernel, Binary64.rd_zero] at this
      grind
    · grind
  · intro h0; exact rts_le_add (by decide) h0

theorem pow10_three : pow10 3 = 1000 := by decide +kernel

/-- **The arithmetic core of H2.** A positive microbolus `u` with insulinReq
    `round(cap(ir0, room), 3)` satisfies `u ≤ room` up to double rounding
    (`room = max_iob − iob`, itself a double): `u ≤ room + room/2^45 + 2^-80`. -/
theorem microbolus_le_room {c : Ctx} {u room : Rat}
    (hinc : ∀ x : Rat, c.p.bolus_increment = some (.fin x) → 0 < x)
    (hroom : c.max_iob - c.iobd.iob.js = .fin room) (hu : SmbBolus c (.fin u)) (hu0 : 0 < u) :
    0 < room ∧ u ≤ room + room / 2 ^ 45 + 1 / 2 ^ 80 := by
  have ht := tiny_pos; have ht' := tiny_le
  obtain ⟨-, hu⟩ := hu
  unfold smbInsulinReq at hu
  rw [hroom] at hu
  generalize hcap : capInsulinReq _ (.fin room) = cap at hu
  have hcapb : cap = .nan ∨ ∃ v, cap = .fin v ∧ v ≤ room := by
    rw [← hcap]; unfold capInsulinReq; split
    · right; exact ⟨room, rfl, Rat.le_refl⟩
    · rename_i hc
      generalize JsNum.round _ 2 = ir0 at hc ⊢
      cases ir0 with
      | nan => left; rfl
      | fin v => right; exact ⟨v, rfl, by simp at hc; grind⟩
  rcases hcapb with h | ⟨v, h, hv⟩
  · subst h
    exfalso
    unfold smbMicroBolus at hu
    obtain ⟨x, hx, -⟩ := smbBolusIncrement_pos hinc
    simp [hx, JsNum.round] at hu
  · subst h
    rw [rnd_fin, pow10_three] at hu
    obtain ⟨hir, hle, -⟩ := smbMicroBolus_le hinc hu.symm hu0
    obtain ⟨h1, h2⟩ := rts1000_facts hir
    -- v is at least about 1/2000
    have hv0 : 0 ≤ v := by
      by_cases hc : 0 ≤ v
      · exact hc
      · have := Binary64.rd_nonpos (show v * 1000 ≤ 0 by grind); grind
    obtain ⟨-, w2⟩ := rd_close (show 0 ≤ v * 1000 by grind)
    have h2 := h2 hv0
    exact ⟨by grind, by grind⟩

end LeanAID.Proofs
