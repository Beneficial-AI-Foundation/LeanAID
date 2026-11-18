/-
  LeanAID.Proofs.Smb — microboluses (SMB): where `units` can be set, and the
  limits it obeys (H2), and the "no microbolus" half of H4.
-/
import LeanAID.Proofs.MaxIob

namespace LeanAID.Proofs

open JsNum

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

/-- The microbolus is at most half the insulinReq and at most maxBolus. -/
theorem smbMicroBolus_le {c : Ctx} {ir u : Rat} (hinc : ∀ x : Rat, c.p.bolus_increment = some (.fin x) → 0 < x)
    (h : smbMicroBolus c (.fin ir) = .fin u) :
    u ≤ ir / 2 ∧ ∀ mb, smbMaxBolus c = .fin mb → u ≤ mb := by
  obtain ⟨x, hx, hx0⟩ := smbBolusIncrement_pos hinc
  unfold smbMicroBolus at h
  rw [hx] at h
  have hk : (1 : Rat) / x ≠ 0 := by
    intro h0; have : (1 : Rat) / x * x = 0 := by rw [h0]; grind
    rw [Rat.div_mul_cancel (by grind)] at this; cases this
  have hkpos : 0 < (1 : Rat) / x := by rw [Rat.lt_div_iff hx0]; grind
  rw [show (1 : JsNum) = .fin 1 from rfl, JsNum.fin_div (by grind : x ≠ 0)] at h
  cases hmb : smbMaxBolus c with
  | nan => rw [hmb] at h; simp at h
  | fin mb =>
    rw [hmb] at h
    rw [show (2 : JsNum) = .fin 2 from rfl, JsNum.fin_div (by decide : (2 : Rat) ≠ 0)] at h
    simp only [JsNum.min_fin, JsNum.fin_mul, JsNum.mathFloor] at h
    rw [JsNum.fin_div hk] at h
    injection h with h
    subst h
    have hle := floor_div_le (z := if ir / 2 ≤ mb then ir / 2 else mb) hkpos
    constructor
    · split at hle <;> grind
    · intro mb' hmb'; injection hmb' with hmb'; subst hmb'; split at hle <;> grind

/-- `round(x, 3)` exceeds `x` by at most 1/2000, and is positive only if `x ≥ 1/2000`. -/
theorem rts1000_facts (x : Rat) : rts x 1000 ≤ x + 1/2000 ∧ (0 < rts x 1000 → 1/2000 ≤ x) := by
  constructor
  · have := rts_mul_le (x := x) (s := 1000) (by decide); grind
  · intro h
    by_cases hx : x < 1/2000
    · exfalso
      have := rts_le_of_lt (x := x) (s := 1000) (n := 0) (by decide) (by grind)
      rw [show ((0 : Int) : Rat) / 1000 = 0 by decide +kernel] at this
      grind
    · grind

theorem pow10_three : pow10 3 = 1000 := by decide +kernel

/-- **The arithmetic core of H2.** A positive microbolus `u` with insulinReq
    `round(cap(ir0, room), 3)` satisfies `u ≤ room`: it never takes IOB above
    `max_iob` (`room = max_iob − iob`). -/
theorem microbolus_le_room {c : Ctx} {u room : Rat}
    (hinc : ∀ x : Rat, c.p.bolus_increment = some (.fin x) → 0 < x)
    (hroom : c.max_iob - c.iobd.iob.js = .fin room) (hu : SmbBolus c (.fin u)) (hu0 : 0 < u) : u ≤ room := by
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
    obtain ⟨hle, -⟩ := smbMicroBolus_le hinc hu.symm
    obtain ⟨h1, h2⟩ := rts1000_facts v
    have hpos : 0 < rts v 1000 := by grind
    have := h2 hpos
    grind

end LeanAID.Proofs
