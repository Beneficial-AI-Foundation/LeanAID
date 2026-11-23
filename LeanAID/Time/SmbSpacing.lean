import LeanAID.Time.Lift

/-!
# The SMB spacing guard in whole milliseconds

oref0 gives a microbolus only if `lastBolusAge c >ʲ smbInterval c.p`
(`smbGivesBolus`). `lastBolusAge` divides the elapsed milliseconds by 60000 and rounds
the result to one decimal, with binary64 operations. The UPPAAL model
(`docs/uppaal-plan.md`, section 4.1) replaces this guard by the clock constraint
`sinceBolus ≥ 60·I + 3` seconds. This file proves that replacement for whole
milliseconds.

**Theorems.**
- `smb_guard_iff`: for a whole-minute interval I in 1..10 and an elapsed time e in
  whole milliseconds, the reported age exceeds I exactly when e ≥ 60000·I + 3000.
  The proof checks e = 60000·I + 3000 and the millisecond before it for each I
  (`smbBoundary_all`, by the kernel), and uses monotonicity (`smbAge_mono`) for the
  rest. Nothing is claimed for a fractional elapsed time.
- `lastBolusAge_guard_iff`: the same for the guard of a context, with no bound on
  the times: the subtraction `now - lastBolusTime` is rounded to binary64, and the
  rounding is monotone and exact at the boundary values.
- `smb_spacing`: if the guard passes in a context whose `lastBolusTime` is a whole
  millisecond L, and L is at or after the time tb of a real prior bolus (the
  BolusSeen assumption, `docs/uppaal-plan.md` section 3), then at least
  60000·I + 3000 milliseconds passed since that bolus. BolusSeen is a hypothesis
  here, not a proved fact (F-22).

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time
open LeanAID JsNum

/-- Division of two finite numbers by a nonzero divisor. -/
theorem fin_div_fin (a b : Rat) (hb : b ≠ 0) : (JsNum.fin a) / (JsNum.fin b) = .fin (Binary64.rd (a / b)) := by
  show JsNum.div _ _ = _
  simp [JsNum.div, hb]

/-- The age in minutes that `round(d / 60000, 1)` gives for an elapsed time `d` in
    milliseconds, with binary64 rounding after each operation. -/
def smbAge (d : Rat) : Rat :=
  Binary64.rd ((roundInt (Binary64.rd (Binary64.rd (d / 60000) * 10)) : Rat) / 10)

/-- `round(d / 60000, 1)` is `smbAge d`. -/
theorem round_age (d : Rat) :
    JsNum.round ((JsNum.fin d) / 60000) 1 = .fin (smbAge d) := by
  unfold JsNum.round smbAge
  rw [show (60000 : JsNum) = .fin 60000 from rfl, fin_div_fin _ _ (by decide)]
  rw [show pow10 1 = 10 by decide +kernel]
  show JsNum.div (JsNum.mathRound (JsNum.mul _ _)) _ = _
  simp only [JsNum.mul, JsNum.mathRound]
  rw [show (JsNum.div (.fin _) (.fin 10)) = _ from fin_div_fin _ _ (by decide)]

/-- `lastBolusAge` is `smbAge` of the elapsed time after its binary64 rounding. -/
theorem lastBolusAge_eq (c : Ctx) (L : Rat) (hL : c.iobd.lastBolusTime.js = .fin L) :
    lastBolusAge c = .fin (smbAge (Binary64.rd (c.clock.now - L))) := by
  unfold lastBolusAge rnd
  rw [hL, ← round_age]
  rfl

/-- `smbAge` is monotone. -/
theorem smbAge_mono {d e : Rat} (h : d ≤ e) : smbAge d ≤ smbAge e := by
  unfold smbAge
  apply Binary64.rd_mono
  have h2 : d / 60000 ≤ e / 60000 := by
    rw [Rat.div_def, Rat.div_def]; exact Rat.mul_le_mul_of_nonneg_right h (by decide +kernel)
  have h3 := Binary64.rd_mono h2
  have h4 := Binary64.rd_mono (Rat.mul_le_mul_of_nonneg_right h3 (by decide : (0:Rat) ≤ 10))
  have h5 : roundInt (Binary64.rd (Binary64.rd (d / 60000) * 10))
      ≤ roundInt (Binary64.rd (Binary64.rd (e / 60000) * 10)) := by
    unfold roundInt; exact Rat.floor_monotone (by grind)
  have h6 : ((roundInt (Binary64.rd (Binary64.rd (d / 60000) * 10)) : Int) : Rat)
      ≤ (roundInt (Binary64.rd (Binary64.rd (e / 60000) * 10)) : Rat) := by
    exact_mod_cast h5
  rw [Rat.div_def, Rat.div_def]; exact Rat.mul_le_mul_of_nonneg_right h6 (by decide +kernel)

/-- The guard at the two boundary values, as the kernel computes it. -/
def smbBoundary (I : Nat) : Bool :=
  (JsNum.round ((JsNum.fin ((60000 * I + 3000 : Nat) : Rat)) / 60000) 1 >ʲ .fin (I : Rat)) &&
  !(JsNum.round ((JsNum.fin ((60000 * I + 2999 : Nat) : Rat)) / 60000) 1 >ʲ .fin (I : Rat))

/-- The boundary checks hold for every whole-minute interval in 1..10. -/
theorem smbBoundary_all : (List.range 10).all (fun i => smbBoundary (i + 1)) = true := by
  decide +kernel

/-- The boundary values of `smbAge` for one interval. -/
theorem smbAge_boundary {I : Nat} (h1 : 1 ≤ I) (h10 : I ≤ 10) :
    (I : Rat) < smbAge (60000 * (I : Int) + 3000 : Int) ∧
    smbAge (60000 * (I : Int) + 2999 : Int) ≤ (I : Rat) := by
  have hb : smbBoundary I = true := by
    have := List.all_eq_true.mp smbBoundary_all (I - 1) (List.mem_range.mpr (by omega))
    simpa [show I - 1 + 1 = I by omega] using this
  unfold smbBoundary at hb
  rw [round_age, round_age] at hb
  simp only [JsNum.gt, JsNum.lt, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at hb
  have c1 : (((60000 * I + 3000 : Nat) : Rat)) = ((60000 * (I : Int) + 3000 : Int) : Rat) := by
    push_cast; rfl
  have c2 : (((60000 * I + 2999 : Nat) : Rat)) = ((60000 * (I : Int) + 2999 : Int) : Rat) := by
    push_cast; rfl
  rw [c1, c2] at hb
  exact ⟨hb.1, Rat.not_lt.mp hb.2⟩

/-- **The SMB guard in whole milliseconds.** For a whole-minute interval `I` in 1..10
    and an elapsed time `e` in whole milliseconds, the reported age exceeds `I` exactly
    when `e ≥ 60000·I + 3000`. -/
theorem smb_guard_iff {I : Nat} (h1 : 1 ≤ I) (h10 : I ≤ 10) (e : Int) :
    (I : Rat) < smbAge e ↔ 60000 * (I : Int) + 3000 ≤ e := by
  obtain ⟨hlo, hhi⟩ := smbAge_boundary h1 h10
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have hle : ((e : Int) : Rat) ≤ ((60000 * (I : Int) + 2999 : Int) : Rat) :=
      Rat.intCast_le_intCast.mpr (by omega)
    have := smbAge_mono hle
    grind
  · intro h
    have hle : ((60000 * (I : Int) + 3000 : Int) : Rat) ≤ ((e : Int) : Rat) :=
      Rat.intCast_le_intCast.mpr h
    have := smbAge_mono hle
    grind

/-- `rd` fixes the boundary values `60000·I + 3000` and `60000·I + 2999`. -/
private theorem rd_boundary (I : Nat) (h10 : I ≤ 10) (k : Int) (hk : 0 ≤ k ∧ k ≤ 3000) :
    Binary64.rd ((60000 * (I : Int) + k : Int) : Rat) = ((60000 * (I : Int) + k : Int) : Rat) :=
  Binary64.rd_intCast (by omega)

/-- **The SMB guard of a context in whole milliseconds.** For a whole-minute interval
    `I` in 1..10, if `lastBolusTime` is a whole millisecond `L`, the guard
    `lastBolusAge c >ʲ I` passes exactly when `now - L ≥ 60000·I + 3000`. There is no
    bound on the times: the subtraction is rounded to binary64 first, and the
    rounding is monotone and exact at the two boundary values. -/
theorem lastBolusAge_guard_iff {c : Ctx} {I : Nat} (h1 : 1 ≤ I) (h10 : I ≤ 10) {L : Int}
    (hL : c.iobd.lastBolusTime.js = .fin L) :
    (lastBolusAge c >ʲ .fin (I : Rat)) = true ↔ 60000 * (I : Int) + 3000 ≤ c.clock.now - L := by
  obtain ⟨hlo, hhi⟩ := smbAge_boundary h1 h10
  rw [lastBolusAge_eq c L hL]
  simp only [JsNum.gt, JsNum.lt, decide_eq_true_eq]
  have hd : ((c.clock.now : Rat) - (L : Rat)) = ((c.clock.now - L : Int) : Rat) := by push_cast; rfl
  rw [hd]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have hle : ((c.clock.now - L : Int) : Rat) ≤ ((60000 * (I : Int) + 2999 : Int) : Rat) :=
      Rat.intCast_le_intCast.mpr (by omega)
    have h2 := Binary64.rd_mono hle
    rw [rd_boundary I h10 2999 (by omega)] at h2
    have := smbAge_mono h2
    grind
  · intro h
    have hle : ((60000 * (I : Int) + 3000 : Int) : Rat) ≤ ((c.clock.now - L : Int) : Rat) :=
      Rat.intCast_le_intCast.mpr h
    have h2 := Binary64.rd_mono hle
    rw [rd_boundary I h10 3000 (by omega)] at h2
    have := smbAge_mono h2
    grind

/-- **SMB spacing under BolusSeen.** If the guard passes for a whole-minute interval
    `I` in 1..10, and `lastBolusTime` is a whole millisecond `L` at or after the time
    `tb` of a real prior bolus, then at least `60000·I + 3000` milliseconds passed since
    that bolus. -/
theorem smb_spacing {c : Ctx} {I : Nat} (h1 : 1 ≤ I) (h10 : I ≤ 10)
    (hI : smbInterval c.p = .fin I) {L tb : Int}
    (hL : c.iobd.lastBolusTime.js = .fin L) (hseen : tb ≤ L)
    (hg : (lastBolusAge c >ʲ smbInterval c.p) = true) :
    60000 * (I : Int) + 3000 ≤ c.clock.now - tb := by
  rw [hI] at hg
  have := (lastBolusAge_guard_iff h1 h10 hL).mp hg
  omega

end LeanAID.Time
