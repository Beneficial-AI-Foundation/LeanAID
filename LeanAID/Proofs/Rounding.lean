/-
  LeanAID.Proofs.Rounding — properties of JavaScript `Math.round`, oref0's
  `round(value, digits)` and `round_basal`.
-/
import LeanAID.Core.RoundBasal
import LeanAID.Proofs.JsNumLemmas

namespace LeanAID.Proofs

open JsNum

/-! ### Small order lemmas on `Rat` -/

theorem div_le_iff_le_mul {a b c : Rat} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  constructor
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_lt.mpr h ((Rat.lt_div_iff hb).mpr h')
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_lt.mpr h ((Rat.lt_div_iff hb).mp h')

theorem le_div_iff_mul_le {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  constructor
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_lt.mpr h ((Rat.div_lt_iff hc).mpr h')
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_lt.mpr h ((Rat.div_lt_iff hc).mp h')

theorem div_le_div_of_le {a b c : Rat} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_le_iff_le_mul hc, Rat.div_mul_cancel (by grind)]; exact h

theorem div_nonneg' {a c : Rat} (hc : 0 < c) (h : 0 ≤ a) : 0 ≤ a / c := by
  rw [le_div_iff_mul_le hc]; grind

/-! ### `Math.round` -/

theorem roundInt_mono {a b : Rat} (h : a ≤ b) : roundInt a ≤ roundInt b :=
  Rat.floor_monotone (by grind)

/-- `Math.round(a) ≤ a + 1/2` -/
theorem roundInt_le (a : Rat) : (roundInt a : Rat) ≤ a + 1/2 := Rat.floor_le _

/-- `a - 1/2 < Math.round(a)` -/
theorem lt_roundInt (a : Rat) : a - 1/2 < (roundInt a : Rat) := by
  have := Rat.lt_floor_add_one (a + 1/2)
  unfold roundInt
  have h2 : ((((a + 1/2).floor + 1 : Int)) : Rat) = ((a + 1/2).floor : Rat) + 1 := by simp
  grind

/-- `Math.round(n) = n` for integers. -/
theorem roundInt_intCast (n : Int) : roundInt (n : Rat) = n := by
  unfold roundInt
  rw [Rat.add_comm, Rat.floor_add_intCast]
  have : (1/2 : Rat).floor = 0 := by decide +kernel
  omega

/-- `Math.round(a) ≤ n` iff `a < n + 1/2`. -/
theorem roundInt_le_iff {a : Rat} {n : Int} : roundInt a ≤ n ↔ a < (n : Rat) + 1/2 := by
  unfold roundInt
  constructor
  · intro h
    have : (a + 1/2).floor < n + 1 := by omega
    have := Rat.floor_lt_iff.mp this
    simp at this; grind
  · intro h
    have : (a + 1/2).floor < n + 1 := Rat.floor_lt_iff.mpr (by simp; grind)
    omega

/-- `n ≤ Math.round(a)` iff `n - 1/2 ≤ a`. -/
theorem le_roundInt_iff {a : Rat} {n : Int} : n ≤ roundInt a ↔ (n : Rat) - 1/2 ≤ a := by
  unfold roundInt
  rw [Rat.le_floor_iff]
  constructor <;> intro h <;> grind

theorem roundInt_nonneg {a : Rat} (h : 0 ≤ a) : 0 ≤ roundInt a :=
  le_roundInt_iff.mpr (by simp; grind)

/-! ### `Math.round(x * s) / s` -/

/-- The rational value of `roundToScale` on a finite input. -/
def rts (x s : Rat) : Rat := (roundInt (x * s) : Rat) / s

theorem roundToScale_fin (x : Rat) {s : Rat} (hs : s ≠ 0) : roundToScale (.fin x) s = .fin (rts x s) := by
  simp only [roundToScale, JsNum.mul, JsNum.mathRound, JsNum.div, rts]
  split <;> simp_all

theorem rts_mono {x y s : Rat} (hs : 0 < s) (h : x ≤ y) : rts x s ≤ rts y s := by
  unfold rts
  apply div_le_div_of_le hs
  have := roundInt_mono (Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hs))
  exact_mod_cast this

theorem rts_nonneg {x s : Rat} (hs : 0 < s) (h : 0 ≤ x) : 0 ≤ rts x s := by
  unfold rts
  apply div_nonneg' hs
  have := roundInt_nonneg (Rat.mul_nonneg h (Rat.le_of_lt hs))
  exact_mod_cast this

/-- Rounding to a multiple of `1/s` moves a value by at most `1/(2s)`
    (stated without division: `rts x s · s ≤ x · s + 1/2`). -/
theorem rts_mul_le {x s : Rat} (hs : 0 < s) : rts x s * s ≤ x * s + 1/2 := by
  unfold rts
  rw [Rat.div_mul_cancel (by grind)]
  exact roundInt_le _

theorem lt_rts_mul {x s : Rat} (hs : 0 < s) : x * s - 1/2 < rts x s * s := by
  unfold rts
  rw [Rat.div_mul_cancel (by grind)]
  exact lt_roundInt _

/-- Rounding is idempotent: rounding a value already on the grid gives it back. -/
theorem rts_rts {x s : Rat} (hs : 0 < s) : rts (rts x s) s = rts x s := by
  unfold rts
  rw [Rat.div_mul_cancel (by grind), roundInt_intCast]

/-- If `x · s < n + 1/2` then rounding to the `1/s` grid stays at or below `n/s`. -/
theorem rts_le_of_lt {x s : Rat} {n : Int} (hs : 0 < s) (h : x * s < n + 1/2) : rts x s ≤ (n : Rat) / s := by
  unfold rts
  apply div_le_div_of_le hs
  have : roundInt (x * s) ≤ n := roundInt_le_iff.mpr (by grind)
  exact_mod_cast this

/-- If `n/s ≤ x` then rounding to the `1/s` grid stays at or above `n/s`. -/
theorem le_rts_of_le {x s : Rat} {n : Int} (hs : 0 < s) (h : (n : Rat) ≤ x * s) : (n : Rat) / s ≤ rts x s := by
  unfold rts
  apply div_le_div_of_le hs
  have : n ≤ roundInt (x * s) := le_roundInt_iff.mpr (by grind)
  exact_mod_cast this

/-! ### `round_basal` -/

/-- The value of `round_basal` on a finite input (round-basal.js lines 27-38). -/
def rbR (x : Rat) (m : Option String) : Rat :=
  if x < 1 then rts x (lowestRateScale m) else if x < 10 then rts x 20 else rts x 10

theorem lowestRateScale_cases (m : Option String) : lowestRateScale m = 20 ∨ lowestRateScale m = 40 := by
  unfold lowestRateScale; split
  · split <;> simp
  · simp

theorem lowestRateScale_pos (m : Option String) : 0 < lowestRateScale m := by
  rcases lowestRateScale_cases m with h | h <;> rw [h] <;> decide

theorem roundBasal_fin (x : Rat) (m : Option String) : roundBasal (.fin x) m = .fin (rbR x m) := by
  have hl := lowestRateScale_pos m
  unfold roundBasal rbR
  by_cases h1 : x < 1
  · simp [JsNum.lt, h1, roundToScale_fin x (Rat.ne_of_gt hl)]
  · by_cases h2 : x < 10
    · simp [JsNum.lt, h1, h2, roundToScale_fin x (by decide : (20 : Rat) ≠ 0)]
    · simp [JsNum.lt, h1, h2, roundToScale_fin x (by decide : (10 : Rat) ≠ 0)]

theorem roundBasal_nan (m : Option String) : roundBasal .nan m = .nan := by
  simp [roundBasal, roundToScale, JsNum.lt, JsNum.mul, JsNum.mathRound, JsNum.div]

/-- Below 1 U/h, `round_basal` stays at or below 1. -/
private theorem low_le_one {x : Rat} (m : Option String) (h : x < 1) : rts x (lowestRateScale m) ≤ 1 := by
  rcases lowestRateScale_cases m with hm | hm <;> rw [hm]
  · have := rts_le_of_lt (x := x) (s := 20) (n := 20) (by decide) (by grind)
    have e : ((20 : Int) : Rat) / 20 = 1 := by decide +kernel
    rw [e] at this; exact this
  · have := rts_le_of_lt (x := x) (s := 40) (n := 40) (by decide) (by grind)
    have e : ((40 : Int) : Rat) / 40 = 1 := by decide +kernel
    rw [e] at this; exact this

private theorem mid_ge_one {x : Rat} (h : 1 ≤ x) : 1 ≤ rts x 20 := by
  have := le_rts_of_le (x := x) (s := 20) (n := 20) (by decide) (by grind)
  have e : ((20 : Int) : Rat) / 20 = 1 := by decide +kernel
  rw [e] at this; exact this

private theorem mid_le_ten {x : Rat} (h : x < 10) : rts x 20 ≤ 10 := by
  have := rts_le_of_lt (x := x) (s := 20) (n := 200) (by decide) (by grind)
  have e : ((200 : Int) : Rat) / 20 = 10 := by decide +kernel
  rw [e] at this; exact this

private theorem high_ge_ten {x : Rat} (h : 10 ≤ x) : 10 ≤ rts x 10 := by
  have := le_rts_of_le (x := x) (s := 10) (n := 100) (by decide) (by grind)
  have e : ((100 : Int) : Rat) / 10 = 10 := by decide +kernel
  rw [e] at this; exact this

/-- **round_basal is monotone.** -/
theorem rbR_mono {x y : Rat} (m : Option String) (h : x ≤ y) : rbR x m ≤ rbR y m := by
  have hl := lowestRateScale_pos m
  unfold rbR
  by_cases hx1 : x < 1
  · by_cases hy1 : y < 1
    · simp only [hx1, hy1, ite_true]; exact rts_mono hl h
    · have := low_le_one m hx1
      by_cases hy10 : y < 10
      · simp only [hx1, hy1, hy10, ite_true, ite_false]; have := mid_ge_one (x := y) (by grind); grind
      · simp only [hx1, hy1, hy10, ite_true, ite_false]; have := high_ge_ten (x := y) (by grind); grind
  · by_cases hx10 : x < 10
    · have hy1 : ¬ y < 1 := by grind
      by_cases hy10 : y < 10
      · simp only [hx1, hy1, hx10, hy10, ite_true, ite_false]; exact rts_mono (by decide) h
      · simp only [hx1, hy1, hx10, hy10, ite_true, ite_false]
        have := mid_le_ten hx10; have := high_ge_ten (x := y) (by grind); grind
    · have hy1 : ¬ y < 1 := by grind
      have hy10 : ¬ y < 10 := by grind
      simp only [hx1, hy1, hx10, hy10, ite_false]; exact rts_mono (by decide) h

theorem rbR_nonneg {x : Rat} (m : Option String) (h : 0 ≤ x) : 0 ≤ rbR x m := by
  have hl := lowestRateScale_pos m
  unfold rbR
  split
  · exact rts_nonneg hl h
  · split
    · exact rts_nonneg (by decide) h
    · exact rts_nonneg (by decide) h

theorem rbR_zero (m : Option String) : rbR 0 m = 0 := by
  have := rbR_nonneg m (Rat.le_refl (a := 0))
  have h2 : rbR 0 m ≤ 0 := by
    have hl := lowestRateScale_pos m
    unfold rbR
    simp only [show (0 : Rat) < 1 by decide, ite_true]
    unfold rts
    rw [div_le_iff_le_mul hl]
    simp [roundInt]
    decide +kernel
  grind

/-- **round_basal is idempotent** on non-negative rates. -/
theorem rbR_idem {x : Rat} (m : Option String) (h : 0 ≤ x) : rbR (rbR x m) m = rbR x m := by
  have hl := lowestRateScale_pos m
  have one : rts 1 20 = 1 := by unfold rts; decide +kernel
  have ten : rts 10 10 = 10 := by unfold rts; decide +kernel
  by_cases hx1 : x < 1
  · have hle := low_le_one m hx1
    have e : rbR x m = rts x (lowestRateScale m) := by simp [rbR, hx1]
    rw [e]
    by_cases hy : rts x (lowestRateScale m) < 1
    · simp [rbR, hy, rts_rts hl]
    · have : rts x (lowestRateScale m) = 1 := by grind
      rw [this]; simp [rbR, one, show ¬ (1 : Rat) < 1 by decide, show (1 : Rat) < 10 by decide]
  · by_cases hx10 : x < 10
    · have e : rbR x m = rts x 20 := by simp [rbR, hx1, hx10]
      rw [e]
      have h1 := mid_ge_one (x := x) (by grind)
      have h2 := mid_le_ten hx10
      by_cases hy : rts x 20 < 10
      · have hy1 : ¬ rts x 20 < 1 := by grind
        simp [rbR, hy, hy1, rts_rts (show (0 : Rat) < 20 by decide)]
      · have : rts x 20 = 10 := by grind
        rw [this]; simp [rbR, ten, show ¬ (10 : Rat) < 1 by decide, show ¬ (10 : Rat) < 10 by decide]
    · have e : rbR x m = rts x 10 := by simp [rbR, hx1, hx10]
      rw [e]
      have h1 := high_ge_ten (x := x) (by grind)
      have hy1 : ¬ rts x 10 < 1 := by grind
      have hy10 : ¬ rts x 10 < 10 := by grind
      simp [rbR, hy1, hy10, rts_rts (show (0 : Rat) < 10 by decide)]

/-- **round_basal moves a rate by at most half an increment**: at most 0.025 U/h
    below 10 U/h and at most 0.05 U/h above. -/
theorem rbR_le (x : Rat) (m : Option String) :
    rbR x m ≤ x + 1/40 ∨ (10 ≤ x ∧ rbR x m ≤ x + 1/20) := by
  unfold rbR
  by_cases hx1 : x < 1
  · left; simp only [hx1, ite_true]
    rcases lowestRateScale_cases m with hm | hm <;> rw [hm]
    · have := rts_mul_le (x := x) (s := 20) (by decide); grind
    · have := rts_mul_le (x := x) (s := 40) (by decide); grind
  · by_cases hx10 : x < 10
    · left; simp only [hx1, hx10, ite_true, ite_false]
      have := rts_mul_le (x := x) (s := 20) (by decide); grind
    · right; simp only [hx1, hx10, ite_false]
      have := rts_mul_le (x := x) (s := 10) (by decide); grind

private theorem div20 (n : Int) : (n : Rat) / 20 = ((2 * n : Int) : Rat) / 40 := by push_cast; grind
private theorem div10 (n : Int) : (n : Rat) / 10 = ((4 * n : Int) : Rat) / 40 := by push_cast; grind

/-- Every non-negative output of `round_basal` is a multiple of 0.025 U/h. -/
theorem rbR_grid {x : Rat} (m : Option String) (h : 0 ≤ x) : ∃ k : Int, 0 ≤ k ∧ rbR x m = (k : Rat) / 40 := by
  unfold rbR rts
  split
  · rcases lowestRateScale_cases m with hm | hm <;> rw [hm]
    · exact ⟨_, by have := roundInt_nonneg (a := x * 20) (Rat.mul_nonneg h (by decide)); omega, div20 _⟩
    · exact ⟨_, roundInt_nonneg (Rat.mul_nonneg h (by decide)), rfl⟩
  · split
    · exact ⟨_, by have := roundInt_nonneg (a := x * 20) (Rat.mul_nonneg h (by decide)); omega, div20 _⟩
    · exact ⟨_, by have := roundInt_nonneg (a := x * 10) (Rat.mul_nonneg h (by decide)); omega, div10 _⟩

end LeanAID.Proofs
