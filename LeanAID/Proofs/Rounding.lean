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

/-! ### `Math.round(x * s) / s`, in doubles -/

open Binary64 (rd rd_mono rd_nonneg rd_intCast rd_rd)

/-- The value of `roundToScale` on a finite input: `x * s` and the final division
    are rounded to doubles; `Math.round` itself is exact. -/
def rts (x s : Rat) : Rat := rd ((roundInt (rd (x * s)) : Rat) / s)

theorem roundToScale_fin (x : Rat) {s : Rat} (hs : s ≠ 0) : roundToScale (.fin x) s = .fin (rts x s) := by
  simp only [roundToScale, JsNum.mul, JsNum.mathRound, JsNum.div, rts]
  split <;> simp_all

theorem rts_mono {x y s : Rat} (hs : 0 < s) (h : x ≤ y) : rts x s ≤ rts y s := by
  unfold rts
  apply rd_mono
  apply div_le_div_of_le hs
  have := roundInt_mono (rd_mono (Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hs)))
  exact_mod_cast this

theorem rts_nonneg {x s : Rat} (hs : 0 < s) (h : 0 ≤ x) : 0 ≤ rts x s := by
  unfold rts
  apply rd_nonneg
  apply div_nonneg' hs
  have := roundInt_nonneg (rd_nonneg (Rat.mul_nonneg h (Rat.le_of_lt hs)))
  exact_mod_cast this

/-- If `rd(x · s) < n + 1/2` then rounding to the `1/s` grid gives at most `rd(n/s)`. -/
theorem rts_le_of_lt {x s : Rat} {n : Int} (hs : 0 < s) (h : rd (x * s) < n + 1/2) : rts x s ≤ rd ((n : Rat) / s) := by
  unfold rts
  apply rd_mono
  apply div_le_div_of_le hs
  have : roundInt (rd (x * s)) ≤ n := roundInt_le_iff.mpr (by grind)
  exact_mod_cast this

/-- If `n ≤ rd(x · s)` then rounding to the `1/s` grid gives at least `rd(n/s)`. -/
theorem le_rts_of_le {x s : Rat} {n : Int} (hs : 0 < s) (h : (n : Rat) ≤ rd (x * s)) : rd ((n : Rat) / s) ≤ rts x s := by
  unfold rts
  apply rd_mono
  apply div_le_div_of_le hs
  have : n ≤ roundInt (rd (x * s)) := le_roundInt_iff.mpr (by grind)
  exact_mod_cast this

/-- For a double-sized integer `n`, `x · s ≤ n` gives `rd(x · s) ≤ n`. -/
theorem rd_le_int {y : Rat} {n : Int} (hn : n.natAbs ≤ 2 ^ 53) (h : y ≤ n) : rd y ≤ n := by
  have := rd_mono h; rwa [rd_intCast hn] at this

theorem int_le_rd {y : Rat} {n : Int} (hn : n.natAbs ≤ 2 ^ 53) (h : (n : Rat) ≤ y) : (n : Rat) ≤ rd y := by
  have := rd_mono h; rwa [rd_intCast hn] at this

/-- `rts x s ≤ 1` style bounds: `x · s ≤ n` (an integer) gives `rts x s ≤ rd(n/s)`. -/
theorem rts_le_of_le {x s : Rat} {n : Int} (hs : 0 < s) (hn : n.natAbs ≤ 2 ^ 53) (h : x * s ≤ n) :
    rts x s ≤ rd ((n : Rat) / s) :=
  rts_le_of_lt hs (by have := rd_le_int hn h; grind)

theorem le_rts_of_le' {x s : Rat} {n : Int} (hs : 0 < s) (hn : n.natAbs ≤ 2 ^ 53) (h : (n : Rat) ≤ x * s) :
    rd ((n : Rat) / s) ≤ rts x s :=
  le_rts_of_le hs (int_le_rd hn h)

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

theorem rd_one : rd 1 = 1 := by have := rd_intCast (n := 1) (by decide); simpa using this
theorem rd_ten : rd 10 = 10 := by have := rd_intCast (n := 10) (by decide); simpa using this

/-- Below 1 U/h, `round_basal` stays at or below 1. -/
private theorem low_le_one {x : Rat} (m : Option String) (h : x < 1) : rts x (lowestRateScale m) ≤ 1 := by
  rcases lowestRateScale_cases m with hm | hm <;> rw [hm]
  · have := rts_le_of_le (x := x) (s := 20) (n := 20) (by decide) (by decide) (by grind)
    have e : ((20 : Int) : Rat) / 20 = 1 := by decide +kernel
    rw [e, rd_one] at this; exact this
  · have := rts_le_of_le (x := x) (s := 40) (n := 40) (by decide) (by decide) (by grind)
    have e : ((40 : Int) : Rat) / 40 = 1 := by decide +kernel
    rw [e, rd_one] at this; exact this

private theorem mid_ge_one {x : Rat} (h : 1 ≤ x) : 1 ≤ rts x 20 := by
  have := le_rts_of_le' (x := x) (s := 20) (n := 20) (by decide) (by decide) (by grind)
  have e : ((20 : Int) : Rat) / 20 = 1 := by decide +kernel
  rw [e, rd_one] at this; exact this

private theorem mid_le_ten {x : Rat} (h : x < 10) : rts x 20 ≤ 10 := by
  have := rts_le_of_le (x := x) (s := 20) (n := 200) (by decide) (by decide) (by grind)
  have e : ((200 : Int) : Rat) / 20 = 10 := by decide +kernel
  rw [e, rd_ten] at this; exact this

private theorem high_ge_ten {x : Rat} (h : 10 ≤ x) : 10 ≤ rts x 10 := by
  have := le_rts_of_le' (x := x) (s := 10) (n := 100) (by decide) (by decide) (by grind)
  have e : ((100 : Int) : Rat) / 10 = 10 := by decide +kernel
  rw [e, rd_ten] at this; exact this

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
  have hl := lowestRateScale_pos m
  unfold rbR
  simp only [show (0 : Rat) < 1 by decide, ite_true]
  unfold rts
  simp only [Rat.zero_mul, Binary64.rd_zero, roundInt]
  rw [show ((0 : Rat) + 1/2).floor = 0 by decide +kernel]
  simp only [Rat.intCast_zero]
  rw [show (0 : Rat) / lowestRateScale m = 0 by grind, Binary64.rd_zero]

/-! ### Error bounds in the form the proofs use -/

/-- The absolute error term of `rd` (half the smallest subnormal). -/
abbrev tiny : Rat := Binary64.pow2 (-1075)

theorem tiny_pos : 0 < tiny := Binary64.pow2_pos _
theorem tiny_le : tiny ≤ 1 / 2 ^ 100 := Binary64.pow2_le_of_le (show (-1075 : Int) ≤ -100 by omega) |>.trans
  (by decide +kernel)

/-- For `y ≥ 0`: `y - y/2^53 - tiny ≤ rd y ≤ y + y/2^53 + tiny`. -/
theorem rd_close {y : Rat} (h : 0 ≤ y) : y - y / 9007199254740992 - tiny ≤ rd y ∧ rd y ≤ y + y / 9007199254740992 + tiny := by
  obtain ⟨h1, h2⟩ := Binary64.rd_err y
  simp only [h, ite_true] at h1 h2
  have e : Binary64.pow2 (-53) = 1 / 9007199254740992 := by decide +kernel
  rw [e] at h1 h2
  constructor <;> grind

/-- The double nearest to a grid point `n/s` is left unchanged by rounding to the
    `1/s` grid, for `0 ≤ n ≤ 2^41` and `0 < s ≤ 1000`. -/
theorem rts_grid_fix {n : Int} {s : Rat} (hs : 0 < s) (hs1 : s ≤ 1000) (hn0 : 0 ≤ n) (hnB : (n : Rat) ≤ 2 ^ 41) :
    rts (rd ((n : Rat) / s)) s = rd ((n : Rat) / s) := by
  have ht := tiny_pos; have ht' := tiny_le
  have hnR : (0 : Rat) ≤ n := by exact_mod_cast hn0
  unfold rts
  have hq0 : 0 ≤ (n : Rat) / s := div_nonneg' hs hnR
  obtain ⟨y1, y2⟩ := rd_close hq0
  generalize hy : rd ((n : Rat) / s) = y at y1 y2
  have hy0 : 0 ≤ y := by rw [← hy]; exact rd_nonneg hq0
  have hqs : (n : Rat) / s * s = n := Rat.div_mul_cancel (by grind)
  have m1 := Rat.mul_le_mul_of_nonneg_right y1 (Rat.le_of_lt hs)
  have m2 := Rat.mul_le_mul_of_nonneg_right y2 (Rat.le_of_lt hs)
  have e1 : ((n : Rat) / s - (n : Rat) / s / 9007199254740992 - tiny) * s = n - n / 9007199254740992 - tiny * s := by
    have : s ≠ 0 := by grind
    grind
  have e2 : ((n : Rat) / s + (n : Rat) / s / 9007199254740992 + tiny) * s = n + n / 9007199254740992 + tiny * s := by
    have : s ≠ 0 := by grind
    grind
  rw [e1] at m1; rw [e2] at m2
  have hts : tiny * s ≤ tiny * 1000 := Rat.mul_le_mul_of_nonneg_left hs1 (Rat.le_of_lt ht)
  have hys0 : 0 ≤ y * s := Rat.mul_nonneg hy0 (Rat.le_of_lt hs)
  obtain ⟨z1, z2⟩ := rd_close hys0
  have hr : roundInt (rd (y * s)) = n := by
    apply Int.le_antisymm
    · exact roundInt_le_iff.mpr (by grind)
    · exact le_roundInt_iff.mpr (by grind)
  rw [hr]; exact hy

/-- Rounding to the `1/s` grid is idempotent, for `0 < s ≤ 1000` and `0 ≤ x ≤ 2^30`. -/
theorem rts_rts {x s : Rat} (hs : 0 < s) (hs1 : s ≤ 1000) (h0 : 0 ≤ x) (hx : x ≤ 2 ^ 30) :
    rts (rts x s) s = rts x s := by
  have ht := tiny_pos; have ht' := tiny_le
  have hxs0 : 0 ≤ x * s := Rat.mul_nonneg h0 (Rat.le_of_lt hs)
  have hxs : x * s ≤ 2 ^ 30 * 1000 := by
    have := Rat.mul_le_mul_of_nonneg_right hx (Rat.le_of_lt hs)
    have := Rat.mul_le_mul_of_nonneg_left hs1 (show (0 : Rat) ≤ 2 ^ 30 by decide)
    grind
  obtain ⟨-, r1⟩ := rd_close hxs0
  have hn0 := roundInt_nonneg (rd_nonneg hxs0)
  have hn1 := roundInt_le (rd (x * s))
  have e : rts x s = rd ((roundInt (rd (x * s)) : Rat) / s) := rfl
  rw [e]
  exact rts_grid_fix hs hs1 hn0 (by grind)

/-- **round_basal is idempotent** on rates between 0 and 2^30 U/h. -/
theorem rbR_idem {x : Rat} (m : Option String) (h : 0 ≤ x) (hx : x ≤ 2 ^ 30) : rbR (rbR x m) m = rbR x m := by
  have hl := lowestRateScale_pos m
  have hl1 : lowestRateScale m ≤ 1000 := by
    rcases lowestRateScale_cases m with h | h <;> rw [h] <;> decide
  have one : rts 1 20 = 1 := by unfold rts; decide +kernel
  have ten : rts 10 10 = 10 := by unfold rts; decide +kernel
  by_cases hx1 : x < 1
  · have hle := low_le_one m hx1
    have e : rbR x m = rts x (lowestRateScale m) := by simp [rbR, hx1]
    rw [e]
    by_cases hy : rts x (lowestRateScale m) < 1
    · simp [rbR, hy, rts_rts hl hl1 h hx]
    · have : rts x (lowestRateScale m) = 1 := by grind
      rw [this]; simp [rbR, one, show ¬ (1 : Rat) < 1 by decide, show (1 : Rat) < 10 by decide]
  · by_cases hx10 : x < 10
    · have e : rbR x m = rts x 20 := by simp [rbR, hx1, hx10]
      rw [e]
      have h1 := mid_ge_one (x := x) (by grind)
      have h2 := mid_le_ten hx10
      by_cases hy : rts x 20 < 10
      · have hy1 : ¬ rts x 20 < 1 := by grind
        simp [rbR, hy, hy1, rts_rts (show (0 : Rat) < 20 by decide) (by decide) h hx]
      · have : rts x 20 = 10 := by grind
        rw [this]; simp [rbR, ten, show ¬ (10 : Rat) < 1 by decide, show ¬ (10 : Rat) < 10 by decide]
    · have e : rbR x m = rts x 10 := by simp [rbR, hx1, hx10]
      rw [e]
      have h1 := high_ge_ten (x := x) (by grind)
      have hy1 : ¬ rts x 10 < 1 := by grind
      have hy10 : ¬ rts x 10 < 10 := by grind
      simp [rbR, hy1, hy10, rts_rts (show (0 : Rat) < 10 by decide) (by decide) h hx]

/-- Rounding to the `1/s` grid moves a value up by at most `1/(2s)`, plus the
    double rounding of `x·s` and of the quotient. -/
theorem rts_le_add {x s : Rat} (hs : 0 < s) (h0 : 0 ≤ x) :
    rts x s * s ≤ (x * s + x * s / 9007199254740992 + tiny + 1/2) * (1 + 1 / 9007199254740992) + tiny * s := by
  have ht := tiny_pos
  have hxs0 : 0 ≤ x * s := Rat.mul_nonneg h0 (Rat.le_of_lt hs)
  obtain ⟨-, r1⟩ := rd_close hxs0
  have hn1 := roundInt_le (rd (x * s))
  have hn0 := roundInt_nonneg (rd_nonneg hxs0)
  unfold rts
  generalize roundInt (rd (x * s)) = n at hn0 hn1 ⊢
  have hnR : (0 : Rat) ≤ n := by exact_mod_cast hn0
  have hq0 : 0 ≤ (n : Rat) / s := div_nonneg' hs hnR
  obtain ⟨-, y2⟩ := rd_close hq0
  have m2 := Rat.mul_le_mul_of_nonneg_right y2 (Rat.le_of_lt hs)
  have hqs : (n : Rat) / s * s = n := Rat.div_mul_cancel (by grind)
  have e2 : ((n : Rat) / s + (n : Rat) / s / 9007199254740992 + tiny) * s = n + n / 9007199254740992 + tiny * s := by
    have : s ≠ 0 := by grind
    grind
  rw [e2] at m2
  grind

theorem rts_ge_sub {x s : Rat} (hs : 0 < s) (h0 : 0 ≤ x) :
    (x * s - x * s / 9007199254740992 - tiny - 1/2) * (1 - 1 / 9007199254740992) - tiny * s ≤ rts x s * s := by
  have ht := tiny_pos
  have hxs0 : 0 ≤ x * s := Rat.mul_nonneg h0 (Rat.le_of_lt hs)
  obtain ⟨r0, -⟩ := rd_close hxs0
  have hn1 := lt_roundInt (rd (x * s))
  have hn0 := roundInt_nonneg (rd_nonneg hxs0)
  unfold rts
  generalize roundInt (rd (x * s)) = n at hn0 hn1 ⊢
  have hnR : (0 : Rat) ≤ n := by exact_mod_cast hn0
  have hq0 : 0 ≤ (n : Rat) / s := div_nonneg' hs hnR
  obtain ⟨y1, -⟩ := rd_close hq0
  have m1 := Rat.mul_le_mul_of_nonneg_right y1 (Rat.le_of_lt hs)
  have hqs : (n : Rat) / s * s = n := Rat.div_mul_cancel (by grind)
  have e1 : ((n : Rat) / s - (n : Rat) / s / 9007199254740992 - tiny) * s = n - n / 9007199254740992 - tiny * s := by
    have : s ≠ 0 := by grind
    grind
  rw [e1] at m1
  grind

/-- **round_basal moves a rate up by at most half an increment** (0.025 U/h below
    10 U/h, 0.05 U/h above), plus double rounding of relative size below 2^-50. -/
theorem rbR_le {x : Rat} (m : Option String) (h0 : 0 ≤ x) :
    rbR x m ≤ x + 1/40 + (x + 1) / 2 ^ 50 ∨ (10 ≤ x ∧ rbR x m ≤ x + 1/20 + (x + 1) / 2 ^ 50) := by
  have ht := tiny_pos; have ht' := tiny_le
  unfold rbR
  by_cases hx1 : x < 1
  · left; simp only [hx1, ite_true]
    rcases lowestRateScale_cases m with hm | hm <;> rw [hm]
    · have := rts_le_add (x := x) (s := 20) (by decide) h0; grind
    · have := rts_le_add (x := x) (s := 40) (by decide) h0; grind
  · by_cases hx10 : x < 10
    · left; simp only [hx1, hx10, ite_true, ite_false]
      have := rts_le_add (x := x) (s := 20) (by decide) h0; grind
    · right; simp only [hx1, hx10, ite_false]
      have := rts_le_add (x := x) (s := 10) (by decide) h0; grind

/-- Every non-negative output of `round_basal` is the double nearest to `n/s` for an
    integer `0 ≤ n` and a scale `s ∈ {10, 20, 40}`. -/
theorem rbR_form {x : Rat} (m : Option String) (h : 0 ≤ x) :
    ∃ n : Int, ∃ s : Rat, 0 ≤ n ∧ (s = 10 ∨ s = 20 ∨ s = 40) ∧ rbR x m = rd ((n : Rat) / s) := by
  unfold rbR rts
  have hn : ∀ s : Rat, 0 < s → 0 ≤ roundInt (rd (x * s)) := fun s hs =>
    roundInt_nonneg (rd_nonneg (Rat.mul_nonneg h (Rat.le_of_lt hs)))
  split
  · rcases lowestRateScale_cases m with hm | hm <;> rw [hm]
    · exact ⟨_, 20, hn 20 (by decide), by simp, rfl⟩
    · exact ⟨_, 40, hn 40 (by decide), by simp, rfl⟩
  · split
    · exact ⟨_, 20, hn 20 (by decide), by simp, rfl⟩
    · exact ⟨_, 10, hn 10 (by decide), by simp, rfl⟩

end LeanAID.Proofs
