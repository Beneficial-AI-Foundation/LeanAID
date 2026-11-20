/-
  LeanAID.Proofs.Binary64 — properties of IEEE-754 round-to-nearest (`Binary64.rd`):
  monotone, sign-preserving, exact on doubles (in particular on integers below 2^53),
  with a relative error bound. These are what the safety proofs use about double
  arithmetic.
-/
import LeanAID.Core.Binary64

namespace LeanAID.Binary64

/-! ### Powers of two -/

theorem two_pow_pos (n : Nat) : (0 : Rat) < (2 : Rat) ^ n := Rat.pow_pos (by decide)

theorem one_le_two_pow (n : Nat) : (1 : Rat) ≤ (2 : Rat) ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Rat.pow_succ]; grind

theorem pow2_pos (e : Int) : 0 < pow2 e := by
  unfold pow2; split
  · exact two_pow_pos _
  · have := two_pow_pos (-e).toNat
    have : (2 : Rat) ^ (-e).toNat ≠ 0 := by grind
    rw [Rat.lt_div_iff (two_pow_pos _)]; grind

theorem pow2_ofNat (n : Nat) : pow2 (n : Int) = (2 : Rat) ^ n := by
  simp [pow2]

theorem pow2_succ (e : Int) : pow2 (e + 1) = pow2 e * 2 := by
  unfold pow2
  by_cases h : 0 ≤ e
  · have h1 : 0 ≤ e + 1 := by omega
    simp only [h, h1, ite_true]
    rw [show (e + 1).toNat = e.toNat + 1 by omega, Rat.pow_succ]
  · by_cases h1 : 0 ≤ e + 1
    · have he : e = -1 := by omega
      subst he; decide +kernel
    · simp only [h, h1, ite_false]
      rw [show (-e).toNat = (-(e + 1)).toNat + 1 by omega, Rat.pow_succ]
      have hp := two_pow_pos (-(e + 1)).toNat
      have : (2 : Rat) ^ (-(e + 1)).toNat ≠ 0 := by grind
      grind

theorem pow2_add_nat (e : Int) (n : Nat) : pow2 (e + n) = pow2 e * (2 : Rat) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show e + ((n + 1 : Nat) : Int) = (e + n) + 1 by omega, pow2_succ, ih, Rat.pow_succ]
    grind

theorem pow2_le_of_le {a b : Int} (h : a ≤ b) : pow2 a ≤ pow2 b := by
  have e : b = a + ((b - a).toNat : Int) := by omega
  rw [e, pow2_add_nat]
  have := pow2_pos a
  have := Rat.mul_le_mul_of_nonneg_left (one_le_two_pow (b - a).toNat) (Rat.le_of_lt this)
  grind

theorem pow2_lt_of_lt {a b : Int} (h : a < b) : pow2 a < pow2 b := by
  have := pow2_le_of_le (show a + 1 ≤ b by omega)
  rw [pow2_succ] at this
  have := pow2_pos a
  grind

/-- `pow2 b` is an integer multiple of `pow2 a` when `a ≤ b`. -/
theorem pow2_dvd {a b : Int} (h : a ≤ b) : pow2 b = (((2 : Int) ^ (b - a).toNat : Int) : Rat) * pow2 a := by
  have e : b = a + ((b - a).toNat : Int) := by omega
  conv => lhs; rw [e]
  rw [pow2_add_nat]; push_cast; grind

/-! ### `flog2` is `⌊log₂ a⌋` -/

private theorem num_pos {a : Rat} (ha : 0 < a) : 0 < a.num := by
  have h1 := Rat.num_nonneg.mpr (Rat.le_of_lt ha)
  have h2 : a.num ≠ 0 := fun h => by rw [Rat.num_eq_zero] at h; subst h; exact Rat.lt_irrefl ha
  omega

private theorem a_eq {a : Rat} : a = (a.num : Rat) / ((a.den : Int) : Rat) := by
  conv => lhs; rw [← Rat.num_divInt_den a]
  rw [Rat.divInt_eq_div]

private theorem mul_den (a : Rat) : a * (a.den : Rat) = (a.num : Rat) := by
  have hd : ((a.den : Int) : Rat) ≠ 0 := by
    have := Rat.den_pos a
    have : (0 : Rat) < ((a.den : Int) : Rat) := by exact_mod_cast this
    grind
  have e := a_eq (a := a)
  have : ((a.den : Int) : Rat) = (a.den : Rat) := rfl
  rw [← this]
  generalize ((a.den : Int) : Rat) = d at e hd ⊢
  generalize (a.num : Rat) = n at e ⊢
  subst e; grind

private theorem num_cast {a : Rat} (ha : 0 < a) : (a.num : Rat) = ((a.num.natAbs : Nat) : Rat) := by
  have := num_pos ha
  have : (a.num.natAbs : Int) = a.num := by omega
  rw [← this]; rfl

theorem flog2_spec {a : Rat} (ha : 0 < a) : pow2 (flog2 a) ≤ a ∧ a < pow2 (flog2 a + 1) := by
  have hn0 : a.num.natAbs ≠ 0 := by have := num_pos ha; omega
  have hd0 : a.den ≠ 0 := by have := Rat.den_pos a; omega
  let p := a.num.natAbs.log2
  let q := a.den.log2
  have hp1 : ((2 : Rat) ^ p) ≤ (a.num.natAbs : Rat) := by
    have := Nat.log2_self_le hn0; exact_mod_cast this
  have hp2 : (a.num.natAbs : Rat) < (2 : Rat) ^ (p + 1) := by
    have := Nat.lt_log2_self (n := a.num.natAbs); exact_mod_cast this
  have hq1 : ((2 : Rat) ^ q) ≤ (a.den : Rat) := by
    have := Nat.log2_self_le hd0; exact_mod_cast this
  have hq2 : (a.den : Rat) < (2 : Rat) ^ (q + 1) := by
    have := Nat.lt_log2_self (n := a.den); exact_mod_cast this
  have hden : (0 : Rat) < a.den := by have := Rat.den_pos a; exact_mod_cast this
  -- a · den = num
  have hmul : a * (a.den : Rat) = (a.num.natAbs : Rat) := by
    rw [← num_cast ha]; exact mul_den a
  -- pow2 (p - q) · 2^q = 2^p
  have hk : pow2 ((p : Int) - q) * (2 : Rat) ^ q = (2 : Rat) ^ p := by
    rw [← pow2_add_nat, show (p : Int) - q + q = p by omega, pow2_ofNat]
  have hk1 : pow2 ((p : Int) - q + 1) * (2 : Rat) ^ q = (2 : Rat) ^ (p + 1) := by
    rw [pow2_succ, Rat.pow_succ, ← hk]; grind
  have hkm : pow2 ((p : Int) - q - 1) * (2 : Rat) ^ (q + 1) = (2 : Rat) ^ p := by
    rw [Rat.pow_succ, ← hk, show (p : Int) - q = ((p : Int) - q - 1) + 1 by omega, pow2_succ]; grind
  have hpos := pow2_pos ((p : Int) - q)
  have hpos1 := pow2_pos ((p : Int) - q + 1)
  have hposm := pow2_pos ((p : Int) - q - 1)
  -- upper: a < pow2 (p - q + 1)
  have up : a < pow2 ((p : Int) - q + 1) := by
    have h1 : pow2 ((p : Int) - q + 1) * (2 : Rat) ^ q ≤ pow2 ((p : Int) - q + 1) * a.den :=
      Rat.mul_le_mul_of_nonneg_left hq1 (Rat.le_of_lt hpos1)
    have h2 : a * a.den < pow2 ((p : Int) - q + 1) * a.den := by grind
    exact Rat.lt_of_mul_lt_mul_right h2 (Rat.le_of_lt hden)
  -- lower: pow2 (p - q - 1) < a
  have low : pow2 ((p : Int) - q - 1) < a := by
    have h1 : pow2 ((p : Int) - q - 1) * a.den < pow2 ((p : Int) - q - 1) * (2 : Rat) ^ (q + 1) :=
      Rat.mul_lt_mul_of_pos_left hq2 hposm
    have h2 : pow2 ((p : Int) - q - 1) * a.den < a * a.den := by grind
    exact Rat.lt_of_mul_lt_mul_right h2 (Rat.le_of_lt hden)
  unfold flog2
  simp only
  split
  · exact ⟨by assumption, up⟩
  · rename_i h
    refine ⟨Rat.le_of_lt low, ?_⟩
    rw [show (p : Int) - q - 1 + 1 = (p : Int) - q by omega]
    exact Rat.not_le.mp h

theorem flog2_mono {a b : Rat} (ha : 0 < a) (h : a ≤ b) : flog2 a ≤ flog2 b := by
  obtain ⟨a1, -⟩ := flog2_spec ha
  obtain ⟨-, b2⟩ := flog2_spec ((by grind : 0 < b))
  by_cases hc : flog2 a ≤ flog2 b
  · exact hc
  · have := pow2_le_of_le (show flog2 b + 1 ≤ flog2 a by omega)
    grind

theorem ulpExp_mono {a b : Rat} (ha : 0 < a) (h : a ≤ b) : ulpExp a ≤ ulpExp b := by
  have := flog2_mono ha h; unfold ulpExp; omega

/-! ### Round half to even -/

theorem rhe_cases (m : Rat) : (rhe m = m.floor ∨ rhe m = m.floor + 1) ∧
    (m - m.floor < 1/2 → rhe m = m.floor) ∧ (1/2 < m - m.floor → rhe m = m.floor + 1) := by
  unfold rhe; simp only
  refine ⟨?_, ?_, ?_⟩
  · split
    · left; rfl
    · split
      · right; rfl
      · split
        · left; rfl
        · right; rfl
  · intro h; simp [h]
  · intro h
    have : ¬ (m - m.floor < 1/2) := by grind
    simp [this, h]

theorem rhe_le (m : Rat) : (rhe m : Rat) ≤ m + 1/2 := by
  obtain ⟨h1, h2, h3⟩ := rhe_cases m
  have := Rat.floor_le m
  have := Rat.lt_floor_add_one m
  rcases h1 with h | h <;> rw [h]
  · push_cast; grind
  · push_cast
    by_cases hr : m - m.floor < 1/2
    · have := h2 hr; omega
    · grind

theorem le_rhe (m : Rat) : m - 1/2 ≤ (rhe m : Rat) := by
  obtain ⟨h1, h2, h3⟩ := rhe_cases m
  have := Rat.floor_le m
  have := Rat.lt_floor_add_one m
  rcases h1 with h | h <;> rw [h]
  · by_cases hr : 1/2 < m - m.floor
    · have := h3 hr; omega
    · grind
  · push_cast; grind

theorem rhe_intCast (n : Int) : rhe (n : Rat) = n := by
  unfold rhe; simp [Rat.floor_intCast, Rat.sub_self, show (0 : Rat) < 1/2 from by decide +kernel]

theorem rhe_mono {a b : Rat} (h : a ≤ b) : rhe a ≤ rhe b := by
  obtain ⟨a1, a2, a3⟩ := rhe_cases a
  obtain ⟨b1, b2, b3⟩ := rhe_cases b
  have hf : a.floor ≤ b.floor := Rat.floor_monotone h
  by_cases hlt : a.floor < b.floor
  · omega
  · have heq : a.floor = b.floor := by omega
    -- same integer part: compare fractional parts
    by_cases ha : a - a.floor < 1/2
    · have := a2 ha; omega
    · by_cases ha' : 1/2 < a - a.floor
      · have hb' : 1/2 < b - b.floor := by rw [← heq]; grind
        have := a3 ha'; have := b3 hb'; omega
      · -- a is at a tie
        by_cases hb : 1/2 < b - b.floor
        · have := b3 hb; omega
        · have hbeq : b = a := by
            have : (a.floor : Rat) = (b.floor : Rat) := by rw [heq]
            grind
          subst hbeq; omega

theorem rhe_nonneg {m : Rat} (h : 0 ≤ m) : 0 ≤ rhe m := by
  have := rhe_mono h; rw [show (0 : Rat) = ((0 : Int) : Rat) by rfl, rhe_intCast] at this; exact this

/-- If `m ≤ n` for an integer `n`, then `rhe m ≤ n`. -/
theorem rhe_le_of_le {m : Rat} {n : Int} (h : m ≤ n) : rhe m ≤ n := by
  have := rhe_mono h; rwa [rhe_intCast] at this

theorem le_rhe_of_le {m : Rat} {n : Int} (h : (n : Rat) ≤ m) : n ≤ rhe m := by
  have := rhe_mono h; rwa [rhe_intCast] at this

/-! ### `rdPos` -/

private theorem div_mul_pow2 (a : Rat) (e : Int) : a / pow2 e * pow2 e = a := by
  have := pow2_pos e; have : pow2 e ≠ 0 := by grind
  grind

private theorem div_le_div_pos {a b c : Rat} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  have h1 : a / c * c = a := by grind
  have h2 : b / c * c = b := by grind
  by_cases hh : a / c ≤ b / c
  · exact hh
  · have := Rat.mul_lt_mul_of_pos_right (Rat.not_le.mp hh) hc; grind

/-- Rounding at a fixed exponent `E` is monotone. -/
private theorem rndAt_mono {a b : Rat} (E : Int) (h : a ≤ b) :
    (rhe (a / pow2 E) : Rat) * pow2 E ≤ (rhe (b / pow2 E) : Rat) * pow2 E := by
  have hp := pow2_pos E
  have := rhe_mono (div_le_div_pos hp h)
  have : (rhe (a / pow2 E) : Rat) ≤ rhe (b / pow2 E) := by exact_mod_cast this
  exact Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hp)

/-- Rounding at exponent `E` does not cross a point `N · 2^E` of the grid. -/
private theorem rndAt_le {a : Rat} (E : Int) (N : Int) (h : a ≤ N * pow2 E) :
    (rhe (a / pow2 E) : Rat) * pow2 E ≤ N * pow2 E := by
  have hm := rndAt_mono E h
  have hp := pow2_pos E; have : pow2 E ≠ 0 := by grind
  rwa [show (N : Rat) * pow2 E / pow2 E = (N : Rat) by grind, rhe_intCast] at hm

private theorem le_rndAt {a : Rat} (E : Int) (N : Int) (h : N * pow2 E ≤ a) :
    (N : Rat) * pow2 E ≤ (rhe (a / pow2 E) : Rat) * pow2 E := by
  have hm := rndAt_mono E h
  have hp := pow2_pos E; have : pow2 E ≠ 0 := by grind
  rwa [show (N : Rat) * pow2 E / pow2 E = (N : Rat) by grind, rhe_intCast] at hm

theorem rdPos_mono {a b : Rat} (ha : 0 < a) (h : a ≤ b) : rdPos a ≤ rdPos b := by
  have hb : 0 < b := (by grind : 0 < b)
  have hE := ulpExp_mono ha h
  unfold rdPos
  by_cases hEq : ulpExp a = ulpExp b
  · rw [hEq]; exact rndAt_mono _ h
  · -- the exponent grows: a < 2^⌊log₂ b⌋ ≤ b, and 2^⌊log₂ b⌋ is on both grids
    have hlt : ulpExp a < ulpExp b := by omega
    have hEb : ulpExp b = flog2 b - 52 := by unfold ulpExp at hlt ⊢; omega
    have hfa : flog2 a + 1 ≤ flog2 b := by unfold ulpExp at hlt; omega
    obtain ⟨-, a2⟩ := flog2_spec ha
    obtain ⟨b1, -⟩ := flog2_spec hb
    have hT : a ≤ pow2 (flog2 b) := by have := pow2_le_of_le hfa; grind
    have hEa : ulpExp a ≤ flog2 b := by omega
    have g1 := pow2_dvd hEa
    have g2 := pow2_dvd (show ulpExp b ≤ flog2 b by omega)
    have l := rndAt_le (ulpExp a) _ (g1 ▸ hT)
    have r := le_rndAt (ulpExp b) _ (g2 ▸ b1)
    rw [← g1] at l; rw [← g2] at r
    exact Rat.le_trans l r

theorem rdPos_nonneg {a : Rat} (ha : 0 < a) : 0 ≤ rdPos a := by
  unfold rdPos
  have hp := pow2_pos (ulpExp a)
  have := le_rndAt (ulpExp a) 0 (a := a) (by simp; grind)
  simpa using this

/-- `|rdPos a - a| ≤ 2^(ulpExp a - 1)`. -/
theorem rdPos_err {a : Rat} : rdPos a ≤ a + pow2 (ulpExp a - 1) ∧ a - pow2 (ulpExp a - 1) ≤ rdPos a := by
  unfold rdPos
  have hp := pow2_pos (ulpExp a)
  have e2 : pow2 (ulpExp a) = pow2 (ulpExp a - 1) * 2 := by
    rw [← pow2_succ]; congr 1; omega
  have h1 := rhe_le (a / pow2 (ulpExp a))
  have h2 := le_rhe (a / pow2 (ulpExp a))
  have m1 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)
  have m2 := Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt hp)
  have : pow2 (ulpExp a) ≠ 0 := by grind
  constructor <;> grind

/-- `2^(ulpExp a - 1) ≤ a · 2^-53 + 2^-1075` for `a > 0`. -/
theorem half_ulp_le {a : Rat} (ha : 0 < a) : pow2 (ulpExp a - 1) ≤ a * pow2 (-53) + pow2 (-1075) := by
  obtain ⟨a1, -⟩ := flog2_spec ha
  have hp53 := pow2_pos (-53)
  have hp1075 := pow2_pos (-1075)
  unfold ulpExp
  by_cases h : flog2 a - 52 ≤ -1074
  · rw [show max (flog2 a - 52) (-1074) - 1 = -1075 by omega]
    have := Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hp53); grind
  · rw [show max (flog2 a - 52) (-1074) - 1 = flog2 a - 53 by omega]
    have e : pow2 (flog2 a) = pow2 (flog2 a - 53) * (2 : Rat) ^ 53 := by
      rw [← pow2_add_nat]; congr 1; omega
    have e2 : pow2 (-53) * (2 : Rat) ^ 53 = 1 := by decide +kernel
    have := Rat.mul_le_mul_of_nonneg_right a1 (Rat.le_of_lt hp53)
    -- pow2 (flog2 a - 53) = pow2 (flog2 a) * pow2 (-53)
    have e3 : pow2 (flog2 a - 53) = pow2 (flog2 a) * pow2 (-53) := by
      rw [e, Rat.mul_assoc, Rat.mul_comm ((2 : Rat) ^ 53), e2, Rat.mul_one]
    grind

/-- A value on the grid of its own exponent is unchanged by rounding. -/
theorem rdPos_fix {a : Rat} (N : Int) (e : Int) (he : ulpExp a ≤ e) (h : a = N * pow2 e) : rdPos a = a := by
  unfold rdPos
  have g := pow2_dvd he
  rw [g] at h
  have hp := pow2_pos (ulpExp a); have : pow2 (ulpExp a) ≠ 0 := by grind
  have : a / pow2 (ulpExp a) = ((N * 2 ^ (e - ulpExp a).toNat : Int) : Rat) := by
    rw [h]; push_cast; grind
  rw [this, rhe_intCast]; push_cast; grind

/-! ### `rd` -/

@[simp] theorem rd_zero : rd 0 = 0 := by simp [rd]

theorem rd_pos_eq {x : Rat} (h : 0 < x) : rd x = rdPos x := by
  unfold rd; simp [Rat.ne_of_gt h, h]

theorem rd_neg_eq {x : Rat} (h : x < 0) : rd x = -(rdPos (-x)) := by
  unfold rd
  have : x ≠ 0 := Rat.ne_of_lt h
  have : ¬ 0 < x := by grind
  simp [*]

theorem rd_neg (x : Rat) : rd (-x) = -(rd x) := by
  by_cases h0 : x = 0
  · subst h0; simp
  · by_cases hp : 0 < x
    · rw [rd_neg_eq (by grind), rd_pos_eq hp, Rat.neg_neg]
    · rw [rd_pos_eq (by grind), rd_neg_eq (by grind), Rat.neg_neg]

theorem rd_nonneg {x : Rat} (h : 0 ≤ x) : 0 ≤ rd x := by
  by_cases h0 : x = 0
  · subst h0; simp
  · rw [rd_pos_eq (by grind)]; exact rdPos_nonneg (by grind)

theorem rd_nonpos {x : Rat} (h : x ≤ 0) : rd x ≤ 0 := by
  have := rd_nonneg (x := -x) (by grind); rw [rd_neg] at this; grind

/-- **Rounding to the nearest double is monotone.** -/
theorem rd_mono {x y : Rat} (h : x ≤ y) : rd x ≤ rd y := by
  by_cases hx : 0 < x
  · rw [rd_pos_eq hx, rd_pos_eq (by grind)]; exact rdPos_mono hx h
  · by_cases hy : y < 0
    · rw [rd_neg_eq (by grind), rd_neg_eq hy]
      have := rdPos_mono (a := -y) (b := -x) (by grind) (by grind)
      grind
    · exact Rat.le_trans (rd_nonpos (by grind)) (rd_nonneg (by grind))

/-- `rd` fixes every integer `n` with `|n| ≤ 2^53`. -/
theorem rd_intCast {n : Int} (h : n.natAbs ≤ 2 ^ 53) : rd (n : Rat) = n := by
  have key : ∀ m : Int, 0 < m → m.natAbs ≤ 2 ^ 53 → rdPos (m : Rat) = m := by
    intro m hm hle
    have hm' : (0 : Rat) < m := by exact_mod_cast hm
    have hf : flog2 (m : Rat) ≤ 53 := by
      obtain ⟨a1, -⟩ := flog2_spec hm'
      by_cases hc : flog2 (m : Rat) ≤ 53
      · exact hc
      · have := pow2_le_of_le (show (54 : Int) ≤ flog2 (m : Rat) by omega)
        have h54 : pow2 54 = ((2 ^ 54 : Int) : Rat) := by decide +kernel
        have : (m : Rat) ≤ ((2 ^ 53 : Int) : Rat) := by
          have : m ≤ 2 ^ 53 := by omega
          exact_mod_cast this
        have : ((2 ^ 53 : Int) : Rat) < ((2 ^ 54 : Int) : Rat) := by decide +kernel
        grind
    by_cases h53 : flog2 (m : Rat) = 53
    · -- m = 2^53 exactly: on the grid with exponent 1
      obtain ⟨a1, -⟩ := flog2_spec hm'
      rw [h53] at a1
      have h2 : pow2 53 = ((2 ^ 53 : Int) : Rat) := by decide +kernel
      have : m = 2 ^ 53 := by
        have : ((2 ^ 53 : Int) : Rat) ≤ (m : Rat) := by rw [← h2]; exact a1
        have : (2 ^ 53 : Int) ≤ m := by exact_mod_cast this
        omega
      subst this
      exact rdPos_fix (2 ^ 52) 1 (by unfold ulpExp; omega) (by decide +kernel)
    · exact rdPos_fix m 0 (by unfold ulpExp; omega) (by simp [pow2])
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases hp : 0 < n
    · rw [rd_pos_eq (by exact_mod_cast hp)]; exact key n hp h
    · have hn : (n : Rat) < 0 := by have : n < 0 := by omega
                                    exact_mod_cast this
      rw [rd_neg_eq hn]
      have := key (-n) (by omega) (by omega)
      push_cast at this; rw [this]; grind

theorem rd_natCast {n : Nat} (h : n ≤ 2 ^ 53) : rd (n : Rat) = n := by
  have := rd_intCast (n := (n : Int)) (by omega); exact_mod_cast this

/-- **Error bound.** `|rd x - x| ≤ |x| · 2^-53 + 2^-1075`. -/
theorem rd_err (x : Rat) :
    rd x ≤ x + (if 0 ≤ x then x else -x) * pow2 (-53) + pow2 (-1075) ∧
    x - (if 0 ≤ x then x else -x) * pow2 (-53) - pow2 (-1075) ≤ rd x := by
  by_cases h0 : x = 0
  · subst h0; simp; have := pow2_pos (-1075); grind
  · by_cases hp : 0 < x
    · rw [rd_pos_eq hp]
      obtain ⟨e1, e2⟩ := rdPos_err (a := x)
      have := half_ulp_le hp
      simp only [Rat.le_of_lt hp, ite_true]
      constructor <;> grind
    · have hn : 0 < -x := by grind
      rw [rd_neg_eq (by grind)]
      obtain ⟨e1, e2⟩ := rdPos_err (a := -x)
      have := half_ulp_le hn
      have : ¬ (0 ≤ x) := by grind
      simp only [this, ite_false]
      constructor <;> grind

/-- A positive multiple `N · 2^E` with `N ≤ 2^53` and `E ≥ -1074` is a double. -/
theorem rd_grid {N : Int} {E : Int} (hN : 0 ≤ N) (hN2 : N ≤ 2 ^ 53) (hE : -1074 ≤ E) :
    rd ((N : Rat) * pow2 E) = (N : Rat) * pow2 E := by
  have hp := pow2_pos E
  by_cases h0 : N = 0
  · subst h0; simp
  have hN0 : 0 < N := by omega
  have hNpos : (0 : Rat) < (N : Rat) := by exact_mod_cast hN0
  have hy : 0 < (N : Rat) * pow2 E := Rat.mul_pos hNpos hp
  rw [rd_pos_eq hy]
  -- ⌊log₂ y⌋ ≤ E + 53
  have hf : flog2 ((N : Rat) * pow2 E) ≤ E + 53 := by
    obtain ⟨a1, -⟩ := flog2_spec hy
    by_cases hc : flog2 ((N : Rat) * pow2 E) ≤ E + 53
    · exact hc
    · have := pow2_le_of_le (show E + 54 ≤ flog2 ((N : Rat) * pow2 E) by omega)
      have e54 : pow2 (E + ((54 : Nat) : Int)) = pow2 E * (2 : Rat) ^ 54 := pow2_add_nat E 54
      have : (N : Rat) ≤ ((2 ^ 53 : Int) : Rat) := by exact_mod_cast hN2
      have : (N : Rat) * pow2 E ≤ ((2 ^ 53 : Int) : Rat) * pow2 E :=
        Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hp)
      have : ((2 ^ 53 : Int) : Rat) * 2 = (2 : Rat) ^ 54 := by decide +kernel
      have : (E + ((54 : Nat) : Int)) = E + 54 := by omega
      grind
  by_cases hN53 : N = 2 ^ 53
  · subst hN53
    have hf' : ulpExp ((((2 : Int) ^ 53 : Int) : Rat) * pow2 E) ≤ E + 1 := by unfold ulpExp; omega
    apply rdPos_fix (2 ^ 52) (E + 1) hf'
    rw [pow2_succ]
    have : (((2 : Int) ^ 53 : Int) : Rat) = (((2 : Int) ^ 52 : Int) : Rat) * 2 := by decide +kernel
    rw [this]; grind
  · -- N < 2^53: ⌊log₂ y⌋ ≤ E + 52
    have hf2 : flog2 ((N : Rat) * pow2 E) ≤ E + 52 := by
      obtain ⟨a1, -⟩ := flog2_spec hy
      by_cases hc : flog2 ((N : Rat) * pow2 E) ≤ E + 52
      · exact hc
      · have := pow2_le_of_le (show E + 53 ≤ flog2 ((N : Rat) * pow2 E) by omega)
        have e53 : pow2 (E + ((53 : Nat) : Int)) = pow2 E * (2 : Rat) ^ 53 := pow2_add_nat E 53
        have : N + 1 ≤ 2 ^ 53 := by omega
        have : (N : Rat) + 1 ≤ ((2 ^ 53 : Int) : Rat) := by exact_mod_cast this
        have : ((N : Rat) + 1) * pow2 E ≤ ((2 ^ 53 : Int) : Rat) * pow2 E :=
          Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hp)
        have : ((2 ^ 53 : Int) : Rat) = (2 : Rat) ^ 53 := by decide +kernel
        have : (E + ((53 : Nat) : Int)) = E + 53 := by omega
        grind
    exact rdPos_fix N E (by unfold ulpExp; omega) rfl

/-- `rdPos a` is `N · 2^E` with `0 ≤ N ≤ 2^53` and `E = ulpExp a ≥ -1074`. -/
theorem rdPos_grid {a : Rat} (ha : 0 < a) :
    ∃ N : Int, 0 ≤ N ∧ N ≤ 2 ^ 53 ∧ rdPos a = (N : Rat) * pow2 (ulpExp a) ∧ -1074 ≤ ulpExp a := by
  refine ⟨rhe (a / pow2 (ulpExp a)), ?_, ?_, rfl, by unfold ulpExp; omega⟩
  · have hp := pow2_pos (ulpExp a)
    apply rhe_nonneg
    have : a / pow2 (ulpExp a) * pow2 (ulpExp a) = a := by
      have : pow2 (ulpExp a) ≠ 0 := by grind
      grind
    by_cases h : 0 ≤ a / pow2 (ulpExp a)
    · exact h
    · have := Rat.mul_lt_mul_of_pos_right (Rat.not_le.mp h) hp; grind
  · obtain ⟨-, a2⟩ := flog2_spec ha
    have hle : ulpExp a ≤ max (flog2 a + 1) (ulpExp a) := by omega
    have g := pow2_dvd hle
    have hk : (max (flog2 a + 1) (ulpExp a) - ulpExp a).toNat ≤ 53 := by unfold ulpExp; omega
    have hb : a ≤ (((2 : Int) ^ (max (flog2 a + 1) (ulpExp a) - ulpExp a).toNat : Int) : Rat) * pow2 (ulpExp a) := by
      rw [← g]; have := pow2_le_of_le (show flog2 a + 1 ≤ max (flog2 a + 1) (ulpExp a) by omega); grind
    have := rndAt_le (ulpExp a) _ hb
    have hp := pow2_pos (ulpExp a)
    have h1 : (rhe (a / pow2 (ulpExp a)) : Rat) ≤ (((2 : Int) ^ (max (flog2 a + 1) (ulpExp a) - ulpExp a).toNat : Int) : Rat) :=
      Rat.le_of_mul_le_mul_right this hp
    have h2 : rhe (a / pow2 (ulpExp a)) ≤ (2 : Int) ^ (max (flog2 a + 1) (ulpExp a) - ulpExp a).toNat := by exact_mod_cast h1
    have h3n : 2 ^ (max (flog2 a + 1) (ulpExp a) - ulpExp a).toNat ≤ 2 ^ 53 := Nat.pow_le_pow_right (by decide) hk
    have h3 : (2 : Int) ^ (max (flog2 a + 1) (ulpExp a) - ulpExp a).toNat ≤ 2 ^ 53 := by exact_mod_cast h3n
    omega

/-- **Rounding a double gives it back** (`rd` is idempotent). -/
theorem rd_rd (x : Rat) : rd (rd x) = rd x := by
  by_cases h0 : x = 0
  · subst h0; simp
  by_cases hp : 0 < x
  · rw [rd_pos_eq hp]
    obtain ⟨N, h1, h2, h3, h4⟩ := rdPos_grid hp
    rw [h3]; exact rd_grid h1 h2 h4
  · have hn : 0 < -x := by grind
    rw [rd_neg_eq (show x < 0 by grind), rd_neg]
    obtain ⟨N, h1, h2, h3, h4⟩ := rdPos_grid hn
    rw [h3, rd_grid h1 h2 h4]

/-- A positive number above half the smallest subnormal rounds to a positive double. -/
theorem rd_pos_of_gt {y : Rat} (h : pow2 (-1075) < y) : 0 < rd y := by
  have hy : 0 < y := by have := pow2_pos (-1075); grind
  rw [rd_pos_eq hy]
  unfold rdPos
  have hp := pow2_pos (ulpExp y)
  have hE : -1074 ≤ ulpExp y := by unfold ulpExp; omega
  -- 2^-1075 ≤ 2^E / 2, so y / 2^E > 1/2
  have h1 : pow2 (ulpExp y - 1) < y := by
    by_cases hc : ulpExp y = -1074
    · rw [hc]; exact h
    · have he : ulpExp y = flog2 y - 52 := by unfold ulpExp at hc ⊢; omega
      obtain ⟨a1, -⟩ := flog2_spec hy
      have := pow2_lt_of_lt (show ulpExp y - 1 < flog2 y by omega)
      grind
  have h2 : pow2 (ulpExp y) = pow2 (ulpExp y - 1) * 2 := by rw [← pow2_succ]; congr 1; omega
  have hm : 1 / 2 < y / pow2 (ulpExp y) := by
    have : pow2 (ulpExp y) ≠ 0 := by grind
    rw [Rat.lt_div_iff hp]; grind
  have := le_rhe (y / pow2 (ulpExp y))
  have hr : 0 < rhe (y / pow2 (ulpExp y)) := by
    have : (0 : Rat) < (rhe (y / pow2 (ulpExp y)) : Rat) := by grind
    exact_mod_cast this
  have : (1 : Rat) ≤ (rhe (y / pow2 (ulpExp y)) : Rat) := by exact_mod_cast hr
  exact Rat.mul_pos (by grind) hp

/-- The only double strictly between `-2^-1074` and `2^-1074` is 0. -/
theorem double_small {x : Rat} (hd : rd x = x) (h1 : -pow2 (-1074) < x) (h2 : x < pow2 (-1074)) : x = 0 := by
  by_cases h0 : x = 0
  · exact h0
  exfalso
  have key : ∀ a : Rat, 0 < a → rd a = a → pow2 (-1074) ≤ a := by
    intro a ha hda
    rw [rd_pos_eq ha] at hda
    obtain ⟨N, hN0, -, hN, hE⟩ := rdPos_grid ha
    rw [hN] at hda
    have hNpos : 0 < N := by
      by_cases hc : 0 < N
      · exact hc
      · have : N = 0 := by omega
        subst this; simp at hda; grind
    have : (1 : Rat) ≤ N := by exact_mod_cast hNpos
    have hpE := pow2_le_of_le hE
    have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt (pow2_pos (ulpExp a)))
    grind
  by_cases hp : 0 < x
  · have := key x hp hd; grind
  · have hn : 0 < -x := by grind
    have : rd (-x) = -x := by rw [rd_neg, hd]
    have := key (-x) hn this; grind


/-! ### Doubling and averaging doubles -/

/-- Twice a positive double is a double. -/
private theorem rd_two_mul_pos {x : Rat} (hp : 0 < x) (h : rd x = x) : rd (2 * x) = 2 * x := by
  rw [rd_pos_eq hp] at h
  obtain ⟨N, h1, h2, h3, h4⟩ := rdPos_grid hp
  have hx : 2 * x = (N : Rat) * pow2 (ulpExp x + 1) := by rw [pow2_succ]; grind
  rw [hx]; exact rd_grid h1 h2 (by omega)

/-- **Twice a double is a double.** `Binary64.rd` does not model overflow, so no upper
    bound is needed; doubling a subnormal stays on the grid. -/
theorem rd_two_mul {x : Rat} (h : rd x = x) : rd (2 * x) = 2 * x := by
  by_cases h0 : x = 0
  · subst h0; simp
  by_cases hp : 0 < x
  · exact rd_two_mul_pos hp h
  · have hn : 0 < -x := by grind
    have h' : rd (-x) = -x := by rw [rd_neg, h]
    have := rd_two_mul_pos hn h'
    rw [show 2 * -x = -(2 * x) by grind, rd_neg] at this
    grind

/-- If `2a ≤ y` for a double `a`, then `a ≤ rd (rd y / 2)`. -/
theorem le_rd_half {a y : Rat} (ha : rd a = a) (h : 2 * a ≤ y) : a ≤ rd (rd y / 2) := by
  have h1 := rd_mono h
  rw [rd_two_mul ha] at h1
  have h2 := rd_mono (show a ≤ rd y / 2 by grind)
  rwa [ha] at h2

/-- If `y ≤ 2b` for a double `b`, then `rd (rd y / 2) ≤ b`. -/
theorem rd_half_le {b y : Rat} (hb : rd b = b) (h : y ≤ 2 * b) : rd (rd y / 2) ≤ b := by
  have h1 := rd_mono h
  rw [rd_two_mul hb] at h1
  have h2 := rd_mono (show rd y / 2 ≤ b by grind)
  rwa [hb] at h2

end LeanAID.Binary64
