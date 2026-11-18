/-
  LeanAID.Core.Binary64Impl — a fast implementation of `Binary64.rd` with natural
  numbers only, and a proof that it equals `rd`.

  `rd` (Core/Binary64.lean) is written for the proofs: rational divisions and powers,
  each normalised with a gcd. The closed-loop simulation (sim/) evaluates it millions
  of times per simulated day, which made it about 10x too slow. `rdImpl` computes the
  same value from the numerator and denominator with bit lengths, one product, one
  integer division and one remainder. `rd_eq_rdImpl` proves `rd = rdImpl`; it is a
  `@[csimp]` lemma, so compiled code (the `aid-lean` binary, `native_decide`) runs
  `rdImpl` wherever the source says `rd`. The kernel and the proofs still see `rd`.
  No trusted step is added: the replacement is justified by the theorem.
-/
import LeanAID.Core.Binary64

namespace LeanAID.Binary64

/-- `flog2 (n/d)` for `n, d > 0`, comparing naturals instead of rationals. -/
def flogND (n d : Nat) : Int :=
  let k0 : Int := (n.log2 : Int) - (d.log2 : Int)
  if (if 0 ≤ k0 then d * 2 ^ k0.toNat ≤ n else d ≤ n * 2 ^ (-k0).toNat) then k0 else k0 - 1

/-- `rhe (N/D)` (round to nearest, ties to even) for `D > 0`, with `N / D` and `N % D`. -/
def rheND (N D : Nat) : Nat :=
  let q := N / D
  let r := N % D
  if 2 * r < D then q else if D < 2 * r then q + 1 else if q % 2 = 0 then q else q + 1

/-- `rdPos (n/d)` for `n, d > 0`. -/
def rdPosND (n d : Nat) : Rat :=
  let e := max (flogND n d - 52) (-1074)
  if 0 ≤ e then ((rheND n (d * 2 ^ e.toNat) * 2 ^ e.toNat : Nat) : Rat)
  else mkRat (rheND (n * 2 ^ (-e).toNat) d : Int) (2 ^ (-e).toNat)

/-- `rd` from the numerator and denominator. Equal to `rd` (`rd_eq_rdImpl`). -/
def rdImpl (x : Rat) : Rat :=
  if x.num = 0 then 0
  else if 0 < x.num then rdPosND x.num.natAbs x.den
  else -(rdPosND x.num.natAbs x.den)

/-! ### Proof of `rd = rdImpl` -/

private theorem pow2_nonneg_eq {e : Int} (h : 0 ≤ e) : pow2 e = ((2 ^ e.toNat : Nat) : Rat) := by
  unfold pow2; rw [if_pos h, Rat.natCast_pow]; rfl

private theorem pow2_neg_eq {e : Int} (h : ¬ 0 ≤ e) : pow2 e = 1 / ((2 ^ (-e).toNat : Nat) : Rat) := by
  unfold pow2; rw [if_neg h, Rat.natCast_pow]; rfl

private theorem natCast_pos {n : Nat} (h : 0 < n) : (0 : Rat) < (n : Rat) := by
  have := (Rat.natCast_lt_natCast (a := 0) (b := n)).mpr h
  simpa using this

private theorem two_pow_nat_pos (k : Nat) : 0 < 2 ^ k := Nat.two_pow_pos k

/-- A positive rational is its numerator's absolute value over its denominator. -/
private theorem pos_eq_nd {a : Rat} (ha : 0 < a) :
    a = ((a.num.natAbs : Nat) : Rat) / ((a.den : Nat) : Rat) := by
  have hn : 0 ≤ a.num := Rat.num_nonneg.mpr (Rat.le_of_lt ha)
  have h1 : ((a.num.natAbs : Nat) : Int) = a.num := by omega
  have h2 : ((a.num.natAbs : Nat) : Rat) = ((a.num : Int) : Rat) := by
    rw [← h1]; rfl
  rw [h2]
  have := Rat.num_divInt_den a
  rw [Rat.divInt_eq_div] at this
  exact this.symm

/-- `a ≤ n/d ↔ a·d ≤ n` and `n/d < b ↔ n < b·d` for `d > 0`. -/
private theorem le_div_iff' {a n d : Rat} (hd : 0 < d) : a ≤ n / d ↔ a * d ≤ n := by
  constructor
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_le.mpr ((Rat.div_lt_iff hd).mpr h') h
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_le.mpr ((Rat.div_lt_iff hd).mp h') h

theorem flog2_eq_flogND {a : Rat} (ha : 0 < a) : flog2 a = flogND a.num.natAbs a.den := by
  have hd : 0 < a.den := Rat.den_pos a
  have hdR : (0 : Rat) < ((a.den : Nat) : Rat) := natCast_pos hd
  unfold flog2 flogND
  simp only
  generalize hk : (a.num.natAbs.log2 : Int) - (a.den.log2 : Int) = k0
  have haeq := pos_eq_nd ha
  generalize a.num.natAbs = n at *
  generalize a.den = d at *
  subst haeq
  congr 1
  apply propext
  by_cases h0 : 0 ≤ k0
  · rw [if_pos h0, pow2_nonneg_eq h0, le_div_iff' hdR, ← Rat.natCast_mul,
      Rat.natCast_le_natCast, Nat.mul_comm]
  · rw [if_neg h0, pow2_neg_eq h0, le_div_iff' hdR]
    have hp : (0 : Rat) < ((2 ^ (-k0).toNat : Nat) : Rat) := natCast_pos (two_pow_nat_pos _)
    constructor
    · intro h
      have h' : (1 / ((2 ^ (-k0).toNat : Nat) : Rat)) * (d : Rat) * ((2 ^ (-k0).toNat : Nat) : Rat)
          ≤ (n : Rat) * ((2 ^ (-k0).toNat : Nat) : Rat) := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hp)
      have : (1 / ((2 ^ (-k0).toNat : Nat) : Rat)) * (d : Rat) * ((2 ^ (-k0).toNat : Nat) : Rat)
          = (d : Rat) := by
        have : ((2 ^ (-k0).toNat : Nat) : Rat) ≠ 0 := by grind
        grind
      rw [this, ← Rat.natCast_mul, Rat.natCast_le_natCast] at h'
      exact h'
    · intro h
      have h' : (d : Rat) ≤ (n : Rat) * ((2 ^ (-k0).toNat : Nat) : Rat) := by
        rw [← Rat.natCast_mul, Rat.natCast_le_natCast]; exact h
      have : (1 / ((2 ^ (-k0).toNat : Nat) : Rat)) * (d : Rat)
          = (d : Rat) / ((2 ^ (-k0).toNat : Nat) : Rat) := by grind
      rw [this]
      exact Rat.not_lt.mp fun hlt => by
        have := (Rat.lt_div_iff hp).mp hlt
        exact Rat.not_le.mpr this h'

theorem rhe_eq_rheND (N D : Nat) (hD : 0 < D) :
    rhe ((N : Rat) / (D : Rat)) = ((rheND N D : Nat) : Int) := by
  have hDR : (0 : Rat) < (D : Rat) := natCast_pos hD
  have hdm := Nat.div_add_mod N D
  generalize hq : N / D = q at hdm
  generalize hr : N % D = r at hdm
  have hrD : r < D := by rw [← hr]; exact Nat.mod_lt _ hD
  -- N/D = q + r/D
  have hsplit : (N : Rat) / (D : Rat) = (q : Rat) + (r : Rat) / (D : Rat) := by
    have : (N : Rat) = (D : Rat) * (q : Rat) + (r : Rat) := by
      rw [← hdm, Rat.natCast_add, Rat.natCast_mul]
    rw [this]
    have : (D : Rat) ≠ 0 := by grind
    grind
  have hr0 : (0 : Rat) ≤ (r : Rat) / (D : Rat) := by
    have : (0 : Rat) ≤ (r : Rat) := by simpa using (Rat.natCast_le_natCast (a := 0) (b := r)).mpr (Nat.zero_le r)
    exact (le_div_iff' hDR).mpr (by simpa using this)
  have hr1 : (r : Rat) / (D : Rat) < 1 := by
    rw [Rat.div_lt_iff hDR]; simpa using (Rat.natCast_lt_natCast.mpr hrD)
  have hfloor : ((N : Rat) / (D : Rat)).floor = (q : Int) := by
    apply Int.le_antisymm
    · have : ((N : Rat) / (D : Rat)).floor < (q : Int) + 1 := by
        rw [Rat.floor_lt_iff, hsplit]
        have : (((q : Int) + 1 : Int) : Rat) = (q : Rat) + 1 := by rw [Rat.intCast_add]; rfl
        rw [this]; grind
      omega
    · rw [Rat.le_floor_iff, hsplit]
      have : (((q : Int) : Int) : Rat) = (q : Rat) := rfl
      rw [this]; grind
  have hfrac : (N : Rat) / (D : Rat) - (((q : Int) : Int) : Rat) = (r : Rat) / (D : Rat) := by
    rw [hsplit]; have : (((q : Int)) : Rat) = (q : Rat) := rfl
    rw [this]; grind
  have hlt : (r : Rat) / (D : Rat) < 1 / 2 ↔ 2 * r < D := by
    rw [Rat.div_lt_iff hDR]
    have : (1 / 2 : Rat) * (D : Rat) = (D : Rat) / 2 := by grind
    rw [this, Rat.lt_div_iff (by decide)]
    rw [show (r : Rat) * 2 = ((r * 2 : Nat) : Rat) by simp, Rat.natCast_lt_natCast]
    omega
  have hgt : 1 / 2 < (r : Rat) / (D : Rat) ↔ D < 2 * r := by
    rw [Rat.lt_div_iff hDR]
    have : (1 / 2 : Rat) * (D : Rat) = (D : Rat) / 2 := by grind
    rw [this, Rat.div_lt_iff (by decide)]
    rw [show (r : Rat) * 2 = ((r * 2 : Nat) : Rat) by simp, Rat.natCast_lt_natCast]
    omega
  unfold rhe rheND
  simp only
  rw [hfloor, hfrac, hq, hr]
  by_cases h1 : 2 * r < D
  · rw [if_pos (hlt.mpr h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hlt.mp h)), if_neg h1]
    by_cases h2 : D < 2 * r
    · rw [if_pos (hgt.mpr h2), if_pos h2]; simp
    · rw [if_neg (fun h => h2 (hgt.mp h)), if_neg h2]
      by_cases h3 : q % 2 = 0
      · rw [if_pos (by omega), if_pos h3]
      · rw [if_neg (by omega), if_neg h3]; simp

theorem rdPos_eq_rdPosND {a : Rat} (ha : 0 < a) : rdPos a = rdPosND a.num.natAbs a.den := by
  have hd : 0 < a.den := Rat.den_pos a
  have haeq := pos_eq_nd ha
  unfold rdPos rdPosND ulpExp
  rw [flog2_eq_flogND ha]
  simp only
  generalize max (flogND a.num.natAbs a.den - 52) (-1074) = e
  generalize a.num.natAbs = n at haeq ⊢
  generalize a.den = d at haeq hd ⊢
  by_cases he : 0 ≤ e
  · rw [if_pos he, pow2_nonneg_eq he]
    have hp : 0 < 2 ^ e.toNat := two_pow_nat_pos _
    have hpR : (0 : Rat) < ((2 ^ e.toNat : Nat) : Rat) := natCast_pos hp
    have hdR : (0 : Rat) < (d : Rat) := natCast_pos hd
    have : a / ((2 ^ e.toNat : Nat) : Rat) = (n : Rat) / ((d * 2 ^ e.toNat : Nat) : Rat) := by
      rw [haeq, Rat.natCast_mul]
      have : (d : Rat) ≠ 0 := by grind
      have : ((2 ^ e.toNat : Nat) : Rat) ≠ 0 := by grind
      grind
    rw [this, rhe_eq_rheND n (d * 2 ^ e.toNat) (Nat.mul_pos hd hp), Rat.natCast_mul]
    rfl
  · rw [if_neg he, pow2_neg_eq he, Rat.mkRat_eq_div]
    have hp : 0 < 2 ^ (-e).toNat := two_pow_nat_pos _
    have hpR : (0 : Rat) < ((2 ^ (-e).toNat : Nat) : Rat) := natCast_pos hp
    have : a / (1 / ((2 ^ (-e).toNat : Nat) : Rat)) = ((n * 2 ^ (-e).toNat : Nat) : Rat) / (d : Rat) := by
      rw [haeq, Rat.natCast_mul]
      have : ((2 ^ (-e).toNat : Nat) : Rat) ≠ 0 := by grind
      grind
    rw [this, rhe_eq_rheND _ d hd]
    have : (((rheND (n * 2 ^ (-e).toNat) d : Nat) : Int) : Rat) = ((rheND (n * 2 ^ (-e).toNat) d : Nat) : Rat) := rfl
    rw [this]
    have : ((2 ^ (-e).toNat : Nat) : Rat) ≠ 0 := by grind
    grind

@[csimp] theorem rd_eq_rdImpl : @rd = @rdImpl := by
  funext x
  unfold rd rdImpl
  by_cases h0 : x.num = 0
  · have : x = 0 := Rat.num_eq_zero.mp h0
    rw [if_pos this, if_pos h0]
  · have hx0 : x ≠ 0 := fun h => h0 (Rat.num_eq_zero.mpr h)
    rw [if_neg hx0, if_neg h0]
    by_cases hp : 0 < x.num
    · have hx : 0 < x := by
        have := Rat.num_nonneg.mp (Int.le_of_lt hp)
        exact Rat.lt_of_le_of_ne this (Ne.symm hx0)
      rw [if_pos hx, if_pos hp, rdPos_eq_rdPosND hx]
    · have hx : ¬ 0 < x := by
        intro h; exact hp (by have := Rat.num_nonneg.mpr (Rat.le_of_lt h); omega)
      have hnx : 0 < -x := by
        have : x < 0 := Rat.lt_of_le_of_ne (Rat.not_lt.mp hx) hx0
        grind
      rw [if_neg hx, if_neg hp, rdPos_eq_rdPosND hnx, Rat.neg_num, Rat.neg_den, Int.natAbs_neg]

end LeanAID.Binary64
