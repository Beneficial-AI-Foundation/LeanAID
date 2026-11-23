import LeanAID.Time.IobFacts

/-!
# Numeric frozen accounting on `iobTotal`

`iobRaw_append` (`Time/IobFacts.lean`) states the effect of one bolus on the raw IOB sum as
an identity between double expressions. This file turns it into a numeric bound.

Let `p` have the bilinear curve and finite DIA. Let `b` be a treatment of `u` units dated `t`,
with `|t − 1| ≤ 2⁵³` and `rd u ≠ 0`, and let no treatment of `R` be dated `≤ t`; this is where
`calcTempTreatments`, which sorts by date, puts `b`. If the raw IOB sum `x` of `L ++ R` at `t`
is finite and `|x|, |u| ≤ 2²⁰`, then inserting `b` between `L` and `R` raises the reported IOB
at `t` by `u` up to `1/1000 + 2⁻²⁸`. The term `1/1000` comes from
the 3-decimal rounding in total.js, the term `2⁻²⁸` from double rounding. The raw sum may be
negative, as zero temps make it.

**Theorems.**
- `round3_accounting`: the arithmetic core, on `Rat`.
- `iobTotal_insert_bolus_num`: the bound on `iobTotal`.

The exponential curves are not covered.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Iob Binary64 LeanAID.Proofs JsNum

/-- For `−M ≤ y ≤ M`: `y − M·2⁻⁵³ − tiny ≤ rd y ≤ y + M·2⁻⁵³ + tiny`. -/
theorem rd_near {y M : Rat} (h1 : -M ≤ y) (h2 : y ≤ M) :
    rd y ≤ y + M / 9007199254740992 + tiny ∧ y - M / 9007199254740992 - tiny ≤ rd y := by
  by_cases h : 0 ≤ y
  · obtain ⟨a, b⟩ := rd_close h
    constructor <;> grind
  · have h' : 0 ≤ -y := by grind
    obtain ⟨a, b⟩ := rd_close h'
    have e := rd_neg y
    constructor <;> grind

theorem tiny_small : tiny ≤ 1 / 1000000000000 :=
  Rat.le_trans tiny_le (by decide +kernel)

/-- The arithmetic of the 3-decimal rounding in total.js around one double addition. Write
    `round3(y) = rd(round(rd(y·1000)) / 1000)`, with `round` JavaScript's `Math.round`. If
    `|x| ≤ 2²⁰` and `|u| ≤ 2²⁰`, then
    `|round3(rd(x + rd u)) − round3(x) − u| ≤ 1/1000 + 2⁻²⁸`. -/
theorem round3_accounting {x u : Rat}
    (hx1 : -(2 ^ 20) ≤ x) (hx2 : x ≤ 2 ^ 20) (hu1 : -(2 ^ 20) ≤ u) (hu2 : u ≤ 2 ^ 20) :
    rd ((roundInt (rd (rd (x + rd u) * 1000)) : Rat) / 1000)
        - rd ((roundInt (rd (x * 1000)) : Rat) / 1000) - u ≤ 1 / 1000 + 1 / 2 ^ 28 ∧
    -(1 / 1000 + 1 / 2 ^ 28) ≤ rd ((roundInt (rd (rd (x + rd u) * 1000)) : Rat) / 1000)
        - rd ((roundInt (rd (x * 1000)) : Rat) / 1000) - u := by
  have ht0 := tiny_pos
  have ht := tiny_small
  have p20 : (2 : Rat) ^ 20 = 1048576 := by decide +kernel
  have p28 : (2 : Rat) ^ 28 = 268435456 := by decide +kernel
  rw [p20] at hx1 hx2 hu1 hu2
  rw [p28]
  -- the bolus as a double
  obtain ⟨v1, v2⟩ := rd_near (M := 1048576) hu1 hu2
  generalize rd u = v at v1 v2
  -- the new raw sum
  obtain ⟨s1, s2⟩ := rd_near (M := 4194304) (y := x + v) (by grind) (by grind)
  generalize rd (x + v) = s at s1 s2
  -- the two products by 1000
  obtain ⟨p1, p2⟩ := rd_near (M := 4294967296) (y := x * 1000) (by grind) (by grind)
  obtain ⟨q1, q2⟩ := rd_near (M := 4294967296) (y := s * 1000) (by grind) (by grind)
  generalize rd (x * 1000) = P at p1 p2
  generalize rd (s * 1000) = Q at q1 q2
  -- Math.round
  have m1 := roundInt_le P
  have m2 := lt_roundInt P
  have n1 := roundInt_le Q
  have n2 := lt_roundInt Q
  generalize (roundInt P : Rat) = m at m1 m2
  generalize (roundInt Q : Rat) = n at n1 n2
  -- the divisions by 1000
  obtain ⟨a1, a2⟩ := rd_near (M := 4194304) (y := m / 1000) (by grind) (by grind)
  obtain ⟨b1, b2⟩ := rd_near (M := 4194304) (y := n / 1000) (by grind) (by grind)
  constructor <;> grind

/-- total.js's 3-decimal rounding `Math.round(y * 1000) / 1000` of a finite double. -/
theorem round3_fin (y : Rat) :
    JsNum.mathRound (JsNum.fin y * 1000) / 1000 = .fin (rd ((roundInt (rd (y * 1000)) : Rat) / 1000)) := by
  show JsNum.div (JsNum.fin (roundInt (rd (y * 1000)) : Rat)) (JsNum.fin 1000) = _
  simp [JsNum.div]

/-! ### The bolus at its sorted position

`calcTempTreatments` sorts the treatments by date (`sortByKey (·.date)`), so a new bolus
dated `t` lands before every treatment dated after `t`, not at the end. `iobStep` skips a
treatment whose date is after `t` or NaN, so those treatments do not change the sums at
`t`. -/

theorem iobStep_skip (p : Profile) (t : Int) (curve : String) (dia peak : JsNum) (acc : IobAcc)
    (r : Treatment) (h : (r.date ≤ʲ JsNum.fin t) = false) :
    iobStep p t curve dia peak acc r = acc := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := acc
  simp [iobStep, h]

theorem foldl_iobStep_skip (p : Profile) (t : Int) (curve : String) (dia peak : JsNum)
    (R : List Treatment) (h : ∀ r ∈ R, (r.date ≤ʲ JsNum.fin t) = false) (acc : IobAcc) :
    R.foldl (iobStep p t curve dia peak) acc = acc := by
  induction R generalizing acc with
  | nil => rfl
  | cons r R ih =>
    simp only [List.foldl_cons]
    rw [iobStep_skip p t curve dia peak acc r (h r (by simp))]
    exact ih (fun r' hr' => h r' (by simp [hr'])) acc

/-- Treatments not dated `≤ t` at the end of the list do not change the raw sums at `t`. -/
theorem iobRaw_skip (L R : List Treatment) (p : Profile) (t : Int)
    (h : ∀ r ∈ R, (r.date ≤ʲ JsNum.fin t) = false) :
    iobRaw (L ++ R) p t = iobRaw L p t := by
  unfold iobRaw
  simp only [List.foldl_append]
  exact foldl_iobStep_skip _ _ _ _ _ R h _

/-- Let `p` have the bilinear curve and finite DIA, let `b` be a treatment of `u` units
    dated `t` with `|t − 1| ≤ 2⁵³` and `rd u ≠ 0`, and let no treatment of `R` be dated
    `≤ t`. Then the raw IOB sum at `t` of `L ++ b :: R` is the double sum of that of
    `L ++ R` and `rd u`. -/
theorem iobRaw_insert (L R : List Treatment) (p : Profile) (t : Int) (b : Treatment) (u d : Rat)
    (hc : (curveSetup p).1 = "bilinear") (hdia : (curveSetup p).2.1 = .fin d)
    (hi : b.insulin = some (.fin u)) (hdate : b.date = .fin t)
    (ht : (t - 1).natAbs ≤ 2 ^ 53) (hu : rd u ≠ 0)
    (hR : ∀ r ∈ R, (r.date ≤ʲ JsNum.fin t) = false) :
    (iobRaw (L ++ b :: R) p t).1 = (iobRaw (L ++ R) p t).1 + .fin (rd u) := by
  rw [show L ++ b :: R = (L ++ [b]) ++ R by simp, iobRaw_skip _ R p t hR, iobRaw_skip L R p t hR]
  exact iobRaw_append L p t b u d hc hdia hi hdate ht hu

/-- **Frozen accounting at the sorted position, numeric.** Let `p` have the bilinear curve
    and finite DIA, let `b` be a treatment of `u` units dated `t` with `|t − 1| ≤ 2⁵³` and
    `rd u ≠ 0`, and let no treatment of `R` be dated `≤ t`, as when `sortByKey (·.date)` puts
    `b` before the later treatments `R`. If the raw IOB sum of `L ++ R` at `t` is a finite `x`
    and `|x|, |u| ≤ 2²⁰`, then the reported IOBs `a` of `L ++ R` and `c` of `L ++ b :: R` at
    `t` are finite and `|c − a − u| ≤ 1/1000 + 2⁻²⁸`. -/
theorem iobTotal_insert_bolus_num (L R : List Treatment) (p : Profile) (t : Int) (b : Treatment)
    (u d x : Rat)
    (hc : (curveSetup p).1 = "bilinear") (hdia : (curveSetup p).2.1 = .fin d)
    (hi : b.insulin = some (.fin u)) (hdate : b.date = .fin t)
    (ht : (t - 1).natAbs ≤ 2 ^ 53) (hu : rd u ≠ 0)
    (hR : ∀ r ∈ R, (r.date ≤ʲ JsNum.fin t) = false)
    (hraw : (iobRaw (L ++ R) p t).1 = .fin x)
    (hx1 : -(2 ^ 20) ≤ x) (hx2 : x ≤ 2 ^ 20) (hu1 : -(2 ^ 20) ≤ u) (hu2 : u ≤ 2 ^ 20) :
    ∃ a c : Rat, (iobTotal (L ++ R) p t).iob = .fin a ∧ (iobTotal (L ++ b :: R) p t).iob = .fin c ∧
      c - a - u ≤ 1 / 1000 + 1 / 2 ^ 28 ∧ -(1 / 1000 + 1 / 2 ^ 28) ≤ c - a - u := by
  have h1 := iobTotal_iob (L ++ R) p t
  have h2 := iobTotal_iob (L ++ b :: R) p t
  rw [iobRaw_insert L R p t b u d hc hdia hi hdate ht hu hR, hraw] at h2
  rw [hraw] at h1
  have hs : JsNum.fin x + JsNum.fin (rd u) = .fin (rd (x + rd u)) := rfl
  rw [hs, round3_fin] at h2
  rw [round3_fin] at h1
  exact ⟨_, _, h1, h2, round3_accounting hx1 hx2 hu1 hu2⟩

end LeanAID.Time
