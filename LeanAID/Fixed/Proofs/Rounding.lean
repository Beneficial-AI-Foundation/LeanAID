import LeanAID.Fixed.Rounding
import LeanAID.Proofs.Headline
import LeanAID.Proofs.ReviewFindings

/-!
# F-04: theorems about the fixed rounding

* `triggerF04_iff`: what the trigger says, in plain terms.
* `determineBasalF04_eq` (**nothing else changed**): without the trigger, the fixed result
  is oref0's result. No hypothesis.
* `roundBasalDown_le`: `round_basal.down m` is between 0 and `m` (for `0 ≤ m ≤ 2^30`, a
  double).
* `f04_fixed` (**the fix works**): when the trigger holds, the fixed rate is between 0 and
  `maxSafeBasal`, and the duration and microbolus are oref0's.
* `f04_example`: the example of FINDINGS F-04 through `determine_basal`.
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Proofs JsNum
open LeanAID.Binary64 (rd rd_mono rd_nonneg rd_nonpos rd_intCast rd_rd)

/-- The trigger in plain terms: oref0's result has a rate `x`, and `x > maxSafeBasal`. -/
theorem triggerF04_iff (inp : DBInputs) :
    TriggerF04 inp ↔ ∃ p x, inp.profile = some p ∧ (determineBasal inp).rate = some x ∧
      (x >ʲ getMaxSafeBasal p) = true := by
  unfold TriggerF04 triggerF04
  constructor
  · intro h
    split at h
    · rename_i p x hp hx; exact ⟨p, x, hp, hx, h⟩
    · cases h
  · rintro ⟨p, x, hp, hx, h⟩
    simp [hp, hx, h]

theorem capRate_of_not {p : Profile} {r : Result}
    (h : ∀ x, r.rate = some x → (x >ʲ getMaxSafeBasal p) = false) : capRate p r = r := by
  unfold capRate
  cases hr : r.rate with
  | none => rfl
  | some x => simp [h x hr]

/-- **F-04, nothing else changed.** If oref0 issues no rate above `maxSafeBasal`, the
    fixed result is oref0's result. -/
theorem determineBasalF04_eq (inp : DBInputs) (h : ¬ TriggerF04 inp) :
    determineBasalF04 inp = determineBasal inp := by
  unfold determineBasalF04
  cases hp : inp.profile with
  | none => rfl
  | some p =>
    simp only
    apply capRate_of_not
    intro x hx
    cases hc : (x >ʲ getMaxSafeBasal p)
    · rfl
    · exact absurd ((triggerF04_iff inp).2 ⟨p, x, hp, hx, hc⟩) h

theorem basalScale_cases (x : JsNum) (m : Option String) :
    basalScale x m = 10 ∨ basalScale x m = 20 ∨ basalScale x m = 40 := by
  unfold basalScale lowestRateScale
  split
  · split
    · split <;> simp
    · simp
  · split <;> simp

/-- The JavaScript computation of `round_basal.down` on a number `M` with scale `s`. -/
theorem roundBasalDown_fin (M : Rat) (m : Option String) :
    roundBasalDown (.fin M) m =
      if M < rd (((rd (M * basalScale (.fin M) m)).floor : Rat) / basalScale (.fin M) m)
      then .fin (rd (rd (((rd (M * basalScale (.fin M) m)).floor : Rat) - 1) / basalScale (.fin M) m))
      else .fin (rd (((rd (M * basalScale (.fin M) m)).floor : Rat) / basalScale (.fin M) m)) := by
  have hs : basalScale (.fin M) m ≠ 0 := by
    rcases basalScale_cases (.fin M) m with h | h | h <;> rw [h] <;> decide
  unfold roundBasalDown
  simp only [fin_mul, mathFloor, fin_div hs, gt_fin, ofNat_eq, fin_sub, decide_eq_true_eq]

/-- The integer `k = ⌊rd(M·s)⌋` of `round_basal.down`, for `0 ≤ M ≤ 2^30`. -/
theorem roundBasalDown_k {M s : Rat} (h0 : 0 ≤ M) (h1 : M ≤ 2 ^ 30) (spos : 0 < s) (sle : s ≤ 40) :
    0 ≤ (rd (M * s)).floor ∧ (rd (M * s)).floor ≤ 137438953472 ∧
      ((rd (M * s)).floor : Rat) - 1 ≤ M * s - 1 / 2 := by
  have hMs0 : 0 ≤ M * s := Rat.mul_nonneg h0 (Rat.le_of_lt spos)
  have hMs : M * s ≤ 2 ^ 36 := by
    have a : M * s ≤ M * 40 := Rat.mul_le_mul_of_nonneg_left sle h0
    have b : M * 40 ≤ 2 ^ 30 * 40 := Rat.mul_le_mul_of_nonneg_right h1 (by decide)
    grind
  have hy0 : 0 ≤ rd (M * s) := rd_nonneg hMs0
  obtain ⟨-, hyle⟩ := rd_close hMs0
  have hKy : ((rd (M * s)).floor : Rat) ≤ rd (M * s) := Rat.floor_le _
  have tl := tiny_le
  have tp := tiny_pos
  refine ⟨Rat.le_floor_iff.mpr (by simpa using hy0), ?_, ?_⟩
  · have : ((rd (M * s)).floor : Rat) ≤ ((137438953472 : Int) : Rat) := by
      have : ((137438953472 : Int) : Rat) = 137438953472 := rfl
      grind
    exact Rat.intCast_le_intCast.mp this
  · have : M * s / 9007199254740992 + tiny ≤ 1 / 2 := by grind
    grind

/-- `rd (k - 1) = k - 1` for the integers of `round_basal.down`. -/
theorem rd_int_sub_one {K : Int} (h0 : 0 ≤ K) (h1 : K ≤ 137438953472) : rd ((K : Rat) - 1) = (K : Rat) - 1 := by
  have h := rd_intCast (n := K - 1) (by omega)
  rw [Rat.intCast_sub] at h
  exact h

/-- `round_basal.down` of a number `M` with `0 ≤ M ≤ 2^30` that is a double is a number
    between 0 and `M`. -/
theorem roundBasalDown_le {M : Rat} (m : Option String) (hd : rd M = M) (h0 : 0 ≤ M) (h1 : M ≤ 2 ^ 30) :
    ∃ r, roundBasalDown (.fin M) m = .fin r ∧ 0 ≤ r ∧ r ≤ M := by
  rw [roundBasalDown_fin]
  generalize hs : basalScale (.fin M) m = s
  have hs' : s = 10 ∨ s = 20 ∨ s = 40 := hs ▸ basalScale_cases _ _
  have spos : 0 < s := by rcases hs' with h | h | h <;> subst h <;> decide
  have sle : s ≤ 40 := by rcases hs' with h | h | h <;> subst h <;> decide
  obtain ⟨hK0, hK1, hKM⟩ := roundBasalDown_k h0 h1 spos sle
  generalize (rd (M * s)).floor = K at hK0 hK1 hKM ⊢
  have hK0' : (0 : Rat) ≤ K := by exact_mod_cast hK0
  split
  · rename_i hgt
    refine ⟨_, rfl, ?_, ?_⟩
    · -- K ≥ 1, because rd (K / s) > M ≥ 0
      have hKpos : 1 ≤ K := by
        by_cases hc : 1 ≤ K
        · exact hc
        · have : K = 0 := by omega
          subst this
          simp at hgt
          have := Binary64.rd_nonpos (show (0 : Rat) ≤ 0 by grind)
          grind
      rw [rd_int_sub_one hK0 hK1]
      apply rd_nonneg
      apply div_nonneg' spos
      have : (1 : Rat) ≤ K := by exact_mod_cast hKpos
      grind
    · rw [rd_int_sub_one hK0 hK1]
      have : ((K : Rat) - 1) / s ≤ M := by
        rw [div_le_iff_le_mul spos]
        grind
      have := rd_mono this
      rwa [hd] at this
  · rename_i hle
    exact ⟨_, rfl, rd_nonneg (div_nonneg' spos hK0'), by grind⟩

/-- **F-04, the fix works.** If oref0 issues a rate above `maxSafeBasal = M` (the trigger),
    where `M` is a double with `0 ≤ M ≤ 2^30`, then the fixed result issues a rate `r` with
    `0 ≤ r ≤ M`, and its duration and microbolus are oref0's. (Every number read from JSON is
    a double, and `M ≤ max_basal`; `ValidInput` gives both, V10.) -/
theorem f04_fixed {inp : DBInputs} (ht : TriggerF04 inp) {p : Profile} (hp : inp.profile = some p) {M : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hd : rd M = M) (h0 : 0 ≤ M) (h1 : M ≤ 2 ^ 30) :
    ∃ r, (determineBasalF04 inp).rate = some (.fin r) ∧ 0 ≤ r ∧ r ≤ M ∧
      (determineBasalF04 inp).duration = (determineBasal inp).duration ∧
      (determineBasalF04 inp).units = (determineBasal inp).units := by
  obtain ⟨p', x, hp', hx, hgt⟩ := (triggerF04_iff inp).1 ht
  rw [hp] at hp'; cases hp'
  obtain ⟨r, hr, r0, r1⟩ := roundBasalDown_le p.model hd h0 h1
  have e : determineBasalF04 inp = { (determineBasal inp).addReason ("; " ++ JsFmt.numToString x ++
      "U/hr is above maxSafeBasal " ++ JsFmt.numToString (getMaxSafeBasal p) ++ ": setting " ++
      JsFmt.numToString (roundBasalDown (getMaxSafeBasal p) p.model) ++ "U/hr")
      with rate := some (roundBasalDown (getMaxSafeBasal p) p.model) } := by
    have hge : (getMaxSafeBasal p ≥ʲ 0) = true := by rw [hM]; simpa using h0
    unfold determineBasalF04 capRate
    rw [hp]
    simp only [hx, hgt, hge, Bool.and_self, ite_true]
  rw [e]
  refine ⟨r, ?_, r0, r1, rfl, rfl⟩
  simp only [hM, hr]

/-- The F-04 example (FINDINGS) through `determine_basal`: `current_basal` 0.5,
    `max_basal` 0.83, BG 300 and rising. oref0 issues 0.85 U/h above `maxSafeBasal` 0.83;
    the fixed version issues 0.8 U/h. -/
theorem f04_example :
    let inp : DBInputs :=
      { glucose_status := some { glucose := some 300, delta := some 5, short_avgdelta := some 5, long_avgdelta := some 5, date := some (.fin 1795003200000) }
        currenttemp := some { duration := some 0, rate := some 0, temp := some "absolute" },
        iob_data := some (.single { iob := some 0, activity := some 0 }),
        profile := some { reviewProfile with current_basal := some 0.5, max_basal := some 0.83 },
        autosens_data := some { ratio := some 1 }, meal_data := some {}, clock := { now := 1795003200000 } }
    TriggerF04 inp ∧ (determineBasal inp).rate = some 0.85 ∧ (determineBasalF04 inp).rate = some 0.8 := by
  decide +kernel

end LeanAID.Fixed
