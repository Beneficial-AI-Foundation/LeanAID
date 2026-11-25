import LeanAID.Fixed.LowGlucose

/-!
# F-23: the trigger and theorems in the form of the other fixes

`LeanAID/Fixed/LowGlucose.lean` holds the fix and its original theorems
(`determineBasalPatched_eq`, `lgs_patched`, `lgs_patched_valid`). This file adds:

* `determineBasalF23_eq` (**nothing else changed**): without the trigger (`TriggerF23`:
  oref0 takes its low-glucose branch with a NaN duration), the fixed result is oref0's.
  No other hypothesis.
* `f23_fixed` (**the fix works**): with the trigger and valid input, the pump model accepts
  the fixed command (`validate` is not `none`), it issues no microbolus, and it sets rate 0
  for a whole number of minutes in [30, 120] or leaves a running zero temp.
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Proofs LeanAID.Time JsNum

/-- **F-23, nothing else changed.** If oref0 does not take its low-glucose branch with a
    NaN duration, the fixed result is oref0's result. -/
theorem determineBasalF23_eq (inp : DBInputs) (h : ¬ TriggerF23 inp) :
    determineBasalF23 inp = determineBasal inp := by
  unfold determineBasalF23 determineBasalPatched determineBasal
  cases hp : dbPrelude inp with
  | error r => rfl
  | ok pre =>
    simp only
    unfold dbDosePatched
    split
    · rfl
    · rename_i h1
      split
      · rename_i h2
        by_cases hd : lgsDur (dbPredict inp pre) = .nan
        · exfalso; apply h
          have hf : doseFirstBranch pre = false := by
            cases hb : doseFirstBranch pre
            · rfl
            · exact absurd hb h1
          have hl : (pre.bg <ʲ pre.threshold || (dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true := h2
          simp [TriggerF23, triggerF23, hp, hf, hl, hd, JsNum.isNaN]
        · rw [patchDur_of_ne hd]
          unfold dbDose
          simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
          rfl
      · rfl

/-- **F-23, the fix works.** For valid input with the trigger, the pump model accepts the
    fixed command, which issues no microbolus and either sets rate 0 for a whole number of
    minutes in `[30, 120]` or issues nothing while a temp with more than 20 minutes left and
    rate 0 (if it is a double) is running. -/
theorem f23_fixed {inp : DBInputs} (hv : ValidInput inp) (ht : TriggerF23 inp) :
    validate (determineBasalF23 inp) ≠ none ∧
    (determineBasalF23 inp).units = none ∧
    (((determineBasalF23 inp).rate = some 0 ∧
        ∃ q : Int, (determineBasalF23 inp).duration = some (.fin q) ∧ 30 ≤ q ∧ q ≤ 120) ∨
     ((determineBasalF23 inp).rate = none ∧ (determineBasalF23 inp).duration = none ∧
       ∃ c ctDur x, inp.currenttemp = some c ∧ c.duration = some (.fin ctDur) ∧ 20 < ctDur ∧
         c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) := by
  unfold TriggerF23 triggerF23 at ht
  cases hp : dbPrelude inp with
  | error r => rw [hp] at ht; cases ht
  | ok pre =>
    rw [hp] at ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨⟨hf, hl⟩, -⟩ := ht
    have hl' : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true := by
      simpa [Bool.or_eq_true] using hl
    exact ⟨lgs_patched_valid hv hp hl' hf, lgs_patched hv hp hl' hf⟩

/-- On the F-23 input (`f23Input`) the trigger holds. -/
theorem f23_trigger_example : TriggerF23 f23Input := by
  decide +kernel

end LeanAID.Fixed
