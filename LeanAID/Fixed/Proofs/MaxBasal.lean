import LeanAID.Fixed.MaxBasal
import LeanAID.Proofs.ReviewFindings

/-!
# F-12: theorems about the fixed handling of a missing maximum basal

* `triggerF12_of_missing`: a missing or non-numeric `max_basal` or `max_daily_basal`
  triggers the fix.
* `determineBasalF12_eq` (**nothing else changed**): if `maxSafeBasal` is a positive number
  (`¬ TriggerF12`), the fixed result is oref0's result. No other hypothesis.
* `f12_fixed` (**the fix works**): with the trigger, no microbolus and no rate other than 0;
  when no rate is issued, the running temp is not above `current_basal`; the reason says
  why.
* `f12_example`: on the input of `missing_max_basal_no_clamp`, where oref0 issues 5.9 U/h,
  the fixed version issues nothing, and with a 2 U/h temp running it cancels the temp.
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Proofs JsNum

theorem nan_mul (x : JsNum) : JsNum.nan * x = .nan := by cases x <;> rfl
theorem mul_nan (x : JsNum) : x * JsNum.nan = .nan := by cases x <;> rfl

/-- A missing or non-numeric `max_basal` or `max_daily_basal` makes `maxSafeBasal` NaN,
    which triggers the fix (given a profile with `current_basal`). -/
theorem triggerF12_of_missing {inp : DBInputs} {p : Profile} (hp : inp.profile = some p)
    (hcb : p.current_basal.isSome)
    (h : p.max_basal.js = .nan ∨ p.max_daily_basal.js = .nan) : TriggerF12 inp := by
  have hM : getMaxSafeBasal p = .nan := by
    unfold getMaxSafeBasal JsNum.min3
    rcases h with h | h
    · rw [h]; rfl
    · rw [h, mul_nan]
      cases p.max_basal.js <;> rfl
  simp [TriggerF12, triggerF12, hp, hcb, maxSafeOk, hM]

/-- If `stProfile` fails, oref0 returns its error. -/
theorem determineBasal_of_stProfile_error {inp : DBInputs} {r : Result} (h : stProfile inp = .error r) :
    determineBasal inp = r := by
  unfold determineBasal dbPrelude
  simp [h, bind, Except.bind]

/-- **F-12, nothing else changed.** If oref0's `maxSafeBasal` is a positive number (or
    oref0 stops earlier, without a profile or `current_basal`), the fixed result is oref0's
    result. -/
theorem determineBasalF12_eq (inp : DBInputs) (h : ¬ TriggerF12 inp) :
    determineBasalF12 inp = determineBasal inp := by
  unfold determineBasalF12
  cases hs : stProfile inp with
  | error r => exact (determineBasal_of_stProfile_error hs).symm
  | ok p =>
    simp only
    have hp := stProfile_ok hs
    have hcb : p.current_basal.isSome := by
      unfold stProfile at hs; rw [hp] at hs
      cases hc : p.current_basal with
      | none => simp [hc] at hs
      | some _ => rfl
    have hok : maxSafeOk p = true := by
      cases hm : maxSafeOk p with
      | true => rfl
      | false => exact absurd (by simp [TriggerF12, triggerF12, hp, hcb, hm]) h
    simp [hok]

/-- With the trigger, `determineBasalF12` returns `refuseF12`. -/
theorem determineBasalF12_refuse {inp : DBInputs} (ht : TriggerF12 inp) :
    ∃ p, inp.profile = some p ∧ determineBasalF12 inp = refuseF12 inp p := by
  unfold TriggerF12 triggerF12 at ht
  cases hp : inp.profile with
  | none => rw [hp] at ht; cases ht
  | some p =>
    rw [hp] at ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
    obtain ⟨hcb, hok⟩ := ht
    have hne : p.current_basal ≠ none := by intro h; simp [h] at hcb
    have hs : stProfile inp = .ok p := by simp [stProfile, hp, hne]
    refine ⟨p, rfl, ?_⟩
    unfold determineBasalF12
    simp [hs, hok]

/-- **F-12, the fix works.** If `maxSafeBasal` is not a positive number (the trigger), the
    fixed version issues no microbolus and no rate other than 0 (a cancel or a zero temp),
    so no rate above `current_basal`; when it issues no rate, the running temp is not above
    `current_basal`. (`f12_example` checks the reason on one input.) -/
theorem f12_fixed {inp : DBInputs} (ht : TriggerF12 inp) :
    ∃ p, inp.profile = some p ∧
    (determineBasalF12 inp).units = none ∧
    ((determineBasalF12 inp).rate = none ∨ (determineBasalF12 inp).rate = some 0) ∧
    ((determineBasalF12 inp).rate = none →
      ∀ ct, inp.currenttemp = some ct → (ct.rate.js >ʲ p.current_basal.js) = false) := by
  obtain ⟨p, hp, e⟩ := determineBasalF12_refuse ht
  refine ⟨p, hp, ?_⟩
  rw [e]
  unfold refuseF12
  cases hct : inp.currenttemp with
  | none =>
    refine ⟨rfl, Or.inl rfl, ?_⟩
    intro _ ct h; cases h
  | some ct =>
    simp only
    by_cases h1 : (ct.rate.js >ʲ p.current_basal.js) = true
    · simp only [h1, ite_true]
      refine ⟨rfl, Or.inr trivial, ?_⟩
      intro h; cases h
    · by_cases h2 : (ct.rate.js =ʲ 0 && ct.duration.js >ʲ 30) = true
      · simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false]
        refine ⟨rfl, Or.inr trivial, ?_⟩
        intro h; cases h
      · simp only [h1, h2, Bool.false_eq_true, ite_false]
        refine ⟨rfl, Or.inl rfl, ?_⟩
        intro _ ct' hct'; cases hct'; simpa using h1

/-- With the trigger, every rate the fixed version issues is 0. So if `current_basal` is a
    number `cb ≥ 0`, no issued rate is above it. -/
theorem f12_rate_le {inp : DBInputs} (ht : TriggerF12 inp) :
    ∀ r, (determineBasalF12 inp).rate = some (.fin r) → r = 0 ∧
      ∀ p cb, inp.profile = some p → p.current_basal = some (.fin cb) → 0 ≤ cb → r ≤ cb := by
  intro r hr
  obtain ⟨p', -, -, hrate, -⟩ := f12_fixed ht
  rcases hrate with h | h <;> rw [h] at hr <;> cases hr
  exact ⟨rfl, fun _ _ _ _ h0 => h0⟩

/-- On the input of `missing_max_basal_no_clamp` (no `max_basal`, no `max_daily_basal`,
    BG 300 and rising), oref0 issues 5.9 U/h; the fixed version issues no rate. With a
    2 U/h temp running for 20 more minutes, the fixed version cancels it (rate 0,
    duration 0). -/
theorem f12_example :
    let inp : DBInputs :=
      { glucose_status := some { glucose := some 300, delta := some 5, short_avgdelta := some 5, long_avgdelta := some 5, date := some (.fin 1795003200000) }
        currenttemp := some { duration := some 0, rate := some 0, temp := some "absolute" },
        iob_data := some (.single { iob := some 0, activity := some 0 }),
        profile := some { reviewProfile with max_basal := none, max_daily_basal := none },
        autosens_data := some { ratio := some 1 }, meal_data := some {}, clock := { now := 1795003200000 } }
    TriggerF12 inp ∧ (determineBasal inp).rate = some 5.9 ∧
    (determineBasalF12 inp).rate = none ∧ (determineBasalF12 inp).units = none ∧
    ((determineBasalF12 inp).reason.getD "").startsWith "Error: maxSafeBasal NaN is not a positive number" ∧
    (determineBasalF12 { inp with currenttemp := some { duration := some 20, rate := some 2, temp := some "absolute" } }).rate = some 0 ∧
    (determineBasalF12 { inp with currenttemp := some { duration := some 20, rate := some 2, temp := some "absolute" } }).duration = some 0 := by
  decide +kernel

end LeanAID.Fixed
