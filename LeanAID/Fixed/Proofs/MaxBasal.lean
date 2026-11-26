import LeanAID.Fixed.MaxBasal
import LeanAID.Fixed.Proofs.Rounding
import LeanAID.Proofs.ReviewFindings

/-!
# F-12: theorems about the fixed handling of a missing maximum basal

* `triggerF12_of_missing`: a missing or non-numeric `max_basal` or `max_daily_basal`
  triggers the fix.
* `determineBasalF12_eq` (**nothing else changed**): if `maxSafeBasal` is a positive number
  (`¬ TriggerF12`), the fixed result is oref0's result. No other hypothesis.
* `f12_fixed` (**the fix works**): with the trigger and a `current_basal` that is a double
  `cb` in `[0, 2^30]`, no microbolus, no finite rate above `cb`, and when no rate is issued
  (and the result is not an error) the running temp is not above `current_basal`.
* `maxSafe_capProfile`: the capped profile's `maxSafeBasal` is `current_basal`.
* `dbDose_units_noSmb`, `determineBasal_units_noSmb`: with `microBolusAllowed = false`,
  oref0 sets no microbolus.
* `f12_example`, `f12_lgs_example`: on the input of `missing_max_basal_no_clamp`, oref0
  issues 5.9 U/h, the fixed version 0.9 U/h (the scheduled basal); with a 2 U/h temp running,
  it cancels the temp; at BG 60 and falling, it sets a zero temp, as oref0 does.
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Proofs JsNum
open LeanAID.Binary64 (rd)

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

/-- The trigger, unpacked. -/
theorem triggerF12_iff {inp : DBInputs} :
    TriggerF12 inp ↔ ∃ p, inp.profile = some p ∧ p.current_basal.isSome = true ∧ maxSafeOk p = false := by
  unfold TriggerF12 triggerF12
  cases hp : inp.profile with
  | none => simp
  | some p => simp

/-- **F-12, nothing else changed.** If oref0's `maxSafeBasal` is a positive number (or
    oref0 stops earlier, without a profile or `current_basal`), the fixed result is oref0's
    result. -/
theorem determineBasalF12_eq (inp : DBInputs) (h : ¬ TriggerF12 inp) :
    determineBasalF12 inp = determineBasal inp := by
  unfold determineBasalF12
  cases hp : inp.profile with
  | none => rfl
  | some p =>
    have : triggerF12 inp = false := by simpa [TriggerF12] using h
    simp [this]

/-- With the trigger, `determineBasalF12` is `postF12` of the F-04 step on `inputF12`. -/
theorem determineBasalF12_trigger {inp : DBInputs} (ht : TriggerF12 inp) :
    ∃ p, inp.profile = some p ∧ p.current_basal.isSome = true ∧ maxSafeOk p = false ∧
      determineBasalF12 inp = postF12 inp p (capRate (capProfile p) (determineBasal (inputF12 inp p))) := by
  obtain ⟨p, hp, hcb, hok⟩ := triggerF12_iff.mp ht
  refine ⟨p, hp, hcb, hok, ?_⟩
  have ht' : triggerF12 inp = true := ht
  unfold determineBasalF12; rw [hp]; simp only [ht', ite_true]
  rfl

/-! ### The capped profile -/

/-- The capped profile's `maxSafeBasal` is `current_basal` (a double). -/
theorem maxSafe_capProfile {p : Profile} {c : Rat} (hc : p.current_basal = some (.fin c)) (hd : rd c = c) :
    getMaxSafeBasal (capProfile p) = .fin c := by
  have h1 : (JsNum.fin 1 * JsNum.fin c : JsNum) = .fin c := by
    show JsNum.fin (rd (1 * c)) = _; rw [Rat.one_mul, hd]
  simp only [getMaxSafeBasal, capProfile, multiplierOr, hc, Option.js_some, h1, JsNum.min3]
  simp [JsNum.min]

/-! ### No microbolus without `microBolusAllowed` -/

theorem highTemp_units_noSmb (c : Ctx) (rT : Result) (h : c.microBolusAllowed = false) :
    (highTemp c rT).units = rT.units := by
  unfold highTemp
  simp only [h, Bool.false_and, Bool.false_eq_true, ite_false]
  split <;> rw [highTempSet_units] <;> simp [Result.addReasonIf, Result.addReason] <;> split <;> rfl

/-- With `microBolusAllowed = false`, oref0's dose phase keeps the units of `c.rT`. -/
theorem dbDose_units_noSmb (c : Ctx) (h : c.microBolusAllowed = false) : (dbDose c).units = c.rT.units := by
  have rest : ∀ rT : Result, rT.units = c.rT.units → (dbDose.dbDoseRest c rT).units = c.rT.units := by
    intro rT h0
    unfold dbDose.dbDoseRest
    simp only
    repeat' split
    all_goals first
      | simp [h0]
      | (rw [neutralTemp_units]; simp [h0])
      | (rw [lowEventualBG_units]; simp [h0])
      | (rw [highTemp_units_noSmb _ _ h]; simp [h0])
  unfold dbDose
  simp only
  split
  · exact rest _ (by simp [Result.addReason])
  · split
    · simp [Result.addReason]
    · exact rest _ rfl

theorem dbPredict_rT_units (inp : DBInputs) (pre : Pre) : (dbPredict inp pre).rT.units = none := by
  cases h : (dbPredict inp pre).rT.units with
  | none => rfl
  | some u => simp at h

theorem dbPredict_mba (inp : DBInputs) (pre : Pre) :
    (dbPredict inp pre).microBolusAllowed = inp.microBolusAllowed := rfl

/-- **No microbolus without `microBolusAllowed`.** If the profile's `maxSafeBasal` is a
    number `≥ 0` (so that oref0's early cancels are understood), oref0 with
    `microBolusAllowed = false` sets no microbolus. -/
theorem determineBasal_units_noSmb {inp : DBInputs} (h : inp.microBolusAllowed = false)
    (hM : ∀ p, inp.profile = some p → ∃ M, getMaxSafeBasal p = .fin M ∧ 0 ≤ M) :
    (determineBasal inp).units = none := by
  unfold determineBasal
  cases hpre : dbPrelude inp with
  | error e => exact (prelude_error hpre hM).1
  | ok pre =>
    simp only
    rw [dbDose_units_noSmb _ (by rw [dbPredict_mba]; exact h)]
    exact dbPredict_rT_units inp pre

/-! ### The last step, `postF12` -/

theorem postF12_units (inp : DBInputs) (p : Profile) (U : Result) : (postF12 inp p U).units = U.units := by
  unfold postF12
  split
  · rfl
  · dsimp only
    split <;> split <;> (try split) <;> rfl

theorem postF12_shape (inp : DBInputs) (p : Profile) (U : Result) : (postF12 inp p U).shape = U.shape := by
  unfold postF12
  split
  · rfl
  · dsimp only
    split <;> split <;> (try split) <;> rfl

theorem postF12_error (inp : DBInputs) (p : Profile) (U : Result) : (postF12 inp p U).error = U.error := by
  unfold postF12
  split
  · rfl
  · dsimp only
    split <;> split <;> (try split) <;> rfl

/-- `postF12` keeps the rate, or replaces no rate by a cancel (rate 0, duration 0). -/
theorem postF12_rate (inp : DBInputs) (p : Profile) (U : Result) :
    ((postF12 inp p U).rate = U.rate ∧ (postF12 inp p U).duration = U.duration) ∨
    (U.rate = none ∧ (postF12 inp p U).rate = some 0 ∧ (postF12 inp p U).duration = some 0) := by
  unfold postF12
  split
  · left; exact ⟨rfl, rfl⟩
  · dsimp only
    split <;> split <;> (try split) <;> simp_all

/-- If `postF12` issues no rate, then neither did `U`, and `U` is an error or the running
    temp is not above `current_basal`. -/
theorem postF12_none {inp : DBInputs} {p : Profile} {U : Result} (h : (postF12 inp p U).rate = none) :
    U.rate = none ∧ (U.shape = .error ∨
      ∀ ct, inp.currenttemp = some ct → (ct.rate.js >ʲ p.current_basal.js) = false) := by
  unfold postF12 at h
  split at h
  · rename_i he; exact ⟨h, Or.inl he⟩
  · dsimp only at h
    have hr : U.rate = none := by
      revert h; split <;> split <;> (try split) <;> simp_all
    refine ⟨hr, Or.inr fun ct hct => ?_⟩
    revert h
    cases hR : U.reason <;> simp only [hr, hct] <;> split <;> simp_all

/-- `postF12` leaves a result with a rate alone except for the reason. -/
theorem postF12_some {inp : DBInputs} {p : Profile} {U : Result} {x : JsNum} (h : U.rate = some x) :
    (postF12 inp p U).rate = some x ∧ (postF12 inp p U).duration = U.duration := by
  rcases postF12_rate inp p U with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨h1 ▸ h, h2⟩
  · rw [h] at h1; cases h1

/-! ### The fix works -/

/-- **F-12, the fix works.** If `maxSafeBasal` is not a positive number (the trigger) and
    `current_basal` is a double `cb` in `[0, 2^30]` (every number read from JSON is a double),
    the fixed version issues no microbolus and no finite rate above `cb`; when it issues no
    rate and its result is not an error, the running temp is not above `current_basal`. -/
theorem f12_fixed {inp : DBInputs} (ht : TriggerF12 inp) {p : Profile} {c : Rat}
    (hp : inp.profile = some p) (hc : p.current_basal = some (.fin c)) (hd : rd c = c)
    (h0 : 0 ≤ c) (h1 : c ≤ 2 ^ 30) :
    (determineBasalF12 inp).units = none ∧
    (∀ r, (determineBasalF12 inp).rate = some (.fin r) → r ≤ c) ∧
    ((determineBasalF12 inp).rate = none → (determineBasalF12 inp).shape ≠ .error →
      ∀ ct, inp.currenttemp = some ct → (ct.rate.js >ʲ p.current_basal.js) = false) := by
  obtain ⟨p', hp', -, -, e⟩ := determineBasalF12_trigger ht
  rw [hp] at hp'; cases hp'
  have hM := maxSafe_capProfile hc hd
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · rw [postF12_units, capRate_units]
    apply determineBasal_units_noSmb rfl
    intro q hq
    have : q = capProfile p := (Option.some.inj hq).symm
    subst this; exact ⟨c, hM, h0⟩
  · intro r hr
    rcases postF12_rate inp p (capRate (capProfile p) (determineBasal (inputF12 inp p))) with ⟨h1', -⟩ | ⟨-, h1', -⟩
    · rw [h1'] at hr
      rcases capRate_rate hM hd h0 h1 hr with ⟨-, hle⟩ | ⟨-, hle, -⟩ <;> exact hle
    · rw [h1'] at hr
      have : (0 : JsNum) = .fin r := Option.some.inj hr
      cases this; exact h0
  · intro hn hs ct hct
    obtain ⟨-, h⟩ := postF12_none hn
    rcases h with h | h
    · exact absurd (by rw [postF12_shape, h]) hs
    · exact h ct hct

/-- The input of `missing_max_basal_no_clamp`: no `max_basal`, no `max_daily_basal`, BG 300
    and rising, scheduled basal 0.9 U/h. -/
def f12Input : DBInputs :=
  { glucose_status := some { glucose := some 300, delta := some 5, short_avgdelta := some 5, long_avgdelta := some 5, date := some (.fin 1795003200000) }
    currenttemp := some { duration := some 0, rate := some 0, temp := some "absolute" },
    iob_data := some (.single { iob := some 0, activity := some 0 }),
    profile := some { reviewProfile with max_basal := none, max_daily_basal := none },
    autosens_data := some { ratio := some 1 }, meal_data := some {}, clock := { now := 1795003200000 } }

/-- On `f12Input`, oref0 issues 5.9 U/h; the fixed version issues the scheduled basal 0.9 U/h
    for 30 minutes and no microbolus, and says why. With a 2 U/h temp running for 20 more
    minutes, oref0 keeps it ("temp 2 >~ req 0.9U/hr" after the cap), and the fixed version
    cancels it (rate 0, duration 0). -/
theorem f12_example :
    TriggerF12 f12Input ∧ (determineBasal f12Input).rate = some 5.9 ∧
    (determineBasalF12 f12Input).rate = some 0.9 ∧ (determineBasalF12 f12Input).duration = some 30 ∧
    (determineBasalF12 f12Input).units = none ∧
    ((determineBasalF12 f12Input).reason.getD "").endsWith
      "; maxSafeBasal NaN is not a positive number (max_basal or max_daily_basal missing or not a number): rate capped at current basal 0.9U/hr, no SMB" ∧
    (determineBasalF12 { f12Input with currenttemp := some { duration := some 20, rate := some 2, temp := some "absolute" } }).rate = some 0 ∧
    (determineBasalF12 { f12Input with currenttemp := some { duration := some 20, rate := some 2, temp := some "absolute" } }).duration = some 0 := by
  decide +kernel

/-- `f12Input` with BG 60 and falling 3 mg/dL per 5 minutes. -/
def f12LowInput : DBInputs :=
  { f12Input with glucose_status := some { glucose := some 60, delta := some (-3), short_avgdelta := some (-3), long_avgdelta := some (-3), date := some (.fin 1795003200000) } }

/-- **Low-glucose suspend still works with the trigger.** On `f12Input` with BG 60 and
    falling 3 mg/dL per 5 minutes, oref0 and the fixed version both set a zero temp for 30
    minutes. (The first version of the fix issued nothing here.) -/
theorem f12_lgs_example :
    TriggerF12 f12LowInput ∧ (determineBasal f12LowInput).rate = some 0 ∧ (determineBasal f12LowInput).duration = some 30 ∧
    (determineBasalF12 f12LowInput).rate = some 0 ∧ (determineBasalF12 f12LowInput).duration = some 30 ∧
    (determineBasalF12 f12LowInput).units = none := by
  decide +kernel

end LeanAID.Fixed
