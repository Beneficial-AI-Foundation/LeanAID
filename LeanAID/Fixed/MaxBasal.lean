import LeanAID.Fixed.Rounding

/-!
# F-12: a missing maximum basal, corrected (second version)

**This file is not oref0.** `LeanAID/Core` is the faithful transcription of oref0 0.7.1 and
is not changed. Every function here calls `Core` functions.

**The oref0 code.** `lib/basal-set-temp.js:11-17` computes
```
    return Math.min(profile.max_basal, max_daily_safety_multiplier * profile.max_daily_basal,
                    current_basal_safety_multiplier * profile.current_basal);
```
With `max_basal` or `max_daily_basal` missing or not a number this is `NaN`, every
`rate > maxSafeBasal` is false, and no cap applies: oref0 issues 5.9 U/h for a scheduled
basal of 0.9 U/h (F-12).

**The fix.** When the trigger holds (the profile has `current_basal` and `maxSafeBasal` is not
a positive number), run oref0's normal decision with three changes:

1. **The cap is the scheduled basal.** oref0 runs on `capProfile p`: the profile with
   `max_basal` and `max_daily_basal` set to `current_basal` and both safety multipliers 1,
   so that `getMaxSafeBasal` is `min(cb, 1·cb, 1·cb) = cb` (for a double `cb`). `getMaxSafeBasal`
   is the only reader of these four fields in `determine_basal` and `setTempBasal`, so
   oref0 uses `current_basal` wherever it used `maxSafeBasal`. The F-04 step
   (`Fixed/Rounding.lean`, `capRate`) with the same profile then replaces a rate rounded
   above `current_basal` by the largest grid rate below it.
2. **No microbolus.** oref0 runs with `microBolusAllowed = false`, its own path when the
   pump loop does not allow SMB (`determine-basal.js:60-62`).
3. **A running temp above `current_basal` is not left running** (`postF12`). Wherever oref0
   issues no rate and keeps a running temp (the "~ req" comparisons, the 20 % window of
   `setTempBasal`, the CGM-error branch for a temp between `current_basal` and its rounding),
   and that temp's rate is above `current_basal`, it is cancelled (rate 0, duration 0, so the
   pump runs its schedule), as oref0 itself cancels at lines 380-392.
4. The reason ends with a note that `maxSafeBasal` is not a positive number and the rate is
   capped at the scheduled basal (and, for 3, that the temp is cancelled).

Everything else, including the low-glucose suspend, the CGM-error and stale-data paths and
the predictions, is oref0's. An error result (`{error}`) is returned unchanged.

The first version (commit `eccda9f`) returned early without any dosing decision; it never
set a zero temp at low glucose. See `docs/FIXED.md`, "F-12".

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Fixed

open LeanAID JsNum

/-- `maxSafeBasal` is a finite positive number. (`JsNum` has no infinities.) -/
def maxSafeOk (p : Profile) : Bool := getMaxSafeBasal p >ʲ 0

/-- **The F-12 trigger**, on the input: a profile with `current_basal` (so oref0 gets past
    lines 138-141) whose `maxSafeBasal = min(max_basal, 3 × max_daily_basal,
    4 × current_basal)` (with the profile's multipliers) is not a positive number. This
    holds when `max_basal` or `max_daily_basal` is missing or not a number
    (`triggerF12_of_missing`), and also when one of the three is zero or negative. -/
def triggerF12 (inp : DBInputs) : Bool :=
  match inp.profile with
  | some p => p.current_basal.isSome && !maxSafeOk p
  | none => false

/-- The F-12 trigger as a proposition. -/
def TriggerF12 (inp : DBInputs) : Prop := triggerF12 inp = true

instance (inp : DBInputs) : Decidable (TriggerF12 inp) := inferInstanceAs (Decidable (_ = _))

/-- The profile whose `maxSafeBasal` is `current_basal`: `max_basal` and `max_daily_basal`
    are `current_basal`, both safety multipliers are 1. Every other field is `p`'s. -/
def capProfile (p : Profile) : Profile :=
  { p with max_basal := p.current_basal, max_daily_basal := p.current_basal,
           max_daily_safety_multiplier := some 1, current_basal_safety_multiplier := some 1 }

/-- The input oref0 runs on under the F-12 trigger: the capped profile, no microbolus. -/
def inputF12 (inp : DBInputs) (p : Profile) : DBInputs :=
  { inp with profile := some (capProfile p), microBolusAllowed := false }

/-- The note appended to the reason under the F-12 trigger. -/
def noteF12 (p : Profile) : String :=
  "; maxSafeBasal " ++ JsFmt.numToString (getMaxSafeBasal p) ++
    " is not a positive number (max_basal or max_daily_basal missing or not a number): rate capped at current basal " ++
    jsStr p.current_basal ++ "U/hr, no SMB"

/-- Point 3 and 4 of the fix, applied to oref0's result `U` on `inputF12 inp p`: append the
    note; if no rate is issued and the running temp is above `current_basal`, cancel it. An
    error result is returned unchanged. -/
def postF12 (inp : DBInputs) (p : Profile) (U : Result) : Result :=
  if U.shape = .error then U else
  let U : Result := match U.reason with
    | some r => { U with reason := some (r ++ noteF12 p) }
    | none => U
  match U.rate, inp.currenttemp with
  | none, some ct =>
    if ct.rate.js >ʲ p.current_basal.js then
      let msg := "; canceling temp basal of " ++ jsStr ct.rate ++ " above current basal " ++ jsStr p.current_basal
      { U with reason := U.reason.map (· ++ msg), deliverAt := (U.deliverAt <|> some inp.clock.now),
               temp := (U.temp <|> some "absolute"), duration := some 0, rate := some 0 }
    else U
  | _, _ => U

/-- `determine_basal` with the F-12 fix: under the trigger, oref0 on `inputF12 inp p`, then
    the F-04 step with the capped profile (point 1), then `postF12`. Without the trigger,
    oref0. -/
def determineBasalF12 (inp : DBInputs) : Result :=
  match inp.profile with
  | some p => if triggerF12 inp then postF12 inp p (determineBasalF04 (inputF12 inp p)) else determineBasal inp
  | none => determineBasal inp

end LeanAID.Fixed
