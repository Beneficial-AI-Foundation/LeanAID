import LeanAID.Core.DetermineBasal

/-!
# F-12: a missing maximum basal, corrected

**This file is not oref0.** `LeanAID/Core` is the faithful transcription of oref0 0.7.1 and
is not changed. `determineBasalF12` adds one early return to `LeanAID.determineBasal`.

**The oref0 code.** `lib/basal-set-temp.js:11-17` computes
```
    return Math.min(profile.max_basal, max_daily_safety_multiplier * profile.max_daily_basal,
                    current_basal_safety_multiplier * profile.current_basal);
```
With `max_basal` or `max_daily_basal` missing or not a number this is `NaN`, every
`rate > maxSafeBasal` is false, and no cap applies: oref0 issues 5.9 U/h for a scheduled
basal of 0.9 U/h (F-12). `determine_basal` checks only `current_basal`
(`lib/determine-basal/determine-basal.js:138-143`):
```
    if (typeof profile === 'undefined' || typeof profile.current_basal === 'undefined') {
        rT.error ='Error: could not get current basal rate';
        return rT;
    }
    var profile_current_basal = round_basal(profile.current_basal, profile);
    var basal = profile_current_basal;
```

**The fix.** After these lines, if `maxSafeBasal` is not a finite positive number, refuse
to raise the rate and return:
```
    var maxSafeBasal = tempBasalFunctions.getMaxSafeBasal(profile);
    if (!(typeof maxSafeBasal === 'number' && isFinite(maxSafeBasal) && maxSafeBasal > 0)) {
        rT.temp = 'absolute';
        rT.deliverAt = deliverAt;
        rT.reason = "Error: maxSafeBasal " + maxSafeBasal + " is not a positive number; check max_basal, max_daily_basal and current_basal. Not raising the temp basal";
        if (currenttemp.rate > profile.current_basal) {
            rT.reason += ". Canceling temp basal of " + currenttemp.rate + " above current basal " + profile.current_basal;
            rT.duration = 0;
            rT.rate = 0;
        } else if (currenttemp.rate === 0 && currenttemp.duration > 30) {
            rT.reason += ". Shortening " + currenttemp.duration + "m long zero temp to 30m. ";
            rT.duration = 30;
            rT.rate = 0;
        } else {
            rT.reason += ". Temp " + currenttemp.rate + " <= current basal " + profile.current_basal + "U/hr; doing nothing. ";
        }
        return rT;
    }
```
**Why this form.** It is oref0's own handling of input it cannot trust, the CGM-error branch
(lines 198-221): no microbolus, no dosing decision, and the running temp is dealt with in the
same three cases. The one change is the first case. oref0 replaces a high temp by a 30-minute
temp at `round_basal(current_basal)`, which rounding can put above `current_basal`; here the
temp is cancelled (rate 0, duration 0, as oref0 cancels at lines 380-392), so the pump runs
its own schedule. The result has the shape of those lines' result (`temp`, `deliverAt`,
`reason`, `duration`, `rate`). The alternative, continuing with `current_basal` as the cap,
would let `setTempBasal` keep a running temp up to 20 % above the request, so it would not
cancel a high temp. A low temp is not set either: the loop stops dosing until the profile is
fixed, as it does for bad CGM data.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Fixed

open LeanAID JsNum

/-- `maxSafeBasal` is a finite positive number. (`JsNum` has no infinities.) -/
def maxSafeOk (p : Profile) : Bool := getMaxSafeBasal p >ʲ 0

/-- The F-12 early return: no microbolus, no rate above `current_basal`; a running temp
    above `current_basal` is cancelled and a long zero temp shortened to 30 minutes. -/
def refuseF12 (inp : DBInputs) (p : Profile) : Result :=
  match inp.currenttemp with
  | none => typeError "rate"
  | some ct =>
    let msg := "Error: maxSafeBasal " ++ JsFmt.numToString (getMaxSafeBasal p) ++
      " is not a positive number; check max_basal, max_daily_basal and current_basal. Not raising the temp basal"
    let rT : Result :=
      { shape := .lastTemp, temp := some "absolute", deliverAt := some inp.clock.now, reason := some msg }
    if ct.rate.js >ʲ p.current_basal.js then
      let rT := rT.addReason (". Canceling temp basal of " ++ jsStr ct.rate ++ " above current basal " ++
        jsStr p.current_basal)
      { rT with duration := some 0, rate := some 0 }
    else if ct.rate.js =ʲ 0 && ct.duration.js >ʲ 30 then
      { rT.addReason (". Shortening " ++ jsStr ct.duration ++ "m long zero temp to 30m. ")
        with duration := some 30, rate := some 0 }
    else
      rT.addReason (". Temp " ++ jsStr ct.rate ++ " <= current basal " ++ jsStr p.current_basal ++
        "U/hr; doing nothing. ")

/-- `determine_basal` with the F-12 fix. -/
def determineBasalF12 (inp : DBInputs) : Result :=
  match stProfile inp with
  | .ok p => if maxSafeOk p then determineBasal inp else refuseF12 inp p
  | .error r => r

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

end LeanAID.Fixed
