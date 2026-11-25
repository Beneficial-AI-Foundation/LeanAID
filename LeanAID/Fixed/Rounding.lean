import LeanAID.Core.DetermineBasal

/-!
# F-04: a rate rounded above `maxSafeBasal`, corrected

**This file is not oref0.** `LeanAID/Core` is the faithful transcription of oref0 0.7.1 and
is not changed. This file adds one step after oref0's `determine_basal`.

**The oref0 code**, `lib/basal-set-temp.js:21-30` in oref0 0.7.1:
```
    var maxSafeBasal = tempBasalFunctions.getMaxSafeBasal(profile);
    var round_basal = require('./round-basal');

    if (rate < 0) {
        rate = 0;
    } else if (rate > maxSafeBasal) {
        rate = maxSafeBasal;
    }

    var suggestedRate = round_basal(rate, profile);
```
`round_basal` rounds to the *nearest* pump step, so when `maxSafeBasal` is not on the pump's
grid the issued rate can be above it: `maxSafeBasal` 0.83 is issued as 0.85 U/h (F-04). The
same happens where `determine_basal` issues a rate without `setTempBasal`: the CGM-error
branch issues `round_basal(current_basal)` (lines 198-206), which is above `maxSafeBasal`
when `current_basal = max_basal = 0.83`.

**The fix.** At the exit of `determine_basal`, if the issued rate is above `maxSafeBasal`,
issue the largest rate on the pump's grid that is at most `maxSafeBasal` instead, and say so
in the reason. Every other result is returned unchanged. In JavaScript
(`scripts/fixes/F-04.patch`) this is a wrapper around `determine_basal` and a function
`round_basal.down` next to `round_basal`:
```
    var rT = determine_basal_oref0(...);
    var maxSafeBasal = tempBasalFunctions.getMaxSafeBasal(profile);
    if (typeof rT.rate !== 'undefined' && rT.rate > maxSafeBasal) {
        var down = round_basal.down(maxSafeBasal, profile);
        rT.reason += "; " + rT.rate + "U/hr is above maxSafeBasal " + maxSafeBasal + ": setting " + down + "U/hr";
        rT.rate = down;
    }
```
The fix acts on the result and not inside `setTempBasal`, so that it changes exactly the
results whose issued rate is above `maxSafeBasal` (`triggerF04`), wherever in
`determine_basal` the rate comes from. A fix inside `setTempBasal` (as in
`private/docs/upstream/oref0/F-04.patch`) would also change the "~ req" comparison with a
running temp, which issues no rate, and would miss the CGM-error branch.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Fixed

open LeanAID JsNum

/-- The pump-step scale `round_basal` uses for a rate `x` (round-basal.js lines 11-40):
    `lowest_rate_scale` (20, or 40 for models ending in "54" or "23") below 1 U/h, 20 below
    10 U/h, 10 above. -/
def basalScale (x : JsNum) (model : Option String) : Rat :=
  if x <ʲ 1 then lowestRateScale model
  else if x <ʲ 10 then 20
  else 10

/-- `round_basal.down(basal, profile)`, not in oref0: the largest rate on the pump's grid
    that is at most `basal`. In JavaScript:
    ```
    var k = Math.floor(basal * scale);
    var down = k / scale;
    if (down > basal) { down = (k - 1) / scale; }   // basal * scale rounded up to an integer
    return down;
    ```
    The second line can exceed `basal` only when the double product `basal * scale` was
    rounded up to an integer; the correction makes the result at most `basal`
    (`roundBasalDown_le`). -/
def roundBasalDown (x : JsNum) (model : Option String) : JsNum :=
  let s : JsNum := .fin (basalScale x model)
  let k := mathFloor (x * s)
  let down := k / s
  if down >ʲ x then (k - 1) / s else down

/-- The F-04 step on a result `r` of `determine_basal` with profile `p`: an issued rate
    above `maxSafeBasal` becomes `roundBasalDown maxSafeBasal`, with a note in the reason.
    Every other result is unchanged. -/
def capRate (p : Profile) (r : Result) : Result :=
  let maxSafeBasal := getMaxSafeBasal p
  match r.rate with
  | some rate =>
    if rate >ʲ maxSafeBasal then
      let down := roundBasalDown maxSafeBasal p.model
      { r.addReason ("; " ++ JsFmt.numToString rate ++ "U/hr is above maxSafeBasal " ++
          JsFmt.numToString maxSafeBasal ++ ": setting " ++ JsFmt.numToString down ++ "U/hr")
        with rate := some down }
    else r
  | none => r

/-- `determine_basal` with the F-04 fix: oref0's result, passed through `capRate`. -/
def determineBasalF04 (inp : DBInputs) : Result :=
  match inp.profile with
  | some p => capRate p (determineBasal inp)
  | none => determineBasal inp

/-- **The F-04 trigger**, stated with oref0's functions: oref0 issues a rate above oref0's
    `maxSafeBasal`. -/
def triggerF04 (inp : DBInputs) : Bool :=
  match inp.profile, (determineBasal inp).rate with
  | some p, some rate => rate >ʲ getMaxSafeBasal p
  | _, _ => false

/-- The F-04 trigger as a proposition. -/
def TriggerF04 (inp : DBInputs) : Prop := triggerF04 inp = true

instance (inp : DBInputs) : Decidable (TriggerF04 inp) := inferInstanceAs (Decidable (_ = _))

end LeanAID.Fixed
