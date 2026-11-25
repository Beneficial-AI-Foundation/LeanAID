import LeanAID.Core.DetermineBasal

/-!
# F-11: an undated glucose reading, corrected

**This file is not oref0.** `LeanAID/Core` is the faithful transcription of oref0 0.7.1 and
is not changed. `determineBasalF11` differs from `LeanAID.determineBasal` in one condition.

**The oref0 code**, `lib/determine-basal/determine-basal.js` in oref0 0.7.1:
```
149    var bgTime = new Date(glucose_status.date);
150    var minAgo = round( (systemTime - bgTime) / 60 / 1000 ,1);
...
187    if (minAgo > 12 || minAgo < -5) { // Dexcom data is too old, or way in the future
...
198    if (bg <= 10 || bg === 38 || noise >= 3 || minAgo > 12 || minAgo < -5 || tooflat ) {
```
A reading without a date (or with a date that is not a number) gives `minAgo = NaN`, both
comparisons are false, and the reading is used however old it is (F-11).

**The fix.** Lines 187 and 198 test the opposite of "fresh" instead of "stale":
```
187    if (!(minAgo <= 12 && minAgo >= -5)) { // Dexcom data is too old, or way in the future
198    if (bg <= 10 || bg === 38 || noise >= 3 || !(minAgo <= 12 && minAgo >= -5) || tooflat ) {
```
For a number `minAgo` this is the same condition. For `NaN` it is true, so an undated reading
takes oref0's own stale-data path: cancel a high temp (replace it by the scheduled basal),
shorten a long zero temp, or do nothing. The reason says that the data is too old and that
it was read "NaNm ago at Invalid Date".

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Fixed

open LeanAID JsNum

/-- Line 187 with the fix: the reading is not known to be fresh. -/
def cgmStaleF11 (g : GluVals) : Bool := !(g.minAgo ≤ʲ 12 && g.minAgo ≥ʲ (-5))

/-- The condition of line 198 with the fix. -/
def cgmErrorF11 (g : GluVals) : Bool := cgmBad g || cgmStaleF11 g || cgmFlat g

/-- `LeanAID.cgmReason` (lines 174-196) with the fix at line 187. -/
def cgmReasonF11 (clock : Clock) (g : GluVals) : Option String :=
  let now : JsNum := .fin clock.now
  if cgmStaleF11 g then
    some ("If current system time " ++ DateFmt.toString now clock.tzOffsetMin clock.tzName ++
      " is correct, then BG data is too old. The last BG data was read " ++ JsFmt.numToString g.minAgo ++
      "m ago at " ++ DateFmt.toString g.bgTime clock.tzOffsetMin clock.tzName)
  else if cgmFlat g then
    if g.gs.last_cal.truthyN && g.gs.last_cal.js <ʲ 3 then some "CGM was just calibrated"
    else some ("CGM data is unchanged (" ++ JsFmt.numToString g.bg ++ "+" ++ jsStr g.gs.delta ++
      ") for 5m w/ " ++ jsStr g.gs.short_avgdelta ++ " mg/dL ~15m change & " ++ jsStr g.gs.long_avgdelta ++
      " mg/dL ~45m change")
  else if cgmBad g then some "CGM is calibrating, in ??? state, or noise is high"
  else none

/-- `LeanAID.cgmResult` (lines 198-221) with the reason of `cgmReasonF11`. The three
    actions are oref0's. -/
def cgmResultF11 (inp : DBInputs) (p : Profile) (g : GluVals) : Result :=
  let basal := profileCurrentBasal p
  match inp.currenttemp with
  | none => typeError "rate"
  | some ct =>
    let rT : Result := { shape := .cgm, reason := cgmReasonF11 inp.clock g }
    if ct.rate.js >ʲ basal then
      { rT.addReason (". Replacing high temp basal of " ++ jsStr ct.rate ++ " with neutral temp of " ++
          JsFmt.numToString basal)
        with deliverAt := some inp.clock.now, temp := some "absolute", duration := some 30, rate := some basal }
    else if ct.rate.js =ʲ 0 && ct.duration.js >ʲ 30 then
      { rT.addReason (". Shortening " ++ jsStr ct.duration ++ "m long zero temp to 30m. ")
        with deliverAt := some inp.clock.now, temp := some "absolute", duration := some 30, rate := some 0 }
    else
      rT.addReason (". Temp " ++ jsStr ct.rate ++ " <= current basal " ++ JsFmt.numToString basal ++
        "U/hr; doing nothing. ")

/-- `LeanAID.stGlucose` (lines 145-221) with the fix. -/
def stGlucoseF11 (inp : DBInputs) (p : Profile) : Except Result GluVals :=
  match inp.glucose_status with
  | none => .error (typeError "date")
  | some gs =>
    let g := gluVals (.fin inp.clock.now) gs
    if cgmErrorF11 g then .error (cgmResultF11 inp p g) else .ok g

/-- `LeanAID.dbPrelude` (lines 128-423) with `stGlucoseF11` in place of `stGlucose`. Every
    other stage is oref0's. -/
def dbPreludeF11 (inp : DBInputs) : Except Result Pre := do
  let p ← stProfile inp
  let g ← stGlucoseF11 inp p
  let mm ← stTargets p
  let target_bg0 := (mm.1 + mm.2) / 2
  let sensitivityRatio := sensitivityRatioOf p inp.autosens_data target_bg0
  let basal := adjustedBasal p sensitivityRatio
  let tgts := adjustTargets p inp.autosens_data g.gs mm.1 mm.2 target_bg0
  let sens := sensOf p inp.autosens_data sensitivityRatio
  let io ← stIob inp
  let ct ← stPumpHistory inp p io.1
  let ev := eventualVals g p sens io.1
  stEventual inp ev
  let meal ← stMeal inp
  return { p, gs := g.gs, ct, iobd := io.1, iobArray := io.2, meal, bg := g.bg, tick := g.tick,
           minDelta := g.minDelta, minAvgDelta := g.minAvgDelta, maxDelta := g.maxDelta, basal,
           target_bg := tgts.2.2, min_bg := tgts.1, max_bg := tgts.2.1, high_bg := p.enableSMB_high_bg_target,
           max_iob := p.max_iob.js, threshold := thresholdOf tgts.1, sens, sensitivityRatio,
           bgi := ev.bgi, deviation := ev.deviation, naive_eventualBG := ev.naive_eventualBG,
           eventualBG := ev.eventualBG,
           expectedDelta := calculateExpectedDelta tgts.2.2 ev.eventualBG ev.bgi }

/-- `determine_basal` with the F-11 fix. -/
def determineBasalF11 (inp : DBInputs) : Result :=
  match dbPreludeF11 inp with
  | .error r => r
  | .ok pre => dbDose (dbPredict inp pre)

/-- **The F-11 trigger**, on the input: the glucose status has no date, or its date is not a
    number (`new Date(glucose_status.date)` is invalid, so `minAgo` is NaN). In `aid-lean`
    the glucose status comes from the newest CGM entry, and its date is missing when that
    entry has no `date`, `display_time` or `dateString` (or none that parses). -/
def triggerF11 (inp : DBInputs) : Bool :=
  match inp.glucose_status with
  | some gs => (DateFmt.timeClip gs.date.js).isNaN
  | none => false

/-- The F-11 trigger as a proposition. -/
def TriggerF11 (inp : DBInputs) : Prop := triggerF11 inp = true

instance (inp : DBInputs) : Decidable (TriggerF11 inp) := inferInstanceAs (Decidable (_ = _))

end LeanAID.Fixed
