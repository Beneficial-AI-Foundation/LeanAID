/-
  LeanAID.Core.DetermineBasal — transcription of
  `lib/determine-basal/determine-basal.js` (oref0 0.7.1, 1192 lines).

  The JavaScript function `determine_basal` (lines 128-1190) is one long function
  with early returns. It is transcribed as three functions, in source order:

  * `dbPrelude`  lines 128-423: input checks, the CGM-error branch, targets,
                 sensitivity, the pump-history checks, BGI, deviation, eventualBG.
                 Returns early (`Except.error`) exactly where the JavaScript does.
  * `dbPredict`  lines 428-903: builds `rT`, runs the prediction loop and computes
                 minPredBG, minGuardBG, carbsReq and the SMB enable flag. No early
                 returns in this range.
  * `dbDose`     lines 905-1188: the dosing decision.

  JavaScript quirks that are reproduced on purpose are marked QUIRK and listed in
  `docs/FINDINGS.md`. Console logging (`console.error`, `process.stderr.write`) has
  no effect on the result and is omitted.
-/
import LeanAID.Core.BasalSetTemp
import LeanAID.Core.DateFmt

namespace LeanAID

open JsNum

/-- `round(value, digits)` from determine-basal.js lines 21-26 (`JsNum.round`). -/
@[reducible] def rnd (value : JsNum) (digits : Nat := 0) : JsNum := JsNum.round value digits

/-- `calculate_expected_delta(target_bg, eventual_bg, bgi)`, lines 31-36. -/
def calculateExpectedDelta (target_bg eventual_bg bgi : JsNum) : JsNum :=
  let five_min_blocks : JsNum := 24   -- (2 * 60) / 5
  let target_delta := target_bg - eventual_bg
  rnd (bgi + target_delta / five_min_blocks) 1

/-- `convert_bg(value, profile)`, lines 39-49. -/
def convertBg (value : JsNum) (p : Profile) : NumOrStr :=
  if p.out_units == some "mmol/L" then .str (JsFmt.toFixed (rnd (value / 18) 1) 1)
  else .num (mathRound value)

/-- `convert_bg(...)` as it prints inside a string concatenation. -/
def convertBgS (value : JsNum) (p : Profile) : String := (convertBg value p).toString

/-- `enable_smb(profile, microBolusAllowed, meal_data, bg, target_bg, high_bg)`,
    lines 51-126. `high_bg` is `none` when `profile.enableSMB_high_bg_target` is
    undefined. -/
def enableSmb (p : Profile) (microBolusAllowed : Bool) (meal : MealData)
    (bg target_bg : JsNum) (high_bg : Option JsNum) : Bool :=
  if !microBolusAllowed then false
  else if !p.allowSMB_with_high_temptarget.truthy && p.temptargetSet.truthy && target_bg >ʲ 100 then false
  else if meal.bwFound == some true && p.A52_risk_enable == some false then false
  else if p.enableSMB_always == some true then true
  else if p.enableSMB_with_COB == some true && meal.mealCOB.truthyN then true
  else if p.enableSMB_after_carbs == some true && meal.carbs.truthyN then true
  else if p.enableSMB_with_temptarget == some true && (p.temptargetSet.truthy && target_bg <ʲ 100) then true
  -- `high_bg !== null && bg >= high_bg`; an undefined `high_bg` makes `bg >= high_bg` false
  else if p.enableSMB_high_bg == some true && bg ≥ʲ high_bg.js then true
  else false

/-- All inputs of `determine_basal(glucose_status, currenttemp, iob_data, profile,
    autosens_data, meal_data, tempBasalFunctions, microBolusAllowed,
    reservoir_data, currentTime)`. `none` is `undefined`. The JavaScript reads the
    clock with `new Date()` when `currentTime` is absent; here the time is always
    an explicit input (`clock.now`). -/
structure DBInputs where
  glucose_status : Option GlucoseStatus
  currenttemp : Option CurrentTemp
  iob_data : Option IobInput
  profile : Option Profile
  autosens_data : Option Autosens := none
  meal_data : Option MealData := none
  microBolusAllowed : Bool := false
  reservoir_data : Reservoir := .undef
  clock : Clock
  deriving Repr, Inhabited

/-- The JavaScript would throw a `TypeError` (reading a property of `undefined`).
    The CLI then exits with a stack trace and no suggestion. -/
def typeError (what : String) : Result :=
  Result.err ("TypeError: Cannot read properties of undefined (reading '" ++ what ++ "')")

/-- Values computed by lines 128-423 and needed later. -/
structure Pre where
  p : Profile
  gs : GlucoseStatus
  ct : CurrentTemp
  /-- `iob_data` after line 357 (the first element of the array, or the object) -/
  iobd : IobTick
  /-- `iobArray`: the ticks the prediction loop iterates over; `none` when
      `iob_data` was a single object, on which `forEach` throws (QUIRK Q1). -/
  iobArray : Option (List IobTick)
  meal : MealData
  bg : JsNum
  tick : NumOrStr
  minDelta : JsNum
  minAvgDelta : JsNum
  maxDelta : JsNum
  basal : JsNum
  target_bg : JsNum
  min_bg : JsNum
  max_bg : JsNum
  high_bg : Option JsNum
  max_iob : JsNum
  threshold : JsNum
  sens : JsNum
  sensitivityRatio : Option JsNum
  bgi : JsNum
  deviation : JsNum
  naive_eventualBG : JsNum
  eventualBG : JsNum
  expectedDelta : JsNum
  deriving Repr, Inhabited

/-! The prelude, lines 128-423, is split into stages in source order. Each stage
    either returns early (`Except.error r`: `determine_basal` returns `r`) or passes
    its values on. Pure computations between the exits are separate functions. -/

/-- Lines 138-143: a profile with `current_basal` is required. -/
def stProfile (inp : DBInputs) : Except Result Profile :=
  match inp.profile with
  | none => .error (Result.err "Error: could not get current basal rate")
  | some p => if p.current_basal.isNone then .error (Result.err "Error: could not get current basal rate") else .ok p

/-- `profile_current_basal = round_basal(profile.current_basal, profile)` (line 142). -/
def profileCurrentBasal (p : Profile) : JsNum := roundBasal p.current_basal.js p.model

/-- Values computed from `glucose_status`, lines 145-166. -/
structure GluVals where
  gs : GlucoseStatus
  bgTime : JsNum
  minAgo : JsNum
  bg : JsNum
  noise : JsNum
  tick : NumOrStr
  minDelta : JsNum
  minAvgDelta : JsNum
  maxDelta : JsNum
  deriving Repr, Inhabited

/-- Lines 145-166. -/
def gluVals (now : JsNum) (gs : GlucoseStatus) : GluVals :=
  -- lines 149-150: `new Date(glucose_status.date)`; a missing date gives NaN (QUIRK Q2)
  let bgTime := DateFmt.timeClip gs.date.js
  { gs, bgTime,
    minAgo := rnd ((now - bgTime) / 60 / 1000) 1,
    bg := gs.glucose.js,
    noise := gs.noise.js,
    tick := if gs.delta.js >ʲ (-0.5) then .str ("+" ++ JsFmt.numToString (rnd gs.delta.js 0))
            else .num (rnd gs.delta.js 0),
    minDelta := JsNum.min gs.delta.js gs.short_avgdelta.js,
    minAvgDelta := JsNum.min gs.short_avgdelta.js gs.long_avgdelta.js,
    maxDelta := JsNum.max3 gs.delta.js gs.short_avgdelta.js gs.long_avgdelta.js }

/-- Line 174: an error code or high noise (`bg <= 10 || bg === 38 || noise >= 3`). -/
def cgmBad (g : GluVals) : Bool := g.bg ≤ʲ 10 || g.bg =ʲ 38 || g.noise ≥ʲ 3

/-- Line 187: data too old or from the future. -/
def cgmStale (g : GluVals) : Bool := g.minAgo >ʲ 12 || g.minAgo <ʲ (-5)

/-- Lines 177-185: flat CGM data (unless the device is "fakecgm"). -/
def cgmFlat (g : GluVals) : Bool :=
  g.bg >ʲ 60 && g.gs.delta.js =ʲ 0 && g.gs.short_avgdelta.js >ʲ (-1) && g.gs.short_avgdelta.js <ʲ 1 &&
    g.gs.long_avgdelta.js >ʲ (-1) && g.gs.long_avgdelta.js <ʲ 1 && g.gs.device != some "fakecgm"

/-- The condition of line 198. -/
def cgmError (g : GluVals) : Bool := cgmBad g || cgmStale g || cgmFlat g

/-- The reason set by lines 174-196. -/
def cgmReason (clock : Clock) (g : GluVals) : Option String :=
  let now : JsNum := .fin clock.now
  if cgmStale g then
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

/-- Lines 198-221: what `determine_basal` returns when the CGM data is unusable:
    replace a high temp by the basal rate, shorten a long zero temp, or do nothing.
    `basal` here is `profile_current_basal` (no sensitivity adjustment yet). -/
def cgmResult (inp : DBInputs) (p : Profile) (g : GluVals) : Result :=
  let basal := profileCurrentBasal p
  match inp.currenttemp with
  | none => typeError "rate"
  | some ct =>
    let rT : Result := { shape := .cgm, reason := cgmReason inp.clock g }
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

/-- Lines 145-221. -/
def stGlucose (inp : DBInputs) (p : Profile) : Except Result GluVals :=
  match inp.glucose_status with
  | none => .error (typeError "date")
  | some gs =>
    let g := gluVals (.fin inp.clock.now) gs
    if cgmError g then .error (cgmResult inp p g) else .ok g

/-- Lines 226-247: `min_bg` and `max_bg` are required. -/
def stTargets (p : Profile) : Except Result (JsNum × JsNum) :=
  match p.min_bg, p.max_bg with
  | some mn, some mx => .ok (mn, mx)
  | _, _ => .error (Result.err "Error: could not determine target_bg. ")

/-- Lines 250-281: `sensitivityRatio`, from a temp target or from autosens. -/
def sensitivityRatioOf (p : Profile) (autosens : Option Autosens) (target_bg : JsNum) : Option JsNum :=
  let high_temptarget_raises_sensitivity := p.exercise_mode.truthy || p.high_temptarget_raises_sensitivity.truthy
  let normalTarget : JsNum := 100
  let halfBasalTarget : JsNum := if p.half_basal_exercise_target.truthyN then p.half_basal_exercise_target.js else 160
  if (high_temptarget_raises_sensitivity && p.temptargetSet.truthy && target_bg >ʲ normalTarget) ||
     (p.low_temptarget_lowers_sensitivity.truthy && p.temptargetSet.truthy && target_bg <ʲ normalTarget) then
    let c := halfBasalTarget - normalTarget
    let sr := if c * (c + target_bg - normalTarget) ≤ʲ 0 then p.autosens_max.js
      else c / (c + target_bg - normalTarget)
    some (rnd (JsNum.min sr p.autosens_max.js) 2)
  else match autosens with
    | some a => a.ratio
    | none => none

/-- Lines 142-143 and 282-290: the basal rate after the sensitivity adjustment. -/
def adjustedBasal (p : Profile) (sensitivityRatio : Option JsNum) : JsNum :=
  if sensitivityRatio.truthyN then roundBasal (p.current_basal.js * sensitivityRatio.js) p.model
  else profileCurrentBasal p

/-- Lines 294-326: targets adjusted for autosens (no temp target) and for noisy CGM data. -/
def adjustTargets (p : Profile) (autosens : Option Autosens) (gs : GlucoseStatus)
    (min_bg0 max_bg0 target_bg0 : JsNum) : JsNum × JsNum × JsNum :=
  let (min_bg1, max_bg1, target_bg1) :=
    if p.temptargetSet.truthy then (min_bg0, max_bg0, target_bg0)
    else match autosens with
      | some a =>
        if (p.sensitivity_raises_target.truthy && a.ratio.js <ʲ 1) || (p.resistance_lowers_target.truthy && a.ratio.js >ʲ 1) then
          let mn := rnd ((min_bg0 - 60) / a.ratio.js) + 60
          let mx := rnd ((max_bg0 - 60) / a.ratio.js) + 60
          let nt := JsNum.max 80 (rnd ((target_bg0 - 60) / a.ratio.js) + 60)
          (mn, mx, nt)
        else (min_bg0, max_bg0, target_bg0)
      | none => (min_bg0, max_bg0, target_bg0)
  if gs.noise.js ≥ʲ 2 then
    let m := JsNum.max 1.1 p.noisyCGMTargetMultiplier.js
    (rnd (JsNum.min 200 (min_bg1 * m)), rnd (JsNum.min 200 (max_bg1 * m)), rnd (JsNum.min 200 (target_bg1 * m)))
  else (min_bg1, max_bg1, target_bg1)

/-- Line 329: `threshold = min_bg - 0.5*(min_bg-40)`. -/
def thresholdOf (min_bg : JsNum) : JsNum := min_bg - 0.5 * (min_bg - 40)

/-- Lines 336-347: ISF adjusted for sensitivity. -/
def sensOf (p : Profile) (autosens : Option Autosens) (sensitivityRatio : Option JsNum) : JsNum :=
  match autosens with
  | some _ => rnd (p.sens.js / sensitivityRatio.js) 1
  | none => p.sens.js

/-- Lines 350-364: `iob_data`, its first element, and the array for the predictions. -/
def stIob (inp : DBInputs) : Except Result (IobTick × Option (List IobTick)) :=
  match inp.iob_data with
  | none => .error (Result.err "Error: iob_data undefined. ")
  | some iobIn =>
    let (iobd?, iobArray) : Option IobTick × Option (List IobTick) :=
      match iobIn with
      | .single t => (some t, none)
      | .array ts => match ts with
        | t :: _ :: _ => (some t, some ts)
        | _ => (none, some ts)            -- arrays of length ≤ 1 have no `.activity`
    match iobd? with
    | none => .error (Result.err "Error: iob_data missing some property. ")
    | some iobd =>
      if iobd.activity.isNone || iobd.iob.isNone then .error (Result.err "Error: iob_data missing some property. ")
      else .ok (iobd, iobArray)

/-- Lines 369-392: `currenttemp` is required; cancel the temp if it disagrees with
    pump history. -/
def stPumpHistory (inp : DBInputs) (p : Profile) (iobd : IobTick) : Except Result CurrentTemp :=
  let now : JsNum := .fin inp.clock.now
  let lastTempAge : JsNum := match iobd.lastTemp with
    | some lt => rnd ((now - lt.date.js) / 60000)
    | none => 0
  match inp.currenttemp with
  | none => .error (typeError "duration")
  | some ct =>
    let rT : Result := { shape := .lastTemp, temp := some "absolute", deliverAt := some inp.clock.now }
    match iobd.lastTemp with
    | none => .ok ct
    | some lt =>
      if inp.microBolusAllowed && optSne ct.rate lt.rate && lastTempAge >ʲ 10 && ct.duration.truthyN then
        .error (setTempBasal 0 0 p (rT.setReason ("Warning: currenttemp rate " ++ jsStr ct.rate ++ " != lastTemp rate " ++
          jsStr lt.rate ++ " from pumphistory; canceling temp")) (some ct))
      else if ct.duration.js >ʲ 0 && (lastTempAge - lt.duration.js) >ʲ 5 && lastTempAge >ʲ 10 then
        .error (setTempBasal 0 0 p (rT.setReason ("Warning: currenttemp running but lastTemp from pumphistory ended " ++
          JsFmt.numToString (lastTempAge - lt.duration.js) ++ "m ago; canceling temp")) (some ct))
      else .ok ct

/-- Values of lines 398-417. -/
structure EvVals where
  bgi : JsNum
  deviation : JsNum
  naive_eventualBG : JsNum
  eventualBG : JsNum
  deriving Repr, Inhabited

/-- Lines 398-417: BGI, deviation, naive and eventual BG. -/
def eventualVals (g : GluVals) (p : Profile) (sens : JsNum) (iobd : IobTick) : EvVals :=
  let bgi := rnd (-iobd.activity.js * sens * 5) 2
  let dev1 := rnd (6 * (g.minDelta - bgi))
  let deviation :=
    if dev1 <ʲ 0 then
      let dev2 := rnd (6 * (g.minAvgDelta - bgi))
      if dev2 <ʲ 0 then rnd (6 * (g.gs.long_avgdelta.js - bgi)) else dev2
    else dev1
  let naive_eventualBG :=
    if iobd.iob.js >ʲ 0 then rnd (g.bg - iobd.iob.js * sens)
    else rnd (g.bg - iobd.iob.js * JsNum.min sens p.sens.js)
  { bgi, deviation, naive_eventualBG, eventualBG := naive_eventualBG + deviation }

/-- Lines 419-422. `rT` already holds `temp` and `deliverAt` (lines 378-379). -/
def stEventual (inp : DBInputs) (ev : EvVals) : Except Result Unit :=
  if ev.eventualBG.isNaN then
    .error { Result.err "Error: could not calculate eventualBG. " with
             temp := some "absolute", deliverAt := some inp.clock.now }
  else .ok ()

/-- `meal_data` is read at line 451 (`enable_smb`); `undefined` throws there. -/
def stMeal (inp : DBInputs) : Except Result MealData :=
  match inp.meal_data with
  | none => .error (typeError "bwFound")
  | some m => .ok m

/-- Lines 128-423 of `determine_basal`. -/
def dbPrelude (inp : DBInputs) : Except Result Pre := do
  let p ← stProfile inp
  let g ← stGlucose inp p
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

/-! ### Predictions (lines 439-786) -/

/-- Constants of the prediction loop that do not change between iterations. -/
structure PredParams where
  sens : JsNum
  ci : JsNum
  uci : JsNum
  cid : JsNum
  remainingCATime : JsNum
  remainingCIpeak : JsNum
  slopeFromDeviations : JsNum
  enableUAM : Bool
  deriving Repr, Inhabited

/-- The mutable variables of the prediction loop (lines 442-572). -/
structure PredState where
  IOBpredBGs : Array JsNum
  COBpredBGs : Array JsNum
  UAMpredBGs : Array JsNum
  ZTpredBGs : Array JsNum
  minIOBPredBG : JsNum := 999
  minCOBPredBG : JsNum := 999
  minUAMPredBG : JsNum := 999
  minCOBGuardBG : JsNum := 999
  minUAMGuardBG : JsNum := 999
  minIOBGuardBG : JsNum := 999
  minZTGuardBG : JsNum := 999
  IOBpredBG : JsNum
  maxIOBPredBG : JsNum
  maxCOBPredBG : JsNum
  maxUAMPredBG : JsNum
  /-- QUIRK Q3: `COBpredBG` and `UAMpredBG` are implicit globals in the JavaScript
      (assigned without `var`). They are only read after the loop when it ran at
      least one full iteration in the same call, so the value from the last
      iteration is what matters; before any iteration they are unread. -/
  COBpredBG : JsNum := .nan
  UAMpredBG : JsNum := .nan
  deriving Repr, Inhabited

/-- `arr[arr.length - 1]` for the prediction arrays, which are never empty. -/
def lastOf (a : Array JsNum) : JsNum := a.back?.getD .nan

def lenJ (a : Array JsNum) : JsNum := .fin a.size

/-- One iteration of `iobArray.forEach(function(iobTick) {...})`, lines 574-638.
    Returns `none` when the iteration throws (missing `iobWithZeroTemp`, line 577),
    which ends the loop: the exception is caught at line 642. -/
def predStep (k : PredParams) (s : PredState) (iobTick : IobTick) : Option PredState := do
  let predBGI := rnd (-iobTick.activity.js * k.sens * 5) 2
  let ztAct ← iobTick.iobWithZeroTemp
  let predZTBGI := rnd (-ztAct.js * k.sens * 5) 2
  let predDev := k.ci * (1 - JsNum.min 1 (lenJ s.IOBpredBGs / (60 / 5)))
  let IOBpredBG := lastOf s.IOBpredBGs + predBGI + predDev
  let ZTpredBG := lastOf s.ZTpredBGs + predZTBGI
  let predCI := JsNum.max 0 (JsNum.max 0 k.ci * (1 - lenJ s.COBpredBGs / JsNum.max (k.cid * 2) 1))
  let intervals := JsNum.min (lenJ s.COBpredBGs) (k.remainingCATime * 12 - lenJ s.COBpredBGs)
  let remainingCI := JsNum.max 0 (intervals / (k.remainingCATime / 2 * 12) * k.remainingCIpeak)
  let COBpredBG := lastOf s.COBpredBGs + predBGI + JsNum.min 0 predDev + predCI + remainingCI
  let predUCIslope := JsNum.max 0 (k.uci + lenJ s.UAMpredBGs * k.slopeFromDeviations)
  let predUCImax := JsNum.max 0 (k.uci * (1 - lenJ s.UAMpredBGs / JsNum.max (3 * 60 / 5) 1))
  let predUCI := JsNum.min predUCIslope predUCImax
  let UAMpredBG := lastOf s.UAMpredBGs + predBGI + JsNum.min 0 predDev + predUCI
  -- lines 613-616: truncate at 4 hours
  let IOBs := if s.IOBpredBGs.size < 48 then s.IOBpredBGs.push IOBpredBG else s.IOBpredBGs
  let COBs := if s.COBpredBGs.size < 48 then s.COBpredBGs.push COBpredBG else s.COBpredBGs
  let UAMs := if s.UAMpredBGs.size < 48 then s.UAMpredBGs.push UAMpredBG else s.UAMpredBGs
  let ZTs := if s.ZTpredBGs.size < 48 then s.ZTpredBGs.push ZTpredBG else s.ZTpredBGs
  -- lines 618-621
  let minCOBGuardBG := if COBpredBG <ʲ s.minCOBGuardBG then rnd COBpredBG else s.minCOBGuardBG
  let minUAMGuardBG := if UAMpredBG <ʲ s.minUAMGuardBG then rnd UAMpredBG else s.minUAMGuardBG
  let minIOBGuardBG := if IOBpredBG <ʲ s.minIOBGuardBG then rnd IOBpredBG else s.minIOBGuardBG
  let minZTGuardBG := if ZTpredBG <ʲ s.minZTGuardBG then rnd ZTpredBG else s.minZTGuardBG
  -- lines 625-638 (insulinPeak5m = 90/60*12 = 18)
  let insulinPeak5m : JsNum := 18
  let minIOBPredBG := if lenJ IOBs >ʲ insulinPeak5m && IOBpredBG <ʲ s.minIOBPredBG then rnd IOBpredBG else s.minIOBPredBG
  let maxIOBPredBG := if IOBpredBG >ʲ s.maxIOBPredBG then IOBpredBG else s.maxIOBPredBG
  let cobActive := k.cid.truthy || k.remainingCIpeak >ʲ 0
  let minCOBPredBG := if cobActive && lenJ COBs >ʲ insulinPeak5m && COBpredBG <ʲ s.minCOBPredBG then rnd COBpredBG else s.minCOBPredBG
  -- QUIRK Q4: line 636 compares COBpredBG with maxIOBPredBG (not maxCOBPredBG)
  let maxCOBPredBG := if cobActive && COBpredBG >ʲ maxIOBPredBG then COBpredBG else s.maxCOBPredBG
  let minUAMPredBG := if k.enableUAM && lenJ UAMs >ʲ 12 && UAMpredBG <ʲ s.minUAMPredBG then rnd UAMpredBG else s.minUAMPredBG
  let maxUAMPredBG := if k.enableUAM && UAMpredBG >ʲ maxIOBPredBG then UAMpredBG else s.maxUAMPredBG
  return { IOBpredBGs := IOBs, COBpredBGs := COBs, UAMpredBGs := UAMs, ZTpredBGs := ZTs,
           minIOBPredBG, minCOBPredBG, minUAMPredBG, minCOBGuardBG, minUAMGuardBG, minIOBGuardBG,
           minZTGuardBG, IOBpredBG, maxIOBPredBG, maxCOBPredBG, maxUAMPredBG, COBpredBG, UAMpredBG }

/-- The `forEach` loop with its `try/catch` (lines 573-644): iterate until the end
    or until an iteration throws. -/
def predLoop (k : PredParams) (s : PredState) : List IobTick → PredState
  | [] => s
  | t :: ts => match predStep k s t with
    | some s' => predLoop k s' ts
    | none => s

/-- Clamp every prediction to [39, 401] and round (lines 650-652). -/
def clampPreds (a : Array JsNum) : Array JsNum := a.map fun p => rnd (JsNum.min 401 (JsNum.max 39 p))

/-- Drop trailing repeated values, keeping at least `keep + 1` entries
    (lines 653-656: `for (i = len-1; i > keep; i--) if (a[i-1] !== a[i]) break; else a.pop()`). -/
def trimFlat (keep : Nat) (a : Array JsNum) : Array JsNum :=
  go a.size a
where
  go : Nat → Array JsNum → Array JsNum
    | 0, a => a
    | fuel + 1, a =>
      let i := a.size - 1
      if a.size ≥ 1 && i > keep then
        if a[i - 1]! ≠ʲ a[i]! then a else go fuel a.pop
      else a

/-- Lines 662-666: drop trailing ZT predictions while they rise above target. -/
def trimZT (target_bg : JsNum) (a : Array JsNum) : Array JsNum :=
  go a.size a
where
  go : Nat → Array JsNum → Array JsNum
    | 0, a => a
    | fuel + 1, a =>
      let i := a.size - 1
      if a.size ≥ 1 && i > 6 then
        if a[i - 1]! ≥ʲ a[i]! || a[i]! ≤ʲ target_bg then a else go fuel a.pop
      else a

/-- Index of the first prediction below `limit`, times 5 (minutes), or 240
    (lines 828-860). -/
def minutesAbove (a : Array JsNum) (limit : JsNum) : JsNum :=
  match a.toList.findIdx? (fun x => x <ʲ limit) with
  | some i => .fin (5 * i)
  | none => 240

/-- Everything the dosing decision (lines 905-1188) reads. -/
structure Ctx extends Pre where
  rT : Result
  enableSMB : Bool
  minGuardBG : JsNum
  minPredBG : JsNum
  minIOBPredBG : JsNum
  /-- `eventualBG` after the COB/UAM adjustment of lines 669-699 -/
  eventualBG' : JsNum
  carbsReq : JsNum
  microBolusAllowed : Bool
  clock : Clock
  deriving Repr, Inhabited

/-- Lines 428-903 of `determine_basal`. -/
def dbPredict (inp : DBInputs) (pre : Pre) : Ctx :=
  let p := pre.p
  let meal := pre.meal
  let bg := pre.bg
  let sens := pre.sens
  let now : JsNum := .fin inp.clock.now
  -- lines 428-437
  let rT : Result :=
    { shape := .main, temp := some "absolute", bg := pre.gs.glucose, tick := some pre.tick,
      eventualBG := some pre.eventualBG, insulinReq := some 0, reservoir := inp.reservoir_data,
      deliverAt := some inp.clock.now, sensitivityRatio := pre.sensitivityRatio }
  -- lines 451-461
  let enableSMB0 := enableSmb p inp.microBolusAllowed meal bg pre.target_bg pre.high_bg
  let enableUAM := p.enableUAM.truthy
  -- lines 466-486
  let ci0 := rnd (pre.minDelta - pre.bgi) 1
  let uci := rnd (pre.minDelta - pre.bgi) 1
  let csf := sens / p.carb_ratio.js
  let maxCarbAbsorptionRate : JsNum := 30
  let maxCI := rnd (maxCarbAbsorptionRate * csf * 5 / 60) 1
  let ci := if ci0 >ʲ maxCI then maxCI else ci0
  -- lines 487-509
  let remainingCATimeMin0 : JsNum := if pre.sensitivityRatio.truthyN then 3 / pre.sensitivityRatio.js else 3
  let assumedCarbAbsorptionRate : JsNum := 20
  let remainingCATime :=
    if meal.carbs.truthyN then
      let rmin := JsNum.max remainingCATimeMin0 (meal.mealCOB.js / assumedCarbAbsorptionRate)
      -- QUIRK Q5: a missing lastCarbTime makes lastCarbAge, and so remainingCATime, NaN
      let lastCarbAge := rnd ((now - meal.lastCarbTime.js) / 60000)
      rnd (rmin + 1.5 * lastCarbAge / 60) 1
    else remainingCATimeMin0
  -- lines 513-527
  let totalCI := JsNum.max 0 (ci / 5 * 60 * remainingCATime / 2)
  let totalCA := totalCI / csf
  let remainingCarbsCap : JsNum := if p.remainingCarbsCap.truthyN then JsNum.min 90 p.remainingCarbsCap.js else 90
  let remainingCarbsFraction : JsNum := if p.remainingCarbsFraction.truthyN then JsNum.min 1 p.remainingCarbsFraction.js else 1
  let remainingCarbsIgnore := 1 - remainingCarbsFraction
  let remainingCarbs := JsNum.min remainingCarbsCap
    (JsNum.max 0 (meal.mealCOB.js - totalCA - meal.carbs.js * remainingCarbsIgnore))
  let remainingCIpeak := remainingCarbs * csf * 5 / 60 / (remainingCATime / 2)
  -- lines 531-535
  let slopeFromMaxDeviation := rnd meal.slopeFromMaxDeviation.js 2
  let slopeFromMinDeviation := rnd meal.slopeFromMinDeviation.js 2
  let slopeFromDeviations := JsNum.min slopeFromMaxDeviation (-slopeFromMinDeviation / 3)
  -- lines 541-546
  let cid := if ci =ʲ 0 then 0
    else JsNum.min (remainingCATime * 60 / 5 / 2) (JsNum.max 0 (meal.mealCOB.js * csf / ci))
  -- lines 550-644: the prediction loop
  let k : PredParams := { sens, ci, uci, cid, remainingCATime, remainingCIpeak, slopeFromDeviations, enableUAM }
  let s0 : PredState :=
    { IOBpredBGs := #[bg], COBpredBGs := #[bg], UAMpredBGs := #[bg], ZTpredBGs := #[bg],
      IOBpredBG := pre.eventualBG, maxIOBPredBG := bg, maxCOBPredBG := bg, maxUAMPredBG := bg }
  -- QUIRK Q1: `forEach` on a single IOB object throws before the first iteration
  let s := match pre.iobArray with
    | some ticks => predLoop k s0 ticks
    | none => s0
  -- lines 649-699
  let IOBpredBGs := trimFlat 12 (clampPreds s.IOBpredBGs)
  let lastIOBpredBG := rnd (lastOf IOBpredBGs)
  let ZTpredBGs := trimZT pre.target_bg (clampPreds s.ZTpredBGs)
  let cobPreds := meal.mealCOB.js >ʲ 0 && (ci >ʲ 0 || remainingCIpeak >ʲ 0)
  let COBpredBGs := if cobPreds then trimFlat 12 (clampPreds s.COBpredBGs) else s.COBpredBGs
  let lastCOBpredBG : Option JsNum := if cobPreds then some (rnd (lastOf COBpredBGs)) else none
  let eventualBG1 := if cobPreds then JsNum.max pre.eventualBG (rnd (lastOf COBpredBGs)) else pre.eventualBG
  let uamPreds := (ci >ʲ 0 || remainingCIpeak >ʲ 0) && enableUAM
  let UAMpredBGs := if uamPreds then trimFlat 12 (clampPreds s.UAMpredBGs) else s.UAMpredBGs
  let lastUAMpredBG : Option JsNum := if uamPreds then some (rnd (lastOf UAMpredBGs)) else none
  let eventualBG2 :=
    if uamPreds && (lastOf UAMpredBGs).truthy then JsNum.max eventualBG1 (rnd (lastOf UAMpredBGs)) else eventualBG1
  let predBGs : PredBGs :=
    { IOB := IOBpredBGs.toList, ZT := ZTpredBGs.toList,
      COB := if cobPreds then some COBpredBGs.toList else none,
      UAM := if uamPreds then some UAMpredBGs.toList else none }
  let rT := { rT with predBGs := some predBGs,
                      eventualBG := if ci >ʲ 0 || remainingCIpeak >ʲ 0 then some eventualBG2 else rT.eventualBG }
  let eventualBG := eventualBG2
  -- lines 704-722
  let minIOBPredBG := JsNum.max 39 s.minIOBPredBG
  let minCOBPredBG := JsNum.max 39 s.minCOBPredBG
  let minUAMPredBG := JsNum.max 39 s.minUAMPredBG
  let minPredBG0 := rnd minIOBPredBG
  let fractionCarbsLeft := meal.mealCOB.js / meal.carbs.js
  let avgPredBG0 :=
    if minUAMPredBG <ʲ 999 && minCOBPredBG <ʲ 999 then
      rnd ((1 - fractionCarbsLeft) * s.UAMpredBG + fractionCarbsLeft * s.COBpredBG)
    else if minCOBPredBG <ʲ 999 then rnd ((s.IOBpredBG + s.COBpredBG) / 2)
    else if minUAMPredBG <ʲ 999 then rnd ((s.IOBpredBG + s.UAMpredBG) / 2)
    else rnd s.IOBpredBG
  -- lines 724-726
  let avgPredBG := if s.minZTGuardBG >ʲ avgPredBG0 then s.minZTGuardBG else avgPredBG0
  -- lines 729-740
  let minGuardBG0 :=
    if k.cid.truthy || remainingCIpeak >ʲ 0 then
      if enableUAM then fractionCarbsLeft * s.minCOBGuardBG + (1 - fractionCarbsLeft) * s.minUAMGuardBG
      else s.minCOBGuardBG
    else if enableUAM then s.minUAMGuardBG
    else s.minIOBGuardBG
  let minGuardBG := rnd minGuardBG0
  -- lines 743-760
  let threshold := pre.threshold
  let target_bg := pre.target_bg
  let minZTUAMPredBG0 :=
    if s.minZTGuardBG <ʲ threshold then (minUAMPredBG + s.minZTGuardBG) / 2
    else if s.minZTGuardBG <ʲ target_bg then
      let blendPct := (s.minZTGuardBG - threshold) / (target_bg - threshold)
      let blendedMinZTGuardBG := minUAMPredBG * blendPct + s.minZTGuardBG * (1 - blendPct)
      (minUAMPredBG + blendedMinZTGuardBG) / 2
    else if s.minZTGuardBG >ʲ minUAMPredBG then (minUAMPredBG + s.minZTGuardBG) / 2
    else minUAMPredBG
  let minZTUAMPredBG := rnd minZTUAMPredBG0
  -- lines 763-786
  let minPredBG1 :=
    if meal.carbs.truthyN then
      if !enableUAM && minCOBPredBG <ʲ 999 then rnd (JsNum.max minIOBPredBG minCOBPredBG)
      else if minCOBPredBG <ʲ 999 then
        let blendedMinPredBG := fractionCarbsLeft * minCOBPredBG + (1 - fractionCarbsLeft) * minZTUAMPredBG
        rnd (JsNum.max3 minIOBPredBG minCOBPredBG blendedMinPredBG)
      else if enableUAM then minZTUAMPredBG
      else minGuardBG
    else if enableUAM then rnd (JsNum.max minIOBPredBG minZTUAMPredBG)
    else minPredBG0
  let minPredBG2 := JsNum.min minPredBG1 avgPredBG
  -- lines 800-802
  let minPredBG := if s.maxCOBPredBG >ʲ bg then JsNum.min minPredBG2 s.maxCOBPredBG else minPredBG2
  -- lines 804-818
  let BGI := convertBg pre.bgi p
  let devC := convertBg pre.deviation p
  let ISF := convertBg sens p
  let CR := rnd p.carb_ratio.js 2
  let tgt := convertBg target_bg p
  let reason := "COB: " ++ jsStr meal.mealCOB ++ ", Dev: " ++ devC.toString ++ ", BGI: " ++ BGI.toString ++
    ", ISF: " ++ ISF.toString ++ ", CR: " ++ JsFmt.numToString CR ++ ", minPredBG " ++ convertBgS minPredBG p ++
    ", minGuardBG " ++ convertBgS minGuardBG p ++ ", IOBpredBG " ++ convertBgS lastIOBpredBG p
  let reason := match lastCOBpredBG with
    | some v => if v >ʲ 0 then reason ++ ", COBpredBG " ++ convertBgS v p else reason
    | none => reason
  let reason := match lastUAMpredBG with
    | some v => if v >ʲ 0 then reason ++ ", UAMpredBG " ++ convertBgS v p else reason
    | none => reason
  let reason := reason ++ "; "
  let rT := { rT with COB := meal.mealCOB, IOB := pre.iobd.iob, BGI := some BGI, deviation := some devC,
                      ISF := some ISF, CR := some CR, target_bg := some tgt, reason := some reason }
  -- lines 822-860
  let carbsReqBG := if pre.naive_eventualBG <ʲ 40 then JsNum.min minGuardBG pre.naive_eventualBG else pre.naive_eventualBG
  let bgUndershoot := threshold - carbsReqBG
  let (minutesAboveMinBG, minutesAboveThreshold) :=
    if cobPreds then (minutesAbove COBpredBGs pre.min_bg, minutesAbove COBpredBGs threshold)
    else (minutesAbove IOBpredBGs pre.min_bg, minutesAbove IOBpredBGs threshold)
  let _ := minutesAboveMinBG
  -- lines 862-880
  let enableSMB1 := if enableSMB0 && minGuardBG <ʲ threshold then false else enableSMB0
  let maxDelta_bg_threshold : JsNum := match p.maxDelta_bg_threshold with
    | none => 0.2
    | some m => JsNum.min m 0.3
  let bigDelta := pre.maxDelta >ʲ maxDelta_bg_threshold * bg
  let rT := if bigDelta then
      rT.addReason ("maxDelta " ++ convertBgS pre.maxDelta p ++ " > " ++ JsFmt.numToString (100 * maxDelta_bg_threshold) ++
        "% of BG " ++ convertBgS bg p ++ ": SMB disabled; ")
    else rT
  let enableSMB := if bigDelta then false else enableSMB1
  -- lines 889-903
  let zeroTempDuration := minutesAboveThreshold
  let zeroTempEffect := p.current_basal.js * sens * zeroTempDuration / 60
  let COBforCarbsReq := JsNum.max 0 (meal.mealCOB.js - 0.25 * meal.carbs.js)
  let carbsReq := rnd ((bgUndershoot - zeroTempEffect) / csf - COBforCarbsReq)
  let rT :=
    if meal.reason == some "Could not parse clock data" then rT
    else if carbsReq ≥ʲ p.carbsReqThreshold.js && minutesAboveThreshold ≤ʲ 45 then
      { rT.addReason (JsFmt.numToString carbsReq ++ " add'l carbs req w/in " ++
          JsFmt.numToString minutesAboveThreshold ++ "m; ") with carbsReq := some carbsReq }
    else rT
  { pre with rT, enableSMB, minGuardBG, minPredBG, minIOBPredBG, eventualBG' := eventualBG, carbsReq,
             microBolusAllowed := inp.microBolusAllowed, clock := inp.clock }

/-! ### Dosing decision (lines 905-1188) -/

/-- The recurring "keep the running temp if it already equals the (adjusted)
    basal, otherwise set the basal as a 30-minute temp" block (e.g. lines 944-950). -/
def neutralTemp (c : Ctx) (rT : Result) : Result :=
  if c.ct.duration.js >ʲ 15 && roundBasal c.basal c.p.model =ʲ roundBasal c.ct.rate.js c.p.model then
    rT.addReason (", temp " ++ jsStr c.ct.rate ++ " ~ req " ++ JsFmt.numToString c.basal ++ "U/hr. ")
  else
    setTempBasal c.basal 30 c.p
      (rT.addReason ("; setting current basal of " ++ JsFmt.numToString c.basal ++ " as temp. ")) (some c.ct)

/-- Lines 930-1005: eventual BG below `min_bg`. -/
def lowEventualBG (c : Ctx) (rT : Result) : Result :=
  let p := c.p
  let eventualBG := c.eventualBG'
  let rT := rT.addReason ("Eventual BG " ++ convertBgS eventualBG p ++ " < " ++ convertBgS c.min_bg p)
  -- lines 933-951
  if c.minDelta >ʲ c.expectedDelta && c.minDelta >ʲ 0 && !c.carbsReq.truthy then
    if c.naive_eventualBG <ʲ 40 then
      setTempBasal 0 30 p (rT.addReason ", naive_eventualBG < 40. ") (some c.ct)
    else
      let rT := if c.gs.delta.js >ʲ c.minDelta then
          rT.addReason (", but Delta " ++ convertBgS c.tick.toNum p ++ " > expectedDelta " ++ convertBgS c.expectedDelta p)
        else
          rT.addReason (", but Min. Delta " ++ JsFmt.toFixed c.minDelta 2 ++ " > Exp. Delta " ++ convertBgS c.expectedDelta p)
      neutralTemp c rT
  else
    -- lines 955-968
    let insulinReq0 := rnd (2 * JsNum.min 0 ((eventualBG - c.target_bg) / c.sens)) 2
    let naiveInsulinReq := rnd (JsNum.min 0 ((c.naive_eventualBG - c.target_bg) / c.sens)) 2
    let insulinReq :=
      if c.minDelta <ʲ 0 && c.minDelta >ʲ c.expectedDelta then
        rnd (insulinReq0 * (c.minDelta / c.expectedDelta)) 2
      else insulinReq0
    let rate := roundBasal (c.basal + 2 * insulinReq) p.model
    -- lines 971-978
    let insulinScheduled := c.ct.duration.js * (c.ct.rate.js - c.basal) / 60
    let minInsulinReq := JsNum.min insulinReq naiveInsulinReq
    if insulinScheduled <ʲ minInsulinReq - c.basal * 0.3 then
      setTempBasal rate 30 p
        (rT.addReason (", " ++ jsStr c.ct.duration ++ "m@" ++ JsFmt.toFixed c.ct.rate.js 2 ++
          " is a lot less than needed. ")) (some c.ct)
    else if c.ct.rate.isSome && (c.ct.duration.js >ʲ 5 && rate ≥ʲ c.ct.rate.js * 0.8) then
      rT.addReason (", temp " ++ jsStr c.ct.rate ++ " ~< req " ++ JsFmt.numToString rate ++ "U/hr. ")
    else
      -- lines 983-1003
      if rate ≤ʲ 0 then
        let bgUndershoot := c.target_bg - c.naive_eventualBG
        let worstCaseInsulinReq := bgUndershoot / c.sens
        let durationReq0 := rnd (60 * worstCaseInsulinReq / p.current_basal.js)
        let durationReq :=
          if durationReq0 <ʲ 0 then 0
          else JsNum.min 120 (JsNum.max 0 (rnd (durationReq0 / 30) * 30))
        if durationReq >ʲ 0 then
          setTempBasal rate durationReq p
            (rT.addReason (", setting " ++ JsFmt.numToString durationReq ++ "m zero temp. ")) (some c.ct)
        else setTempBasal rate 30 p rT (some c.ct)
      else
        setTempBasal rate 30 p (rT.addReason (", setting " ++ JsFmt.numToString rate ++ "U/hr. ")) (some c.ct)

/-- The SMB block, lines 1076-1160. Returns `.inl rT` when it returns (an SMB
    low temp is set), `.inr rT` when control continues to the high-temp code. -/
def smbBlock (c : Ctx) (rT : Result) (insulinReq : JsNum) : Result ⊕ Result :=
  let p := c.p
  let now : JsNum := .fin c.clock.now
  let lastBolusAge := rnd ((now - c.iobd.lastBolusTime.js) / 60000) 1
  -- lines 1078-1095
  let mealInsulinReq := rnd (c.meal.mealCOB.js / p.carb_ratio.js) 3
  let maxBolus :=
    if p.maxSMBBasalMinutes.isNone then rnd (p.current_basal.js * 30 / 60) 1
    else if c.iobd.iob.js >ʲ mealInsulinReq && c.iobd.iob.js >ʲ 0 then
      if p.maxUAMSMBBasalMinutes.truthyN then rnd (p.current_basal.js * p.maxUAMSMBBasalMinutes.js / 60) 1
      else rnd (p.current_basal.js * 30 / 60) 1
    else rnd (p.current_basal.js * p.maxSMBBasalMinutes.js / 60) 1
  -- lines 1097-1100
  let bolusIncrement : JsNum := if p.bolus_increment.truthyN then p.bolus_increment.js else 0.1
  let roundSMBTo := 1 / bolusIncrement
  let microBolus := mathFloor (JsNum.min (insulinReq / 2) maxBolus * roundSMBTo) / roundSMBTo
  -- lines 1102-1122
  let smbTarget := c.target_bg
  let worstCaseInsulinReq := (smbTarget - (c.naive_eventualBG + c.minIOBPredBG) / 2) / c.sens
  let durationReq0 := rnd (60 * worstCaseInsulinReq / p.current_basal.js)
  let durationReq1 := if insulinReq >ʲ 0 && microBolus <ʲ bolusIncrement then 0 else durationReq0
  let (durationReq, smbLowTempReq) : JsNum × JsNum :=
    if durationReq1 ≤ʲ 0 then (0, 0)
    else if durationReq1 ≥ʲ 30 then (JsNum.min 60 (JsNum.max 0 (rnd (durationReq1 / 30) * 30)), 0)
    else (30, rnd (c.basal * durationReq1 / 30) 2)
  -- lines 1123-1130
  let rT := rT.addReason (" insulinReq " ++ JsFmt.numToString insulinReq)
  let rT := if microBolus ≥ʲ maxBolus then rT.addReason ("; maxBolus " ++ JsFmt.numToString maxBolus) else rT
  let rT := if durationReq >ʲ 0 then
      rT.addReason ("; setting " ++ JsFmt.numToString durationReq ++ "m low temp of " ++
        JsFmt.numToString smbLowTempReq ++ "U/h") else rT
  let rT := rT.addReason ". "
  -- lines 1133-1150
  let SMBInterval : JsNum := if p.SMBInterval.truthyN then JsNum.min 10 (JsNum.max 1 p.SMBInterval.js) else 3
  let nextBolusMins := rnd (SMBInterval - lastBolusAge) 0
  let nextBolusSeconds := JsNum.mod (rnd ((SMBInterval - lastBolusAge) * 60) 0) 60
  let rT :=
    if lastBolusAge >ʲ SMBInterval then
      if microBolus >ʲ 0 then
        { rT.addReason ("Microbolusing " ++ JsFmt.numToString microBolus ++ "U. ") with units := some microBolus }
      else rT
    else rT.addReason ("Waiting " ++ JsFmt.numToString nextBolusMins ++ "m " ++
      JsFmt.numToString nextBolusSeconds ++ "s to microbolus again. ")
  -- lines 1154-1158
  if durationReq >ʲ 0 then
    .inl { rT with rate := some smbLowTempReq, duration := some durationReq, rateFirst := true }
  else .inr rT

/-- Lines 1054-1188: the high-temp branch when IOB is not above `max_iob`. -/
def highTemp (c : Ctx) (rT : Result) : Result :=
  let p := c.p
  let eventualBG := c.eventualBG'
  -- lines 1058-1069
  let insulinReq0 := rnd ((JsNum.min c.minPredBG eventualBG - c.target_bg) / c.sens) 2
  let capped := insulinReq0 >ʲ c.max_iob - c.iobd.iob.js
  let rT := if capped then rT.addReason ("max_iob " ++ JsFmt.numToString c.max_iob ++ ", ") else rT
  let insulinReq1 := if capped then c.max_iob - c.iobd.iob.js else insulinReq0
  let rate0 := roundBasal (c.basal + 2 * insulinReq1) p.model
  let insulinReq := rnd insulinReq1 3
  let rT := { rT with insulinReq := some insulinReq }
  -- lines 1076-1160
  let afterSmb : Result ⊕ Result :=
    if c.microBolusAllowed && c.enableSMB && c.bg >ʲ c.threshold then smbBlock c rT insulinReq else .inr rT
  match afterSmb with
  | .inl r => r
  | .inr rT =>
    -- lines 1162-1167
    let maxSafeBasal := getMaxSafeBasal p
    let (rate, rT) :=
      if rate0 >ʲ maxSafeBasal then
        (roundBasal maxSafeBasal p.model,
         rT.addReason ("adj. req. rate: " ++ JsFmt.numToString rate0 ++ " to maxSafeBasal: " ++
           JsFmt.numToString maxSafeBasal ++ ", "))
      else (rate0, rT)
    -- lines 1169-1187
    let insulinScheduled := c.ct.duration.js * (c.ct.rate.js - c.basal) / 60
    if insulinScheduled ≥ʲ insulinReq * 2 then
      setTempBasal rate 30 p
        (rT.addReason (jsStr c.ct.duration ++ "m@" ++ JsFmt.toFixed c.ct.rate.js 2 ++
          " > 2 * insulinReq. Setting temp basal of " ++ JsFmt.numToString rate ++ "U/hr. ")) (some c.ct)
    else if c.ct.duration.isNone || c.ct.duration.js =ʲ 0 then
      setTempBasal rate 30 p (rT.addReason ("no temp, setting " ++ JsFmt.numToString rate ++ "U/hr. ")) (some c.ct)
    else if c.ct.duration.js >ʲ 5 && roundBasal rate p.model ≤ʲ roundBasal c.ct.rate.js p.model then
      rT.addReason ("temp " ++ jsStr c.ct.rate ++ " >~ req " ++ JsFmt.numToString rate ++ "U/hr. ")
    else
      setTempBasal rate 30 p (rT.addReason ("temp " ++ jsStr c.ct.rate ++ "<" ++ JsFmt.numToString rate ++ "U/hr. "))
        (some c.ct)

/-- Lines 905-1188 of `determine_basal`: the dosing decision. -/
def dbDose (c : Ctx) : Result :=
  let p := c.p
  let rT := c.rT
  -- lines 908-921: low glucose suspend
  if c.bg <ʲ c.threshold && c.iobd.iob.js <ʲ (-p.current_basal.js * 20 / 60) && c.minDelta >ʲ 0 &&
      c.minDelta >ʲ c.expectedDelta then
    let rT := rT.addReason ("IOB " ++ jsStr c.iobd.iob ++ " < " ++
      JsFmt.numToString (rnd (-p.current_basal.js * 20 / 60) 2))
    let rT := rT.addReason (" and minDelta " ++ convertBgS c.minDelta p ++ " > " ++ "expectedDelta " ++
      convertBgS c.expectedDelta p ++ "; ")
    dbDoseRest c rT
  else if c.bg <ʲ c.threshold || c.minGuardBG <ʲ c.threshold then
    let rT := rT.addReason ("minGuardBG " ++ convertBgS c.minGuardBG p ++ "<" ++ convertBgS c.threshold p)
    let bgUndershoot := c.target_bg - c.minGuardBG
    let worstCaseInsulinReq := bgUndershoot / c.sens
    let durationReq := rnd (60 * worstCaseInsulinReq / p.current_basal.js)
    let durationReq := rnd (durationReq / 30) * 30
    let durationReq := JsNum.min 120 (JsNum.max 30 durationReq)
    setTempBasal 0 durationReq p rT (some c.ct)
  else dbDoseRest c rT
where
  /-- Lines 923-1188, after the low-glucose-suspend check. -/
  dbDoseRest (c : Ctx) (rT : Result) : Result :=
    let p := c.p
    let eventualBG := c.eventualBG'
    let minutes := DateFmt.getMinutes c.clock.now c.clock.tzOffsetMin
    -- lines 925-928
    if p.skip_neutral_temps.truthy && minutes ≥ 55 then
      setTempBasal 0 0 p (rT.addReason ("; Canceling temp at " ++ toString minutes ++ "m past the hour. ")) (some c.ct)
    -- lines 930-1005
    else if eventualBG <ʲ c.min_bg then lowEventualBG c rT
    -- lines 1008-1024
    else if c.minDelta <ʲ c.expectedDelta && !(c.microBolusAllowed && c.enableSMB) then
      let rT := if c.gs.delta.js <ʲ c.minDelta then
          rT.addReason ("Eventual BG " ++ convertBgS eventualBG p ++ " > " ++ convertBgS c.min_bg p ++
            " but Delta " ++ convertBgS c.tick.toNum p ++ " < Exp. Delta " ++ convertBgS c.expectedDelta p)
        else
          rT.addReason ("Eventual BG " ++ convertBgS eventualBG p ++ " > " ++ convertBgS c.min_bg p ++
            " but Min. Delta " ++ JsFmt.toFixed c.minDelta 2 ++ " < Exp. Delta " ++ convertBgS c.expectedDelta p)
      neutralTemp c rT
    -- lines 1026-1038
    else if JsNum.min eventualBG c.minPredBG <ʲ c.max_bg && !(c.microBolusAllowed && c.enableSMB) then
      let rT := rT.addReason (convertBgS eventualBG p ++ "-" ++ convertBgS c.minPredBG p ++ " in range: no temp required")
      neutralTemp c rT
    else
      -- lines 1042-1044
      let rT := if eventualBG ≥ʲ c.max_bg then
          rT.addReason ("Eventual BG " ++ convertBgS eventualBG p ++ " >= " ++ convertBgS c.max_bg p ++ ", ")
        else rT
      -- lines 1045-1053
      if c.iobd.iob.js >ʲ c.max_iob then
        neutralTemp c (rT.addReason ("IOB " ++ JsFmt.numToString (rnd c.iobd.iob.js 2) ++ " > max_iob " ++
          JsFmt.numToString c.max_iob))
      else highTemp c rT

/-- `determine_basal(...)`, lib/determine-basal/determine-basal.js lines 128-1190. -/
def determineBasal (inp : DBInputs) : Result :=
  match dbPrelude inp with
  | .error r => r
  | .ok pre => dbDose (dbPredict inp pre)

end LeanAID
