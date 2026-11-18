/-
  LeanAID.Core.BasalSetTemp — transcription of `lib/basal-set-temp.js`.
-/
import LeanAID.Core.RoundBasal

namespace LeanAID

/-- `reason(rT, msg)`, basal-set-temp.js lines 3-6: append with ". " if a
    (non-empty) reason exists. -/
def Result.reasonMsg (r : Result) (msg : String) : Result :=
  { r with reason := some (match r.reason with
      | some s => if s.isEmpty then msg else s ++ ". " ++ msg
      | none => msg) }

/-- The safety multiplier with oref0's default: `undefined`, `null` and `NaN`
    select the default (basal-set-temp.js lines 13-14). -/
def multiplierOr (m : Option JsNum) (dflt : Rat) : JsNum :=
  match m with
  | some (.fin x) => .fin x
  | _ => .fin dflt

/-- `tempBasalFunctions.getMaxSafeBasal(profile)`, basal-set-temp.js lines 11-17:
    `min(max_basal, max_daily_safety_multiplier × max_daily_basal,
         current_basal_safety_multiplier × current_basal)`. -/
def getMaxSafeBasal (p : Profile) : JsNum :=
  JsNum.min3 p.max_basal.js
    (multiplierOr p.max_daily_safety_multiplier 3 * p.max_daily_basal.js)
    (multiplierOr p.current_basal_safety_multiplier 4 * p.current_basal.js)

/-- The clamp of basal-set-temp.js lines 24-28: negative rates become 0, rates
    above `maxSafeBasal` become `maxSafeBasal`. -/
def clampRate (rate maxSafeBasal : JsNum) : JsNum :=
  if rate <ʲ 0 then 0
  else if rate >ʲ maxSafeBasal then maxSafeBasal
  else rate

/-- `tempBasalFunctions.setTempBasal(rate, duration, profile, rT, currenttemp)`,
    basal-set-temp.js lines 19-57. -/
def setTempBasal (rate duration : JsNum) (p : Profile) (rT : Result)
    (currenttemp : Option CurrentTemp) : Result :=
  let maxSafeBasal := getMaxSafeBasal p
  let rate := clampRate rate maxSafeBasal
  let suggestedRate := roundBasal rate p.model
  -- lines 31-34: a running temp close enough to the request is left alone
  let keepRunning : Option (JsNum × JsNum) :=
    match currenttemp with
    | some { duration := some ctDur, rate := some ctRate, .. } =>
      if ctDur >ʲ (duration - 10) && ctDur ≤ʲ 120 && suggestedRate ≤ʲ ctRate * 1.2 &&
          suggestedRate ≥ʲ ctRate * 0.8 && duration >ʲ 0 then some (ctDur, ctRate) else none
    | _ => none
  match keepRunning with
  | some (ctDur, ctRate) =>
    rT.addReason (" " ++ JsFmt.numToString ctDur ++ "m left and " ++ JsFmt.numToString ctRate ++
      " ~ req " ++ JsFmt.numToString suggestedRate ++ "U/hr: no temp required")
  | none =>
    if JsNum.seq suggestedRate p.current_basal.js then
      if p.skip_neutral_temps == some true then
        let tempActive := match currenttemp with
          | some { duration := some d, .. } => d >ʲ 0
          | _ => false
        if tempActive then
          { rT.reasonMsg "Suggested rate is same as profile rate, a temp basal is active, canceling current temp"
            with duration := some 0, rate := some 0 }
        else
          rT.reasonMsg "Suggested rate is same as profile rate, no temp basal is active, doing nothing"
      else
        { rT.reasonMsg ("Setting neutral temp basal of " ++ jsStr p.current_basal ++ "U/hr")
          with duration := some duration, rate := some suggestedRate }
    else
      { rT with duration := some duration, rate := some suggestedRate }

end LeanAID
