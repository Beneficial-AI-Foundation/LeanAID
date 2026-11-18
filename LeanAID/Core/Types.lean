/-
  LeanAID.Core.Types — the inputs and outputs of oref0's dose decision.

  Each structure mirrors a JavaScript object that oref0 reads. A field that the
  JavaScript code may find missing is an `Option`: `none` is `undefined`.
  `Option.js` gives the value a missing number takes in arithmetic (`NaN`), and
  `Option.truthy` gives JavaScript truthiness of an optional boolean.

  JSON `null` is mapped to `none` by the shell (`App/Json.lean`); in JavaScript,
  `null` behaves like `0` in arithmetic. This only matters outside the valid input
  domain (`docs/DESIGN.md`) and is listed there as a known difference.
-/
import LeanAID.Core.JsNum

namespace LeanAID

/-- The value of a possibly-missing number in arithmetic (`undefined` → `NaN`). -/
@[inline] def _root_.Option.js (x : Option JsNum) : JsNum := JsNum.ofOpt x

/-- JavaScript truthiness of a possibly-missing boolean. -/
@[inline] def _root_.Option.truthy : Option Bool → Bool
  | some b => b
  | none => false

/-- JavaScript truthiness of a possibly-missing number (`undefined`, `0`, `NaN` are falsy). -/
@[inline] def _root_.Option.truthyN : Option JsNum → Bool
  | some x => x.truthy
  | none => false

/-- JavaScript `x !== y` between two possibly-missing numbers:
    `undefined === undefined`, and `NaN !== NaN`. -/
def optSne : Option JsNum → Option JsNum → Bool
  | none, none => false
  | some a, some b => JsNum.sne a b
  | _, _ => true

/-- `String(x)` for a possibly-missing number. -/
def jsStr : Option JsNum → String
  | some x => JsFmt.numToString x
  | none => "undefined"

/-- One entry of a basal schedule (`profile.basalprofile`). -/
structure BasalEntry where
  i : Option JsNum := none
  minutes : JsNum
  rate : JsNum
  deriving Repr, Inhabited, DecidableEq

/-- The fields of oref0's `profile` object that the in-scope code reads. -/
structure Profile where
  current_basal : Option JsNum := none
  /-- `profile.model`, when it is a string (round_basal checks `typeof === 'string'`). -/
  model : Option String := none
  min_bg : Option JsNum := none
  max_bg : Option JsNum := none
  enableSMB_high_bg_target : Option JsNum := none
  max_iob : Option JsNum := none
  exercise_mode : Option Bool := none
  high_temptarget_raises_sensitivity : Option Bool := none
  low_temptarget_lowers_sensitivity : Option Bool := none
  half_basal_exercise_target : Option JsNum := none
  temptargetSet : Option Bool := none
  autosens_max : Option JsNum := none
  sensitivity_raises_target : Option Bool := none
  resistance_lowers_target : Option Bool := none
  noisyCGMTargetMultiplier : Option JsNum := none
  maxRaw : Option JsNum := none
  sens : Option JsNum := none
  carb_ratio : Option JsNum := none
  allowSMB_with_high_temptarget : Option Bool := none
  A52_risk_enable : Option Bool := none
  enableSMB_always : Option Bool := none
  enableSMB_with_COB : Option Bool := none
  enableSMB_after_carbs : Option Bool := none
  enableSMB_with_temptarget : Option Bool := none
  enableSMB_high_bg : Option Bool := none
  enableUAM : Option Bool := none
  out_units : Option String := none
  remainingCarbsCap : Option JsNum := none
  remainingCarbsFraction : Option JsNum := none
  maxDelta_bg_threshold : Option JsNum := none
  carbsReqThreshold : Option JsNum := none
  skip_neutral_temps : Option Bool := none
  maxSMBBasalMinutes : Option JsNum := none
  maxUAMSMBBasalMinutes : Option JsNum := none
  bolus_increment : Option JsNum := none
  SMBInterval : Option JsNum := none
  max_basal : Option JsNum := none
  max_daily_basal : Option JsNum := none
  /-- `undefined`, `null` and `NaN` all select the default 3 (basal-set-temp.js line 13). -/
  max_daily_safety_multiplier : Option JsNum := none
  /-- `undefined`, `null` and `NaN` all select the default 4 (basal-set-temp.js line 14). -/
  current_basal_safety_multiplier : Option JsNum := none
  -- insulin on board (lib/iob)
  dia : Option JsNum := none
  curve : Option String := none
  useCustomPeakTime : Option Bool := none
  insulinPeakTime : Option JsNum := none
  basalprofile : List BasalEntry := []
  suspend_zeros_iob : Option Bool := none
  deriving Repr, Inhabited

/-- `glucose_status`, the output of `lib/glucose-get-last.js`. -/
structure GlucoseStatus where
  glucose : Option JsNum := none
  delta : Option JsNum := none
  short_avgdelta : Option JsNum := none
  long_avgdelta : Option JsNum := none
  /-- epoch milliseconds -/
  date : Option JsNum := none
  noise : Option JsNum := none
  last_cal : Option JsNum := none
  device : Option String := none
  deriving Repr, Inhabited

/-- `currenttemp`: the temp basal the pump reports as running. -/
structure CurrentTemp where
  duration : Option JsNum := none
  rate : Option JsNum := none
  temp : Option String := none
  deriving Repr, Inhabited

/-- `iob_data.lastTemp`. -/
structure LastTemp where
  date : Option JsNum := none
  rate : Option JsNum := none
  duration : Option JsNum := none
  deriving Repr, Inhabited

/-- One element of the IOB array produced by `lib/iob/index.js`. -/
structure IobTick where
  iob : Option JsNum := none
  activity : Option JsNum := none
  /-- `iobWithZeroTemp.activity`; the outer `none` means `iobWithZeroTemp` is missing. -/
  iobWithZeroTemp : Option (Option JsNum) := none
  lastTemp : Option LastTemp := none
  lastBolusTime : Option JsNum := none
  deriving Repr, Inhabited

/-- `iob_data` as passed to `determine_basal`: a single object (as in oref0's
    unit tests) or the array produced by `oref0-calculate-iob`. -/
inductive IobInput where
  | single (t : IobTick)
  | array (ts : List IobTick)
  deriving Repr, Inhabited

/-- `meal_data`, the output of `lib/meal`. -/
structure MealData where
  carbs : Option JsNum := none
  mealCOB : Option JsNum := none
  bwCarbs : Option JsNum := none
  bwFound : Option Bool := none
  slopeFromMaxDeviation : Option JsNum := none
  slopeFromMinDeviation : Option JsNum := none
  lastCarbTime : Option JsNum := none
  reason : Option String := none
  deriving Repr, Inhabited

/-- `autosens_data`. -/
structure Autosens where
  ratio : Option JsNum := none
  deriving Repr, Inhabited

/-- `reservoir_data`: `undefined` (unit tests), `null` (CLI without
    `--reservoir`), or the raw file contents. -/
inductive Reservoir where
  | undef
  | null
  | str (s : String)
  deriving Repr, Inhabited, DecidableEq

/-- A field that oref0 sets to a number or to a string (`tick`, `convert_bg`). -/
inductive NumOrStr where
  | num (x : JsNum)
  | str (s : String)
  deriving Repr, Inhabited, DecidableEq

def NumOrStr.toString : NumOrStr → String
  | .num x => JsFmt.numToString x
  | .str s => s

/-- JavaScript `Number(x)` applied to a `tick`-like value. Only the strings oref0
    itself builds ("+" followed by a number) occur. -/
def NumOrStr.toNum : NumOrStr → JsNum
  | .num x => x
  | .str s =>
    -- `"+" + n` where `n` is a number oref0 printed: parse it back.
    let t := if s.startsWith "+" then (s.drop 1).toString else s
    match t.toInt? with
    | some i => .fin i
    | none => .nan

/-- The time-and-place facts `determine_basal` reads from the JavaScript runtime:
    `new Date()` (or `currentTime`), and the local time zone, which oref0 uses for
    `getMinutes()` and for printing dates in its reason strings. -/
structure Clock where
  /-- current time, epoch milliseconds -/
  now : Int
  /-- local time zone offset from UTC, in minutes (e.g. +120 for EET) -/
  tzOffsetMin : Int := 0
  /-- the name JavaScript prints in `Date.prototype.toString`, e.g. "Coordinated Universal Time" -/
  tzName : String := "Coordinated Universal Time"
  deriving Repr, Inhabited

/-- Which JavaScript object layout the result has; determines the JSON key order. -/
inductive Shape where
  /-- `{error}` only; the CLI prints the error to stderr and nothing to stdout -/
  | error
  /-- CGM-data error branch, determine-basal.js lines 198-221 -/
  | cgm
  /-- pump-history disagreement, lines 378-392 -/
  | lastTemp
  /-- the main object built at line 428 -/
  | main
  deriving Repr, Inhabited, DecidableEq

/-- `rT.predBGs` -/
structure PredBGs where
  IOB : List JsNum := []
  ZT : List JsNum := []
  COB : Option (List JsNum) := none
  UAM : Option (List JsNum) := none
  deriving Repr, Inhabited

/-- The suggestion object `rT` returned by `determine_basal` / `setTempBasal`.
    A `none` field is absent from the JavaScript object (or `undefined`, which
    `JSON.stringify` also omits). -/
structure Result where
  shape : Shape := .main
  error : Option String := none
  temp : Option String := none
  bg : Option JsNum := none
  tick : Option NumOrStr := none
  eventualBG : Option JsNum := none
  insulinReq : Option JsNum := none
  reservoir : Reservoir := .undef
  deliverAt : Option Int := none
  sensitivityRatio : Option JsNum := none
  predBGs : Option PredBGs := none
  COB : Option JsNum := none
  IOB : Option JsNum := none
  BGI : Option NumOrStr := none
  deviation : Option NumOrStr := none
  ISF : Option NumOrStr := none
  CR : Option JsNum := none
  target_bg : Option NumOrStr := none
  reason : Option String := none
  carbsReq : Option JsNum := none
  units : Option JsNum := none
  rate : Option JsNum := none
  duration : Option JsNum := none
  /-- `true` when `rate` was assigned before `duration` (the SMB return path,
      determine-basal.js lines 1155-1156); affects JSON key order only. -/
  rateFirst : Bool := false
  deriving Repr, Inhabited

/-- `rT.reason += s`: concatenation, where a missing reason prints as "undefined". -/
def Result.addReason (r : Result) (s : String) : Result :=
  { r with reason := some ((r.reason.getD "undefined") ++ s) }

/-- `rT.reason = s` -/
def Result.setReason (r : Result) (s : String) : Result :=
  { r with reason := some s }

/-- An error result `{ error: msg }`. -/
def Result.err (msg : String) : Result := { shape := .error, error := some msg }

end LeanAID
