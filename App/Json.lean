/-
  App.Json — the unverified input shell: JSON values to the core's input types,
  and JavaScript `Date.parse` for the date strings oref0 reads.

  JSON numbers are exact decimals (mantissa · 10^-exponent) and become exact
  rationals, so no floating point is involved. A field of the wrong JSON type is
  treated as missing (`undefined`); see docs/DESIGN.md (D4) for `null`.
-/
import Lean.Data.Json
import LeanAID

namespace App

open Lean LeanAID

def numOf : Json → Option JsNum
  | .num n => some (.fin ((n.mantissa : Rat) / ((10 : Rat) ^ n.exponent)))
  | _ => none

def field (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => some v
  | .error _ => none

def num (j : Json) (k : String) : Option JsNum := (field j k).bind numOf
def bool (j : Json) (k : String) : Option Bool :=
  match field j k with | some (.bool b) => some b | _ => none
def str (j : Json) (k : String) : Option String :=
  match field j k with | some (.str s) => some s | _ => none

/-! ### Dates (`Date.parse`) -/

/-- Days since 1970-01-01 of a proleptic Gregorian date (Hinnant's `days_from_civil`). -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- Split a character list at every `sep`. -/
def splitAt (sep : Char) (s : List Char) : List (List Char) :=
  s.foldr (fun c acc => if c == sep then [] :: acc else match acc with
    | a :: as => (c :: a) :: as
    | [] => [[c]]) [[]]

def digits (s : List Char) : Option Nat :=
  if s.isEmpty || !s.all Char.isDigit then none
  else some (s.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

/-- `Date.parse(s)` for ISO-8601 strings: `YYYY-MM-DD`, optionally `THH:MM[:SS[.sss]]`
    and a zone `Z`, `±HH:MM` or `±HHMM`. Without a zone, a date-time is local time
    (`localOffsetMin`) and a bare date is UTC, as in ECMAScript. -/
def dateParse (s : String) (localOffsetMin : Int) : Option Int := do
  let cs : List Char := ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse
  let (datePart, rest) := (cs.takeWhile (fun c => c != 'T' && c != ' '), cs.dropWhile (fun c => c != 'T' && c != ' '))
  let ds := splitAt '-' datePart
  let (y, mo, d) ← match ds with
    | [a, b, c] => do pure ((← digits a), (← digits b), (← digits c))
    | _ => none
  let base := daysFromCivil y mo d * 86400000
  if rest.isEmpty then return base
  let t := rest.drop 1
  -- zone
  let zoneStart := t.findIdx (fun c => c == 'Z' || c == '+' || c == '-')
  let (timePart, zone) := (t.take zoneStart, t.drop zoneStart)
  let (hms, frac) := (timePart.takeWhile (· != '.'), (timePart.dropWhile (· != '.')).drop 1)
  let hs := splitAt ':' hms
  let (h, mi, se) ← match hs with
    | [a, b] => do pure ((← digits a), (← digits b), 0)
    | [a, b, c] => do pure ((← digits a), (← digits b), (← digits c))
    | _ => none
  let ms : Nat := match digits (frac.take 3) with
    | some v => v * 10 ^ (3 - min 3 (frac.take 3).length)
    | none => 0
  let off : Int ← match zone with
    | [] => some localOffsetMin
    | ['Z'] => some 0
    | sign :: zs =>
      let zz := zs.filter (· != ':')
      match digits (zz.take 2), digits (zz.drop 2) with
      | some zh, some zm => some ((if sign == '-' then -1 else 1) * ((zh : Int) * 60 + zm))
      | some zh, none => if zz.length == 2 then some ((if sign == '-' then -1 else 1) * ((zh : Int) * 60)) else none
      | _, _ => none
  return base + ((h : Int) * 3600000 + mi * 60000 + se * 1000 + ms) - off * 60000

/-- `new Date(x).getTime()` for a JSON value: numbers as they are, strings parsed. -/
def timeOf (j : Json) (tz : Int) : Option JsNum :=
  match j with
  | .num _ => numOf j
  | .str s => (dateParse s tz).map fun t => .fin t
  | _ => none

/-! ### Inputs -/

def profileOf (j : Json) : Profile :=
  { current_basal := num j "current_basal", model := str j "model", min_bg := num j "min_bg",
    max_bg := num j "max_bg", enableSMB_high_bg_target := num j "enableSMB_high_bg_target",
    max_iob := num j "max_iob", exercise_mode := bool j "exercise_mode",
    high_temptarget_raises_sensitivity := bool j "high_temptarget_raises_sensitivity",
    low_temptarget_lowers_sensitivity := bool j "low_temptarget_lowers_sensitivity",
    half_basal_exercise_target := num j "half_basal_exercise_target", temptargetSet := bool j "temptargetSet",
    autosens_max := num j "autosens_max", sensitivity_raises_target := bool j "sensitivity_raises_target",
    resistance_lowers_target := bool j "resistance_lowers_target",
    noisyCGMTargetMultiplier := num j "noisyCGMTargetMultiplier", maxRaw := num j "maxRaw", sens := num j "sens",
    carb_ratio := num j "carb_ratio", allowSMB_with_high_temptarget := bool j "allowSMB_with_high_temptarget",
    A52_risk_enable := bool j "A52_risk_enable", enableSMB_always := bool j "enableSMB_always",
    enableSMB_with_COB := bool j "enableSMB_with_COB", enableSMB_after_carbs := bool j "enableSMB_after_carbs",
    enableSMB_with_temptarget := bool j "enableSMB_with_temptarget", enableSMB_high_bg := bool j "enableSMB_high_bg",
    enableUAM := bool j "enableUAM", out_units := str j "out_units", remainingCarbsCap := num j "remainingCarbsCap",
    remainingCarbsFraction := num j "remainingCarbsFraction", maxDelta_bg_threshold := num j "maxDelta_bg_threshold",
    carbsReqThreshold := num j "carbsReqThreshold", skip_neutral_temps := bool j "skip_neutral_temps",
    maxSMBBasalMinutes := num j "maxSMBBasalMinutes", maxUAMSMBBasalMinutes := num j "maxUAMSMBBasalMinutes",
    bolus_increment := num j "bolus_increment", SMBInterval := num j "SMBInterval", max_basal := num j "max_basal",
    max_daily_basal := num j "max_daily_basal", max_daily_safety_multiplier := num j "max_daily_safety_multiplier",
    current_basal_safety_multiplier := num j "current_basal_safety_multiplier", dia := num j "dia",
    curve := str j "curve", useCustomPeakTime := bool j "useCustomPeakTime", insulinPeakTime := num j "insulinPeakTime",
    suspend_zeros_iob := bool j "suspend_zeros_iob" }

def currentTempOf (j : Json) : CurrentTemp :=
  { duration := num j "duration", rate := num j "rate", temp := str j "temp" }

def iobTickOf (j : Json) (tz : Int) : IobTick :=
  { iob := num j "iob", activity := num j "activity",
    iobWithZeroTemp := (field j "iobWithZeroTemp").bind fun z =>
      match z with | .obj _ => some (num z "activity") | _ => none,
    lastTemp := (field j "lastTemp").bind fun lt =>
      match lt with
      | .obj _ => some { date := (field lt "date").bind (timeOf · tz), rate := num lt "rate", duration := num lt "duration" }
      | _ => none,
    lastBolusTime := (field j "lastBolusTime").bind (timeOf · tz) }

def iobInputOf (j : Json) (tz : Int) : IobInput :=
  match j with
  | .arr a => .array (a.toList.map (iobTickOf · tz))
  | _ => .single (iobTickOf j tz)

def mealOf (j : Json) : MealData :=
  { carbs := num j "carbs", mealCOB := num j "mealCOB", bwCarbs := num j "bwCarbs", bwFound := bool j "bwFound",
    slopeFromMaxDeviation := num j "slopeFromMaxDeviation", slopeFromMinDeviation := num j "slopeFromMinDeviation",
    lastCarbTime := num j "lastCarbTime", reason := str j "reason" }

def entryOf (j : Json) (tz : Int) : Glucose.Entry :=
  { glucose := num j "glucose", sgv := num j "sgv", noise := num j "noise", type_ := str j "type",
    device := str j "device", date := num j "date",
    displayTimeMs := (str j "display_time").bind fun s => (dateParse s tz).map (.fin ·),
    dateStringMs := (str j "dateString").bind fun s => (dateParse s tz).map (.fin ·) }

end App
