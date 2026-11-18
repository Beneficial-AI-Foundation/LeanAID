/-
  App.Serve — `aid-lean serve`, for the closed-loop simulation in `sim/`.

  Reads one JSON object per line on stdin and writes one JSON object per line on
  stdout, flushing after each, so that one process serves a whole simulation run.
  Each input line holds what oref0's loop has at one 5-minute step:

    { "pumphistory": [...], "profile": {...}, "clock": "<ISO time>",
      "glucose": [...], "currenttemp": {...}, "meal": {...},
      "autosens": {...} (optional), "microBolusAllowed": bool, "currentTime": <epoch ms> }

  and the output line is

    { "iob": [<IOB array, the fields determine-basal reads, plus the IOB sums>],
      "suggestion": <determine-basal output, as `JSON.stringify(rT)`> }

  Both IOB (`LeanAID.Iob.generate`, lib/iob) and the decision
  (`LeanAID.determineBasal`) are computed by the Lean core. Meal data (COB) is not:
  the caller supplies it (computed by oref0's lib/meal in JavaScript). Time zone UTC.
  This shell is not verified.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import App.Json
import LeanAID.Core.JsonOut

open Lean LeanAID LeanAID.Iob

namespace App.Serve

/-- `new Date(tz(s)).getTime()` for a timestamp string in the formats the simulator
    writes (ISO-8601 with a zone). -/
def msOfStr (s : String) : Option Int := dateParse s 0

def pumpFieldsOf (j : Json) : PumpFields :=
  { type_ := str j "_type", eventType := str j "eventType", enteredBy := str j "enteredBy",
    timestamp := str j "timestamp", timestampMs := (str j "timestamp").bind msOfStr,
    created_at := str j "created_at", created_atMs := (str j "created_at").bind msOfStr,
    amount := num j "amount", insulin := num j "insulin", rate := num j "rate",
    absolute := num j "absolute", duration := num j "duration",
    durationNull := (match field j "duration" with | some .null => true | _ => false),
    durationMin := num j "duration (min)", temp := str j "temp" }

def pumpRecordOf (j : Json) : PumpRecord :=
  { toPumpFields := pumpFieldsOf j,
    bolus := (field j "bolus").bind fun b => match b with
      | .obj _ => some (pumpFieldsOf b)
      | _ => none }

def basalEntryOf (j : Json) : Option BasalEntry := do
  let m ← num j "minutes"
  let r ← num j "rate"
  pure { i := num j "i", minutes := m, rate := r }

/-- The profile, including `basalprofile` (read by lib/iob). -/
def fullProfileOf (j : Json) : Profile :=
  { profileOf j with
    basalprofile := match field j "basalprofile" with
      | some (.arr a) => a.toList.filterMap basalEntryOf
      | _ => [] }

def sumJson (s : IobSum) : List (String × Option String) :=
  [("iob", some (JsonOut.num s.iob)), ("activity", some (JsonOut.num s.activity)),
   ("basaliob", some (JsonOut.num s.basaliob)), ("bolusiob", some (JsonOut.num s.bolusiob)),
   ("netbasalinsulin", some (JsonOut.num s.netbasalinsulin)),
   ("bolusinsulin", some (JsonOut.num s.bolusinsulin))]

/-- The IOB array as JSON (the sums of each tick; `lastBolusTime` and `lastTemp` on the
    first element, as lib/iob/index.js puts them). -/
def iobJson (o : IobOut) : String :=
  let ticks := o.ticks.zipIdx.map fun (t, k) =>
    let extra : List (String × Option String) :=
      if k == 0 then
        [("lastBolusTime", some (JsonOut.num o.lastBolusTime)),
         ("lastTemp", some (JsonOut.obj [("date", some (JsonOut.num o.lastTemp.date)),
            ("rate", o.lastTemp.rate.map JsonOut.num), ("duration", o.lastTemp.duration.map JsonOut.num)]))]
      else []
    JsonOut.obj (sumJson t.sum ++ [("iobWithZeroTemp", some (JsonOut.obj (sumJson t.withZeroTemp)))] ++ extra)
  "[" ++ ",".intercalate ticks ++ "]"

/-- The IOB array as `determine_basal` receives it (the same values a JSON round trip
    of oref0's array gives for the fields it reads). -/
def iobInput (o : IobOut) : IobInput :=
  .array (o.ticks.zipIdx.map fun (t, k) =>
    { iob := some t.sum.iob, activity := some t.sum.activity,
      iobWithZeroTemp := some (some t.withZeroTemp.activity),
      lastTemp := if k == 0 then some { date := some o.lastTemp.date, rate := o.lastTemp.rate,
                                         duration := o.lastTemp.duration } else none,
      lastBolusTime := if k == 0 then some o.lastBolusTime else none })

def step (j : Json) : String :=
  let tz : Int := 0
  let get := fun k => (field j k).getD .null
  let profile := fullProfileOf (get "profile")
  let clockMs : Int := match str j "clock" with
    | some s => (msOfStr s).getD 0
    | none => 0
  let history := match get "pumphistory" with
    | .arr a => a.toList.map pumpRecordOf
    | _ => []
  let iobOut := generate { history, profile, clockMs, tzOffsetMin := tz }
  let entries := match get "glucose" with
    | .arr a => a.toList.map (entryOf · tz)
    | _ => []
  let suggestion := match Glucose.getLastGlucose entries with
    | none => JsonOut.obj [("error", some (JsonOut.str "no glucose"))]
    | some gs =>
      let now : Int := match num j "currentTime" with
        | some (.fin q) => q.floor
        | _ => 0
      let inp : DBInputs :=
        { glucose_status := some gs, currenttemp := some (currentTempOf (get "currenttemp")),
          iob_data := some (iobInput iobOut), profile := some profile,
          autosens_data := (field j "autosens").bind fun a => match a with
            | .obj _ => some { ratio := num a "ratio" } | _ => none,
          meal_data := some (match field j "meal" with | some m => mealOf m | none => {}),
          microBolusAllowed := (bool j "microBolusAllowed").getD false, reservoir_data := .null,
          clock := { now, tzOffsetMin := tz } }
      let r := determineBasal inp
      match r.error with
      | some e => JsonOut.obj [("error", some (JsonOut.str e))]
      | none => JsonOut.result r
  "{\"iob\":" ++ iobJson iobOut ++ ",\"suggestion\":" ++ suggestion ++ "}"

/-- `aid-lean serve`: one output line per input line, until end of input. -/
partial def serve : IO UInt32 := do
  let inp ← IO.getStdin
  let out ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← inp.getLine
    if line.isEmpty then return
    if line.all Char.isWhitespace then loop else
    match Json.parse line with
    | .ok j => out.putStrLn (step j)
    | .error e => out.putStrLn (JsonOut.obj [("parseError", some (JsonOut.str e))])
    out.flush
    loop
  loop
  return 0

end App.Serve
