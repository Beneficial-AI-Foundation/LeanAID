/-
  App.IobBatch — `aid-lean iob-batch <cases.jsonl>`, for the differential test of insulin
  on board, meal history and the basal schedule (`scripts/difftest/iob.js`).

  Each input line is a JSON object

    { "pumphistory": [...], "history24": [...] (optional), "carbhistory": [...],
      "profile": {... with "basalprofile"}, "clock": "<ISO time>", "autosens": {...} (optional),
      "currentIOBOnly": bool (optional),
      "lookups": [ { "schedule": [...], "t": <epoch ms> }, ... ] (optional) }

  and the output line is

    { "iob":   <the IOB array of lib/iob/index.js `generate`, as JSON.stringify prints it>,
      "meal":  <the array of lib/meal/history.js `findMealInputs`>,
      "basal": [<lib/profile/basal.js `basalLookup(schedule, new Date(t))`, null for undefined>, ...] }

  computed by the Lean core (`LeanAID.Iob.generate`, `LeanAID.MealHistory.findMealInputs`,
  `LeanAID.Iob.basalLookup`). Time zone UTC. This shell is not verified.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import App.Json
import App.Serve
import LeanAID.Core.MealHistory

open Lean LeanAID LeanAID.Iob LeanAID.MealHistory

namespace App.IobBatch

/-- One element of `iobTotal`'s result: the six sums and `time` (a `Date`). -/
def sumObj (s : IobSum) : List (String × Option String) :=
  Serve.sumJson s ++ [("time", some (JsonOut.str (DateFmt.toISOString s.time)))]

/-- `lastTemp`: `{date: 0}` if there was no temp, else the temp object of history.js. -/
def lastTempObj (lt : LastTempOut) : String :=
  JsonOut.obj [("rate", lt.rate.map JsonOut.num), ("duration", lt.duration.map JsonOut.num),
    ("timestamp", lt.timestamp.map JsonOut.str),
    ("started_at", lt.startedAt.map (JsonOut.str ∘ DateFmt.toISOString)),
    ("date", some (JsonOut.num lt.date))]

/-- The whole IOB array as `JSON.stringify(iobArray)` prints it (up to key order). -/
def iobArrayJson (o : IobOut) : String :=
  let ticks := o.ticks.zipIdx.map fun (t, k) =>
    let extra : List (String × Option String) :=
      if k == 0 then [("lastBolusTime", some (JsonOut.num o.lastBolusTime)), ("lastTemp", some (lastTempObj o.lastTemp))]
      else []
    JsonOut.obj (sumObj t.sum ++ [("iobWithZeroTemp", some (JsonOut.obj (sumObj t.withZeroTemp)))] ++ extra)
  "[" ++ ",".intercalate ticks ++ "]"

def mealPumpRecordOf (j : Json) : MealPumpRecord :=
  { base := Serve.pumpFieldsOf j, carbs := num j "carbs", carb_input := num j "carb_input" }

def carbRecordOf (j : Json) : CarbRecord :=
  { carbs := num j "carbs", created_at := str j "created_at",
    created_atMs := (str j "created_at").bind Serve.msOfStr }

def mealInputJson (m : MealInput) : String :=
  JsonOut.obj [("timestamp", m.timestamp.map JsonOut.str), ("carbs", m.carbs.map JsonOut.num),
    ("nsCarbs", m.nsCarbs.map JsonOut.num), ("bwCarbs", m.bwCarbs.map JsonOut.num),
    ("journalCarbs", m.journalCarbs.map JsonOut.num), ("bolus", m.bolus.map JsonOut.num)]

def arr (j : Json) : List Json := match j with | .arr a => a.toList | _ => []

def step (j : Json) : String :=
  let tz : Int := 0
  let get := fun k => (field j k).getD .null
  let profile := Serve.fullProfileOf (get "profile")
  let clockMs : Int := match str j "clock" with
    | some s => (Serve.msOfStr s).getD 0
    | none => 0
  let history := (arr (get "pumphistory")).map Serve.pumpRecordOf
  let history24 := (field j "history24").map fun h => (arr h).map Serve.pumpRecordOf
  let autosens : Option Autosens := (field j "autosens").bind fun a => match a with
    | .obj _ => some { ratio := num a "ratio" } | _ => none
  let currentIOBOnly := (bool j "currentIOBOnly").getD false
  let iobOut := generate { history, history24, profile, autosens, clockMs, tzOffsetMin := tz } currentIOBOnly
  let meal := findMealInputs ((arr (get "pumphistory")).map mealPumpRecordOf) ((arr (get "carbhistory")).map carbRecordOf)
  let lookups := (arr (get "lookups")).map fun l =>
    let sched := (arr ((field l "schedule").getD .null)).filterMap Serve.basalEntryOf
    let t : JsNum := (num l "t").getD .nan
    match basalLookup sched t tz with
    | some r => JsonOut.num r
    | none => "null"
  "{\"iob\":" ++ iobArrayJson iobOut ++ ",\"meal\":[" ++ ",".intercalate (meal.map mealInputJson) ++
    "],\"basal\":[" ++ ",".intercalate lookups ++ "]}"

/-- `aid-lean iob-batch <cases.jsonl>`: one output line per input line. -/
def batch (path : String) : IO UInt32 := do
  let h ← IO.FS.Handle.mk path .read
  let out ← IO.getStdout
  let rec loop (fuel : Nat) : IO Unit := do
    match fuel with
    | 0 => pure ()
    | fuel + 1 =>
      let line ← h.getLine
      if line.isEmpty then pure () else
      match Json.parse line with
      | .ok j => out.putStrLn (step j)
      | .error e => out.putStrLn s!"{JsonOut.obj [("parseError", some (JsonOut.str e))]}"
      loop fuel
  loop 100000000
  return 0

end App.IobBatch
