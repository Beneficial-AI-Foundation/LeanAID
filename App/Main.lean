/-
  App.Main — `aid-lean`, the command-line shell around the verified core.

    aid-lean determine-basal <iob.json> <currenttemp.json> <glucose.json> <profile.json>
                             [<autosens.json>] [<meal.json>]
                             [--auto-sens F] [--meal F] [--reservoir F] [--currentTime T]
                             [--microbolus] [--safe] [--fixed]
    aid-lean selftest
    aid-lean serve [--fixed]  (JSON lines on stdin: IOB and determine-basal; see App/Serve.lean)
    aid-lean batch <cases.jsonl> [--fixed | --fixed-triggers]
    aid-lean iob-batch <cases.jsonl> [--fixed]  (IOB, meal history, basal lookups; see App/IobBatch.lean)

  `--fixed` (not in oref0) runs the corrected version of `LeanAID/Fixed` instead of the
  faithful translation: `determineBasalFixed` (fixes of F-04, F-11, F-12, F-23) and
  `generateFixed` (F-24); see docs/FIXED.md. Without `--fixed` nothing changes.
  `batch --fixed-triggers` prints `{"triggers":[...],"result":<line>}` for each case, with
  the findings whose trigger holds (`LeanAID.Fixed.triggers`).

  `determine-basal` mirrors `bin/oref0-determine-basal.js`: the suggestion as JSON on
  stdout, or the error on stderr. `--safe` (not in oref0) first checks that the input
  is valid in the sense of the safety theorems (`LeanAID.validInputB`) and that meal
  data with carbs has a `lastCarbTime` (FINDINGS F-06) and that meal data with COB has
  positive carbs (F-23; this check is not in oref0), and refuses otherwise
  (exit code 2). This shell is not verified.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import App.Json
import App.Serve
import App.IobBatch
import LeanAID.Core.JsonOut
import LeanAID.Spec.ValidCheck
import LeanAID.Fixed.Combined
import LeanAID.Conformance.Case
import LeanAID.Conformance.Data.DetermineBasalData
import LeanAID.Conformance.Data.IobData
import LeanAID.Conformance.Data.SmallData
import Std.Time

open Lean LeanAID LeanAID.Conformance

namespace App

def readJson (path : String) : IO Json := do
  let s ← IO.FS.readFile path
  match Json.parse s with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"Could not parse input data: {path}: {e}")

/-- Local time zone: offset in minutes and the name JavaScript prints. -/
def localZone (nowMs : Int) : IO (Int × String) := do
  let tzEnv ← IO.getEnv "TZ"
  try
    let rules ← Std.Time.Database.defaultGetLocalZoneRules
    let ts := Std.Time.Timestamp.ofMillisecondsSinceUnixEpoch (.ofInt nowMs)
    let ltt := rules.findLocalTimeTypeForTimestamp ts
    let offSec : Int := ltt.getTimeZone.offset.second.val
    let name := if offSec == 0 && (tzEnv == some "UTC" || tzEnv == some "Etc/UTC" || tzEnv == none)
      then "Coordinated Universal Time" else ltt.getTimeZone.name
    pure (offSec / 60, name)
  catch _ => pure (0, "Coordinated Universal Time")

structure Opts where
  positional : Array String := #[]
  autosens : Option String := none
  meal : Option String := none
  reservoir : Option String := none
  currentTime : Option String := none
  microbolus : Bool := false
  safe : Bool := false
  fixed : Bool := false

partial def parseOpts (args : List String) (o : Opts := {}) : Except String Opts :=
  match args with
  | [] => .ok o
  | "--auto-sens" :: f :: rest => parseOpts rest { o with autosens := some f }
  | "-a" :: f :: rest => parseOpts rest { o with autosens := some f }
  | "--meal" :: f :: rest => parseOpts rest { o with meal := some f }
  | "-m" :: f :: rest => parseOpts rest { o with meal := some f }
  | "--reservoir" :: f :: rest => parseOpts rest { o with reservoir := some f }
  | "-r" :: f :: rest => parseOpts rest { o with reservoir := some f }
  | "--currentTime" :: t :: rest => parseOpts rest { o with currentTime := some t }
  | "-c" :: t :: rest => parseOpts rest { o with currentTime := some t }
  | "--microbolus" :: rest => parseOpts rest { o with microbolus := true }
  | "--safe" :: rest => parseOpts rest { o with safe := true }
  | "--fixed" :: rest => parseOpts rest { o with fixed := true }
  | a :: rest => if a.startsWith "-" then .error s!"Unknown argument: {a}" else
      parseOpts rest { o with positional := o.positional.push a }

def determineBasalCmd (args : List String) : IO UInt32 := do
  let o ← match parseOpts args with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 1
  if o.positional.size < 4 || o.positional.size > 6 then
    IO.eprintln "usage: aid-lean determine-basal <iob.json> <currenttemp.json> <glucose.json> <profile.json> [<autosens.json>] [<meal.json>] [--auto-sens F] [--meal F] [--reservoir F] [--currentTime T] [--microbolus] [--safe] [--fixed]"
    return 1
  let autosensFile := o.autosens <|> o.positional[4]?
  let mealFile := o.meal <|> o.positional[5]?
  -- the clock
  let wallNow : Int := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val
  let (tz0, _) ← localZone wallNow
  let now : Int ← match o.currentTime with
    | some t => match dateParse t tz0 with
      | some ms => pure ms
      | none => pure wallNow
    | none => pure wallNow
  let (tz, tzName) ← localZone now
  let ioj ← readJson o.positional[0]!
  let ctj ← readJson o.positional[1]!
  let glj ← readJson o.positional[2]!
  let prj ← readJson o.positional[3]!
  let entries := match glj with
    | .arr a => a.toList.map (entryOf · tz)
    | _ => []
  let some gs := Glucose.getLastGlucose entries
    | IO.eprintln "Could not parse input data: no glucose readings"; return 1
  let autosens : Option Autosens ← match autosensFile with
    | none => pure none
    | some f => do
      try
        let j ← readJson f
        pure (some { ratio := num j "ratio" })
      catch _ => pure (some { ratio := some 1 })
  let meal : MealData ← match mealFile with
    | none => pure {}
    | some f => do
      try pure (mealOf (← readJson f))
      catch _ => pure {}
  let reservoir : Reservoir ← match o.reservoir with
    | none => pure .null
    | some f => do
      try pure (.str (← IO.FS.readFile f))
      catch _ => pure .null
  let microbolus ← if o.microbolus then System.FilePath.isDir "autotune" else pure false
  let inp : DBInputs :=
    { glucose_status := some gs, currenttemp := some (currentTempOf ctj), iob_data := some (iobInputOf ioj tz),
      profile := some (profileOf prj), autosens_data := autosens, meal_data := some meal,
      microBolusAllowed := microbolus, reservoir_data := reservoir,
      clock := { now, tzOffsetMin := tz, tzName } }
  if o.safe then
    -- docs/DESIGN.md, "What `--safe` rejects": (1) profile/autosens outside V0-V10,
    -- (2) carbs without lastCarbTime (F-06), (3) a glucose reading without a finite date (F-11),
    -- (4) COB without positive carbs (F-23)
    let reasons : List String :=
      (if validInputB inp then [] else ["profile or autosens outside the valid domain (V0-V10)"]) ++
      (if !meal.carbs.truthyN || (match meal.lastCarbTime with | some (.fin _) => true | _ => false) then []
       else ["meal data has carbs but no numeric lastCarbTime (F-06)"]) ++
      (match gs.date with | some (.fin _) => [] | _ => ["glucose reading has no date (F-11)"]) ++
      -- Not in oref0: oref0 computes `fractionCarbsLeft = mealCOB / carbs` without a check
      -- (determine-basal.js:709). With COB and no positive carbs it is NaN or infinite, and at
      -- low BG oref0 then issues rate 0 with a NaN duration (F-23).
      (if !meal.mealCOB.truthyN || (match meal.carbs with | some (.fin c) => decide (0 < c) | _ => false) then []
       else ["meal data has mealCOB but no positive carbs (F-23)"])
    if !reasons.isEmpty then
      IO.eprintln s!"aid-lean --safe: refusing input: {"; ".intercalate reasons}; no suggestion"
      return 2
  let r := if o.fixed then LeanAID.Fixed.determineBasalFixed inp else determineBasal inp
  match r.error with
  | some e => IO.eprintln e
  | none => IO.println (JsonOut.result r)
  return 0

/-- One case of `aid-lean batch`: a JSON object with the contents of the CLI's input
    files (`iob`, `currenttemp`, `glucose`, `profile`, optional `autosens`, `meal`),
    `microBolusAllowed` and `currentTime` (epoch ms). -/
def batchInput (j : Json) : Option DBInputs :=
  let tz : Int := 0
  let get := fun k => (field j k).getD .null
  let entries := match get "glucose" with
    | .arr a => a.toList.map (entryOf · tz)
    | _ => []
  match Glucose.getLastGlucose entries with
  | none => none
  | some gs =>
    let now : Int := match num j "currentTime" with
      | some (.fin q) => q.floor
      | _ => 0
    let inp : DBInputs :=
      { glucose_status := some gs, currenttemp := some (currentTempOf (get "currenttemp")),
        iob_data := some (iobInputOf (get "iob") tz), profile := some (profileOf (get "profile")),
        autosens_data := (field j "autosens").bind fun a => match a with
          | .obj _ => some { ratio := num a "ratio" } | _ => none,
        meal_data := some (match field j "meal" with | some m => mealOf m | none => {}),
        microBolusAllowed := (bool j "microBolusAllowed").getD false, reservoir_data := .null,
        clock := { now, tzOffsetMin := tz } }
    some inp

/-- How `aid-lean batch` prints a result. -/
def resultLine (r : Result) : String :=
  match r.error with
  | some e => JsonOut.obj [("error", some (JsonOut.str e))]
  | none => JsonOut.result r

/-- `aid-lean batch`'s output for one case: oref0's result, or with `mode` `fixed` the
    corrected result, or with `fixedTriggers` the corrected result and the triggers. -/
inductive BatchMode | oref0 | fixed | fixedTriggers

def batchCase (j : Json) (mode : BatchMode := .oref0) : String :=
  match batchInput j with
  | none => "{\"error\":\"no glucose\"}"
  | some inp =>
    match mode with
    | .oref0 => resultLine (determineBasal inp)
    | .fixed => resultLine (LeanAID.Fixed.determineBasalFixed inp)
    | .fixedTriggers =>
      "{\"triggers\":[" ++ ",".intercalate ((LeanAID.Fixed.triggers inp).map JsonOut.str) ++ "],\"result\":" ++
        resultLine (LeanAID.Fixed.determineBasalFixed inp) ++ "}"

/-- `aid-lean batch <cases.jsonl>`: one output line per input line (time zone UTC). -/
def batch (path : String) (mode : BatchMode := .oref0) : IO UInt32 := do
  let h ← IO.FS.Handle.mk path .read
  let out ← IO.getStdout
  let rec loop (fuel : Nat) : IO Unit := do
    match fuel with
    | 0 => pure ()
    | fuel + 1 =>
      let line ← h.getLine
      if line.isEmpty then pure () else
      match Json.parse line with
      | .ok j => out.putStrLn (batchCase j mode)
      | .error e => out.putStrLn s!"{JsonOut.obj [("parseError", some (JsonOut.str e))]}"
      loop fuel
  loop 100000000
  return 0

def selftest : IO UInt32 := do
  let db := DetermineBasalData.all
  let dis := DetermineBasalData.disabled
  let rb := SmallData.roundBasal
  let st := SmallData.setTempBasal
  let bl := SmallData.basalLookup
  let md := SmallData.maxDailyBasal
  let gl := SmallData.getLastGlucose
  let ch := SmallData.cobHistory
  let iob := IobData.all
  let dbOk := (db.filter DBCase.ok).length
  let disOk := (dis.filter DBCase.ok).length
  let rbOk := (rb.filter RBCase.ok).length
  let stOk := (st.filter STBCase.ok).length
  let blOk := (bl.filter BasalLookupCase.ok).length + (md.filter MaxDailyCase.ok).length
  let glOk := (gl.filter GLGCase.ok).length
  let chOk := (ch.filter COBHCase.ok).length
  let iobExact := (iob.filter IobCase.ok).length
  let iobTies := (iob.filter IobCase.okUpToTies).length
  IO.println s!"determine_basal (oref0 tests)        {dbOk}/{db.length}"
  IO.println s!"determine_basal (disabled tests)     {disOk}/{dis.length}"
  IO.println s!"round_basal                          {rbOk}/{rb.length}"
  IO.println s!"setTempBasal                         {stOk}/{st.length}"
  IO.println s!"basal lookup / max daily basal       {blOk}/{bl.length + md.length}"
  IO.println s!"getLastGlucose                       {glOk}/{gl.length}"
  IO.println s!"meal history                         {chOk}/{ch.length}"
  IO.println s!"iob (exact)                          {iobExact}/{iob.length}"
  IO.println s!"iob (up to rounding ties)            {iobTies}/{iob.length}"
  let total := db.length + dis.length + rb.length + st.length + bl.length + md.length + gl.length + ch.length + iob.length
  let passed := dbOk + disOk + rbOk + stOk + blOk + glOk + chOk + iobTies
  IO.println s!"selftest: {passed}/{total} conformance cases ({iobTies - iobExact} at rounding ties)"
  return (if passed == total then 0 else 1)

end App

def main (args : List String) : IO UInt32 := do
  match args with
  | "determine-basal" :: rest => App.determineBasalCmd rest
  | ["selftest"] => App.selftest
  | ["batch", f] => App.batch f
  | ["batch", f, "--fixed"] => App.batch f .fixed
  | ["batch", f, "--fixed-triggers"] => App.batch f .fixedTriggers
  | ["serve"] => App.Serve.serve
  | ["serve", "--fixed"] => App.Serve.serve true
  | ["iob-batch", f] => App.IobBatch.batch f
  | ["iob-batch", f, "--fixed"] => App.IobBatch.batch f true
  | _ =>
    IO.eprintln "usage: aid-lean determine-basal <iob.json> <currenttemp.json> <glucose.json> <profile.json> [<autosens.json>] [<meal.json>] [options]\n       aid-lean selftest\n       aid-lean serve [--fixed]\n       aid-lean batch <cases.jsonl> [--fixed | --fixed-triggers]\n       aid-lean iob-batch <cases.jsonl> [--fixed]\n(--fixed: the corrected version, docs/FIXED.md)\nResearch artifact. Not for dosing insulin."
    return 1
