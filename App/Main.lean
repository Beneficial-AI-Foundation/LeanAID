/-
  App.Main — `aid-lean`, the command-line shell around the verified core.

    aid-lean determine-basal <iob.json> <currenttemp.json> <glucose.json> <profile.json>
                             [<autosens.json>] [<meal.json>]
                             [--auto-sens F] [--meal F] [--reservoir F] [--currentTime T]
                             [--microbolus] [--safe]
    aid-lean selftest

  `determine-basal` mirrors `bin/oref0-determine-basal.js`: the suggestion as JSON on
  stdout, or the error on stderr. `--safe` (not in oref0) first checks that the input
  is valid in the sense of the safety theorems (`LeanAID.validInputB`) and that meal
  data with carbs has a `lastCarbTime` (FINDINGS F-06), and refuses otherwise
  (exit code 2). This shell is not verified.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import App.Json
import LeanAID
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
  | a :: rest => if a.startsWith "-" then .error s!"Unknown argument: {a}" else
      parseOpts rest { o with positional := o.positional.push a }

def determineBasalCmd (args : List String) : IO UInt32 := do
  let o ← match parseOpts args with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 1
  if o.positional.size < 4 || o.positional.size > 6 then
    IO.eprintln "usage: aid-lean determine-basal <iob.json> <currenttemp.json> <glucose.json> <profile.json> [<autosens.json>] [<meal.json>] [--auto-sens F] [--meal F] [--reservoir F] [--currentTime T] [--microbolus] [--safe]"
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
    let mealOk := !meal.carbs.truthyN || meal.lastCarbTime.isSome
    if !(validInputB inp && mealOk) then
      IO.eprintln "aid-lean --safe: input outside the valid domain of the safety theorems (docs/DESIGN.md); no suggestion"
      return 2
  let r := determineBasal inp
  match r.error with
  | some e => IO.eprintln e
  | none => IO.println (JsonOut.result r)
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
  | _ =>
    IO.eprintln "usage: aid-lean determine-basal <iob.json> <currenttemp.json> <glucose.json> <profile.json> [<autosens.json>] [<meal.json>] [options]\n       aid-lean selftest\nResearch artifact. Not for dosing insulin."
    return 1
