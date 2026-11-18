/-
  LeanAID.Conformance.Case — the shape of a conformance case.
-/
import LeanAID.Core.DetermineBasal
import LeanAID.Core.JsonOut
import LeanAID.Core.Iob
import LeanAID.Core.Glucose
import LeanAID.Core.MealHistory

namespace LeanAID.Conformance

/-- A `determine_basal` call made by oref0's test suite: the inputs and oref0's
    output as `JSON.stringify` printed it (`none` if oref0 threw). -/
structure DBCase where
  id : String
  name : String
  input : DBInputs
  expected : Option String

/-- Does the Lean transcription produce exactly oref0's output? -/
def DBCase.ok (c : DBCase) : Bool :=
  match c.expected with
  | some e => JsonOut.result (determineBasal c.input) == e
  | none => (determineBasal c.input).error.isSome

end LeanAID.Conformance

namespace LeanAID.Conformance
open LeanAID.Iob

/-- (iob, activity, basaliob, bolusiob, netbasalinsulin, bolusinsulin) -/
abbrev SumTuple := JsNum × JsNum × JsNum × JsNum × JsNum × JsNum

def _root_.LeanAID.Iob.IobSum.tuple (s : IobSum) : SumTuple :=
  (s.iob, s.activity, s.basaliob, s.bolusiob, s.netbasalinsulin, s.bolusinsulin)

/-- A call of `lib/iob` (`generate`) made by oref0's tests, with oref0's output. -/
structure IobCase where
  id : String
  name : String
  input : HistoryInputs
  currentIOBOnly : Bool
  ticks : List (SumTuple × SumTuple)
  lastBolusTime : JsNum
  lastTempDate : JsNum
  lastTempRate : Option JsNum
  lastTempDuration : Option JsNum

/-- Exact agreement with oref0 on every element of the IOB array. -/
def IobCase.ok (c : IobCase) : Bool :=
  let o := generate c.input c.currentIOBOnly
  o.ticks.map (fun t => (t.sum.tuple, t.withZeroTemp.tuple)) == c.ticks &&
  o.lastBolusTime == c.lastBolusTime && o.lastTemp.date == c.lastTempDate &&
  o.lastTemp.rate == c.lastTempRate && o.lastTemp.duration == c.lastTempDuration

end LeanAID.Conformance

namespace LeanAID.Conformance

/-- `round_basal(basal, profile)` -/
structure RBCase where
  id : String
  name : String
  basal : JsNum
  model : Option String
  expected : JsNum

def RBCase.ok (c : RBCase) : Bool := roundBasal c.basal c.model == c.expected

/-- `setTempBasal(rate, duration, profile, rT, currenttemp)` -/
structure STBCase where
  id : String
  name : String
  rate : JsNum
  duration : JsNum
  profile : Profile
  rT : Result
  currenttemp : Option CurrentTemp
  expRate : Option JsNum
  expDuration : Option JsNum
  expReason : Option String

def STBCase.ok (c : STBCase) : Bool :=
  let r := LeanAID.setTempBasal c.rate c.duration c.profile c.rT c.currenttemp
  r.rate == c.expRate && r.duration == c.expDuration && r.reason == c.expReason

structure BasalLookupCase where
  id : String
  schedule : List BasalEntry
  nowMs : Int
  expected : Option JsNum

def BasalLookupCase.ok (c : BasalLookupCase) : Bool := Iob.basalLookup c.schedule (.fin c.nowMs) 0 == c.expected

structure MaxDailyCase where
  id : String
  basals : List BasalEntry
  expected : JsNum

def MaxDailyCase.ok (c : MaxDailyCase) : Bool := Iob.maxDailyBasal c.basals == c.expected

/-- JSON rendering of `glucose_status` as `JSON.stringify` prints it. -/
def glucoseStatusJson (g : GlucoseStatus) : String :=
  JsonOut.obj [("delta", g.delta.map JsonOut.num), ("glucose", g.glucose.map JsonOut.num), ("noise", g.noise.map JsonOut.num),
    ("short_avgdelta", g.short_avgdelta.map JsonOut.num), ("long_avgdelta", g.long_avgdelta.map JsonOut.num),
    ("date", g.date.map JsonOut.num), ("last_cal", g.last_cal.map JsonOut.num), ("device", g.device.map JsonOut.str)]

structure GLGCase where
  id : String
  name : String
  entries : List Glucose.Entry
  expected : String

def GLGCase.ok (c : GLGCase) : Bool :=
  match Glucose.getLastGlucose c.entries with
  | some g => glucoseStatusJson g == c.expected
  | none => false

structure COBHCase where
  id : String
  name : String
  pump : List MealHistory.MealPumpRecord
  carbs : List MealHistory.CarbRecord
  expected : List MealHistory.MealInput

def COBHCase.ok (c : COBHCase) : Bool := MealHistory.findMealInputs c.pump c.carbs == c.expected

end LeanAID.Conformance

namespace LeanAID.Conformance
open LeanAID.Iob

/-- The activity sum of `iobTotal` before its final `Math.round(x*10000)/10000`. -/
def rawActivity (ts : List Treatment) (p : Profile) (timeMs : Int) : JsNum :=
  let now : JsNum := .fin timeMs
  let (curve, dia, peak) := curveSetup p
  ts.foldl (fun a t =>
    if t.date ≤ʲ now && t.date >ʲ now - dia * 60 * 60 * 1000 then
      match iobCalc t timeMs curve dia peak p with
      | some c => if c.activityContrib.truthy then a + c.activityContrib else a
      | none => a
    else a) 0

/-- `x · 10000` lies exactly halfway between two integers. -/
def isTie4 : JsNum → Bool
  | .fin q => let y := q * 10000; decide (y - (y.floor : Rat) = 1/2)
  | .nan => false

/-- Two IOB tuples agree except for `activity`, which differs by exactly
    1/10000, and the exact (rational) activity before rounding is a tie. The
    JavaScript computes the same quantity in doubles, lands just below the tie
    and rounds down; exact arithmetic rounds the tie up (docs/DESIGN.md, D2). -/
def tupleOkUpToTie (got exp : SumTuple) (raw : JsNum) : Bool :=
  got == exp ||
  (got.1 == exp.1 && got.2.2 == exp.2.2 && isTie4 raw &&
    (match got.2.1, exp.2.1 with
     | .fin a, .fin b => a - b = 1/10000 || b - a = 1/10000
     | _, _ => false))

/-- Agreement with oref0, allowing only the tie differences of `tupleOkUpToTie`. -/
def IobCase.okUpToTies (c : IobCase) : Bool :=
  let o := generate c.input c.currentIOBOnly
  let tr := (calcTempTreatments c.input none).treatments
  let trZ := (calcTempTreatments { c.input with history := (calcTempTreatments c.input none).history, history24 := none }
              (some 240)).treatments
  let rows := (o.ticks.zip c.ticks).zipIdx
  o.ticks.length == c.ticks.length &&
  rows.all (fun ((t, (es, ez)), k) =>
    let time := c.input.clockMs + (k * 5 : Nat) * 60000
    tupleOkUpToTie t.sum.tuple es (rawActivity tr c.input.profile time) &&
    tupleOkUpToTie t.withZeroTemp.tuple ez (rawActivity trZ c.input.profile time)) &&
  o.lastBolusTime == c.lastBolusTime && o.lastTemp.date == c.lastTempDate &&
  o.lastTemp.rate == c.lastTempRate && o.lastTemp.duration == c.lastTempDuration

end LeanAID.Conformance
