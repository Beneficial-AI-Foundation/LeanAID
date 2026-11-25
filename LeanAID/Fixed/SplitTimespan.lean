import LeanAID.Core.Iob

/-!
# F-24: `splitTimespan` drops pieces of a temp (QUIRK Q6), corrected

**This file is not oref0.** `LeanAID/Core` is the faithful transcription of oref0 0.7.1 and
is not changed. `generateF24` is `LeanAID.Iob.generate` (insulin on board,
`lib/iob/index.js`) with `splitTimespan` replaced by `splitTimespanF24`.

**The oref0 code**, `lib/iob/history.js:50-80` in oref0 0.7.1:
```
function splitTimespan(event, splitterMoments) {
    var results = [event];
    var splitFound = true;
    while(splitFound) {
        var resultArray = [];
        splitFound = false;
        _.forEach(results,function split(o) {
            _.forEach(splitterMoments,function split(p) {
                var splitResult = splitTimespanWithOneSplitter(o,p);
                if (splitResult.length > 1) {
                    resultArray = resultArray.concat(splitResult);
                    splitFound = true;
                    return false;
                }
            });
            if (!splitFound) resultArray = resultArray.concat([o]);
        });
        results = resultArray;
    }
    return results;
}
```
`splitFound` is shared by all pieces of one pass: once a piece has split, every later piece
of the pass that does not split is dropped, with its insulin (F-24).

**The fix**, as `sim/q6fix.js` applies it: each piece has its own flag, and `splitFound`
still decides whether another pass is needed.
```
        _.forEach(results,function split(o) {
            var thisSplit = false;
            _.forEach(splitterMoments,function split(p) {
                var splitResult = splitTimespanWithOneSplitter(o,p);
                if (splitResult.length > 1) {
                    resultArray = resultArray.concat(splitResult);
                    splitFound = true; thisSplit = true;
                    return false;
                }
            });
            if (!thisSplit) resultArray = resultArray.concat([o]);
        });
```

`splitStageW`, `calcTempTreatmentsW` and `generateW` are the transcriptions
`LeanAID.Iob.splitStage`, `calcTempTreatments` and `generate` with the split function as a
parameter; with `splitTimespan` they are the transcriptions themselves
(`generateW_splitTimespan`, proved by `rfl` in `Fixed/Proofs/SplitTimespan.lean`).

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Iob JsNum

/-- One pass of `splitTimespan`'s `while` loop with the fix: a piece that no splitter
    splits is kept. Compare `LeanAID.Iob.splitPass`. -/
def splitPassF24 (splitters : List JsNum) (tz : Int) (results : List TempEvent) : List TempEvent × Bool :=
  results.foldl (fun (acc, splitFound) o =>
    match splitPass.tryAll tz o splitters with
    | some r => (acc ++ r, true)
    | none => (acc ++ [o], splitFound)) ([], false)

/-- `splitTimespan` with the fixed pass, with the transcription's fuel bound. -/
def splitTimespanF24 (e : TempEvent) (splitters : List JsNum) (tz : Int) : List TempEvent :=
  go 10000 [e]
where
  go : Nat → List TempEvent → List TempEvent
    | 0, rs => rs
    | fuel + 1, rs =>
      let (rs', found) := splitPassF24 splitters tz rs
      if found then go fuel rs' else rs'

/-! ### The IOB pipeline with the split function as a parameter -/

/-- A split function: `splitTimespan` or `splitTimespanF24`. -/
abbrev SplitFn := TempEvent → List JsNum → Int → List TempEvent

/-- The zero temps of pump suspends, history.js lines 470-503 (in `splitStage`). -/
def suspendZeros (inp : HistoryInputs) (suspends : List Suspend) (firstResumeMs : Option Int)
    (suspendedPrior currentlySuspended : Bool) (lastSuspendTime : Option String) : List TempEvent :=
  let nowMs := inp.clockMs
  let now : JsNum := .fin nowMs
  let zSuspend : List TempEvent := suspends.filterMap fun s =>
    s.startedAt.map fun st => { rate := 0, duration := s.duration.js, startedAt := st, date := s.date }
  let maxDiaAgo := nowMs - 8 * 60 * 60 * 1000
  let firstResumeDate : JsNum := match firstResumeMs with | some t => .fin t | none => .nan
  let zPrior : List TempEvent :=
    if suspendedPrior && (JsNum.fin maxDiaAgo) <ʲ firstResumeDate then
      [{ rate := 0, duration := (firstResumeDate - .fin maxDiaAgo) / 60 / 1000, startedAt := maxDiaAgo, date := .fin maxDiaAgo }]
    else []
  let zCurrent : List TempEvent :=
    if currentlySuspended then
      let lastSuspendMs := (suspends.find? (fun s => s.timestamp == lastSuspendTime)).bind (·.startedAt)
      match lastSuspendMs with
      | some st => [{ rate := 0, duration := (now - .fin st) / 60 / 1000, startedAt := st, date := .fin st, timestamp := lastSuspendTime, timestampMs := some st }]
      | none => []
    else []
  zSuspend ++ zPrior ++ zCurrent

/-- `LeanAID.Iob.splitStage` (history.js lines 396-503) with the split function `split`. -/
def splitStageW (split : SplitFn) (inp : HistoryInputs) (thO : Array TempEvent) (suspends : List Suspend)
    (firstResumeMs : Option Int) (suspendedPrior currentlySuspended : Bool)
    (lastSuspendTime : Option String) : List TempEvent × List TempEvent :=
  let p := inp.profile
  let tz := inp.tzOffsetMin
  let tempHistoryFinal := thO.toList
  let splitters := p.basalprofile.map (·.minutes)
  let splitHistoryByBasal := tempHistoryFinal.flatMap (fun o => split o splitters tz)
  let lastSuspendTimeNum : JsNum := match lastSuspendTime with | some s => numberOfString s | none => .nan
  if p.suspend_zeros_iob.truthy then
    let sh := splitHistoryByBasal.flatMap fun o =>
      splitAroundSuspends o suspends firstResumeMs suspendedPrior lastSuspendTimeNum currentlySuspended tz
    let thMut := sh.foldl (fun (acc : Array TempEvent) e => match e.origin with
      | some k => acc.set! k { acc[k]! with duration := e.duration, date := e.date, startedAt := e.startedAt,
                                            timestamp := e.timestamp }
      | none => acc) thO
    (sh ++ (suspendZeros inp suspends firstResumeMs suspendedPrior currentlySuspended lastSuspendTime).flatMap
      (fun o => split o splitters tz), thMut.toList)
  else (splitHistoryByBasal, tempHistoryFinal)

/-- The values `calcTempTreatments` computes before it splits the temps (history.js lines
    161-394). -/
structure PreSplit where
  thO : Array TempEvent
  suspends : List Suspend
  firstResumeMs : Option Int
  suspendedPrior : Bool
  currentlySuspended : Bool
  lastSuspendTime : Option String
  boluses : Array Treatment
  history : Array PumpRecord

/-- `LeanAID.Iob.calcTempTreatments`, lines 161-394: everything before the split. -/
def preSplit (inp : HistoryInputs) (zeroTempDuration : Option JsNum) : PreSplit :=
  let nowMs := inp.clockMs
  let pumpHistory : Array PumpRecord := (inp.history ++ (inp.history24.getD [])).toArray
  let sr := collectSuspends pumpHistory.toList nowMs
  let pumpSuspends := sortByKey (·.date) sr.1
  let resumesA := (sortByKey (·.date) sr.2).toArray
  let firstResumeMs : Option Int := if h : 0 < resumesA.size then resumesA[0].startedAt else none
  let suspendedPrior : Bool :=
    if h : 0 < resumesA.size then pumpSuspends.isEmpty || resumesA[0].date <ʲ (pumpSuspends.head!).date else false
  let susA0 := pumpSuspends.toArray
  let m := matchSuspends resumesA (List.range susA0.size) { suspends := susA0, iStop := susA0.size }
  let susA := if m.iStop + 1 < m.suspends.size then m.suspends.extract 0 (m.iStop + 1) else m.suspends
  let suspends := susA.toList
  let sc := scanRecords nowMs zeroTempDuration pumpHistory
  let th0 := (sortByKey (·.date) sc.temps.toList).toArray
  let th := trimTemps (th0.size * 2 + 2) 0 th0
  let thO := (th.toList.zipIdx.map fun (e, k) => { e with origin := some k }).toArray
  { thO, suspends, firstResumeMs, suspendedPrior, currentlySuspended := m.currentlySuspended,
    lastSuspendTime := m.lastSuspendTime, boluses := sc.boluses, history := sc.history }

/-- `LeanAID.Iob.calcTempTreatments` (history.js lines 161-571) with the split function
    `split`. -/
def calcTempTreatmentsW (split : SplitFn) (inp : HistoryInputs) (zeroTempDuration : Option JsNum) : HistoryOut :=
  let q := preSplit inp zeroTempDuration
  let sp := splitStageW split inp q.thO q.suspends q.firstResumeMs q.suspendedPrior q.currentlySuspended
    q.lastSuspendTime
  let splitHistory := sortByKey (·.date) sp.1
  let tempBoluses := tempBolusesOf inp splitHistory q.boluses
  let tempAsTreatments : List Treatment := sp.2.map fun e =>
    { date := e.date, rate := some e.rate, duration := some e.duration, timestamp := e.timestamp,
      startedAt := some e.startedAt }
  { treatments := sortByKey (·.date) (tempBoluses.toList ++ tempAsTreatments), history := q.history.toList }

/-- `LeanAID.Iob.generate` (index.js lines 8-82) with the split function `split`. -/
def generateW (split : SplitFn) (inp : HistoryInputs) (currentIOBOnly : Bool := false) : IobOut :=
  let r1 := calcTempTreatmentsW split inp none
  let treatments := r1.treatments
  let r2 := calcTempTreatmentsW split { inp with history := r1.history, history24 := none } (some 240)
  let treatmentsWithZeroTemp := r2.treatments
  let last := treatments.foldl lastStep ((0 : JsNum), ({ date := 0 } : LastTempOut))
  let lastBolusTime := last.1
  let lastTemp := last.2
  let iStop := if currentIOBOnly then 1 else 4 * 60
  let ticks := (List.range ((iStop + 4) / 5)).map fun k =>
    let t := inp.clockMs + (k * 5 : Nat) * 60000
    { sum := iobTotal treatments inp.profile t, withZeroTemp := iobTotal treatmentsWithZeroTemp inp.profile t }
  { ticks, lastBolusTime, lastTemp }

/-- Insulin on board (`lib/iob/index.js` `generate`) with the F-24 fix. -/
def generateF24 (inp : HistoryInputs) (currentIOBOnly : Bool := false) : IobOut :=
  generateW splitTimespanF24 inp currentIOBOnly

/-! ### The trigger -/

/-- The temps that `calcTempTreatments` passes to `splitTimespan`: the trimmed temp history
    and, with `suspend_zeros_iob`, the zero temps of suspends. -/
def splitArgs (inp : HistoryInputs) (zeroTempDuration : Option JsNum) : List TempEvent :=
  let q := preSplit inp zeroTempDuration
  q.thO.toList ++
    (if inp.profile.suspend_zeros_iob.truthy then
      suspendZeros inp q.suspends q.firstResumeMs q.suspendedPrior q.currentlySuspended q.lastSuspendTime
     else [])

/-- One pass of oref0's loop drops a piece: some piece after a piece that splits does not
    split itself. `seen` says whether an earlier piece of the pass has split. -/
def passDrops (splitters : List JsNum) (tz : Int) : Bool → List TempEvent → Bool
  | _, [] => false
  | seen, o :: os =>
    let s := (splitPass.tryAll tz o splitters).isSome
    (seen && !s) || passDrops splitters tz (seen || s) os

/-- oref0's `splitTimespan` (`LeanAID.Iob.splitTimespan`) drops a piece of the temp `e`:
    some pass of its loop drops a piece. -/
def q6Event (e : TempEvent) (splitters : List JsNum) (tz : Int) : Bool :=
  go 10000 [e]
where
  go : Nat → List TempEvent → Bool
    | 0, _ => false
    | fuel + 1, rs =>
      passDrops splitters tz false rs ||
        (let (rs', found) := splitPass splitters tz rs
         if found then go fuel rs' else false)

/-- **The F-24 trigger**, stated with oref0's functions: oref0's `splitTimespan` drops a
    piece of one of the temps it splits, in either of the two calls of `calcTempTreatments`
    by `generate` (the IOB and the IOB with a 240-minute zero temp). -/
def triggerF24 (inp : HistoryInputs) : Bool :=
  let splitters := inp.profile.basalprofile.map (·.minutes)
  let inp2 : HistoryInputs := { inp with history := (calcTempTreatments inp none).history, history24 := none }
  (splitArgs inp none ++ splitArgs inp2 (some 240)).any fun e => q6Event e splitters inp.tzOffsetMin

/-- The F-24 trigger as a proposition. -/
def TriggerF24 (inp : HistoryInputs) : Prop := triggerF24 inp = true

instance (inp : HistoryInputs) : Decidable (TriggerF24 inp) := inferInstanceAs (Decidable (_ = _))

end LeanAID.Fixed
