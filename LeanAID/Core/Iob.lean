/-
  LeanAID.Core.Iob — transcription of insulin on board:
  `lib/iob/calculate.js`, `lib/iob/total.js`, `lib/iob/history.js`,
  `lib/iob/index.js` and `basalLookup` from `lib/profile/basal.js`.

  Times are epoch milliseconds. The shell parses every timestamp string the way
  oref0 does (`new Date(tz(s))`, moment-timezone) and passes both the string
  (oref0 compares timestamp strings with `===`) and its time value.
  Local-time computations (`getHours()`, `moment().format()`) use the fixed
  offset `tzOffsetMin`; daylight-saving transitions are not modelled.
-/
import LeanAID.Core.Types
import LeanAID.Core.DateFmt
import LeanAID.Core.Exp

namespace LeanAID.Iob

open JsNum

/-! ### lib/profile/basal.js -/

/-- Stable sort by a numeric key, ascending, `NaN` last (lodash `_.sortBy`). -/
def sortByKey {α : Type} (key : α → JsNum) (xs : List α) : List α :=
  xs.mergeSort fun a b => match key a, key b with
    | .fin x, .fin y => decide (x ≤ y)
    | .fin _, .nan => true
    | .nan, .fin _ => false
    | .nan, .nan => true

/-- `basalLookup(schedules, now)`, basal.js lines 6-28. `nowMs` is the time value
    of the `Date` passed (`NaN` for an invalid date). Returns `none` when the
    function returns `undefined` (last rate is 0). -/
def basalLookup (schedules : List BasalEntry) (nowMs : JsNum) (tzOffsetMin : Int) : Option JsNum :=
  let data := (sortByKey (fun e => e.i.js) schedules).toArray
  if h : data.size = 0 then none     -- JavaScript would throw reading `.rate` of undefined
  else
    let basalRate0 := data[data.size - 1].rate
    if basalRate0 =ʲ 0 then none
    else
      let nowMinutes : JsNum := match DateFmt.timeClip nowMs with
        | .fin q => .fin ((DateFmt.getHours q.floor tzOffsetMin) * 60 + DateFmt.getMinutes q.floor tzOffsetMin : Nat)
        | .nan => .nan
      let rec find (i : Nat) (fuel : Nat) : JsNum :=
        match fuel with
        | 0 => basalRate0
        | fuel + 1 =>
          if i + 1 < data.size then
            if nowMinutes ≥ʲ data[i]!.minutes && nowMinutes <ʲ data[i + 1]!.minutes then data[i]!.rate
            else find (i + 1) fuel
          else basalRate0
      some (mathRound (find 0 data.size * 1000) / 1000)

/-- `maxDailyBasal(inputs)`, basal.js lines 31-34: the largest rate. -/
def maxDailyBasal (basals : List BasalEntry) : JsNum :=
  match basals with
  | [] => .nan
  | b :: bs => (bs.foldl (fun m e => if e.rate >ʲ m.rate then e else m) b).rate * 1000 / 1000

/-! ### lib/iob/calculate.js -/

/-- What `iobCalc` returns: `{activityContrib, iobContrib}`, or `{}` (`none`). -/
structure Contrib where
  activityContrib : JsNum
  iobContrib : JsNum
  deriving Repr, Inhabited

/-- `iobCalcBilinear(treatment, minsAgo, dia)`, calculate.js lines 40-88. -/
def iobCalcBilinear (insulin minsAgo dia : JsNum) : Contrib :=
  let default_dia : JsNum := 3
  let peak : JsNum := 75
  let end_ : JsNum := 180
  let timeScalar := default_dia / dia
  let scaled_minsAgo := timeScalar * minsAgo
  let activityPeak := 2 / (dia * 60)
  let slopeUp := activityPeak / peak
  let slopeDown := -1 * (activityPeak / (end_ - peak))
  if scaled_minsAgo <ʲ peak then
    let x1 := scaled_minsAgo / 5 + 1
    { activityContrib := insulin * (slopeUp * scaled_minsAgo),
      iobContrib := insulin * ((-0.001852 * x1 * x1) + (0.001852 * x1) + 1.000000) }
  else if scaled_minsAgo <ʲ end_ then
    let minsPastPeak := scaled_minsAgo - peak
    let x2 := (scaled_minsAgo - peak) / 5
    { activityContrib := insulin * (activityPeak + (slopeDown * minsPastPeak)),
      iobContrib := insulin * ((0.001323 * x2 * x2) + (-0.054233 * x2) + 0.555560) }
  else { activityContrib := 0, iobContrib := 0 }

/-- The peak time used by `iobCalcExponential`, calculate.js lines 93-121.
    `peak0` is the default passed in by total.js. -/
def exponentialPeak (p : Profile) (peak0 : JsNum) : JsNum :=
  if p.curve == some "rapid-acting" then
    if p.useCustomPeakTime == some true && p.insulinPeakTime.isSome then
      if p.insulinPeakTime.js >ʲ 120 then 120
      else if p.insulinPeakTime.js <ʲ 50 then 50
      else p.insulinPeakTime.js
    else 75
  else if p.curve == some "ultra-rapid" then
    if p.useCustomPeakTime == some true && p.insulinPeakTime.isSome then
      if p.insulinPeakTime.js >ʲ 100 then 100
      else if p.insulinPeakTime.js <ʲ 35 then 35
      else p.insulinPeakTime.js
    else 55
  else peak0   -- QUIRK: unsupported or differently-cased curve keeps total.js's default

/-- `iobCalcExponential(treatment, minsAgo, dia, peak, profile)`, calculate.js lines 91-142. -/
def iobCalcExponential (insulin minsAgo dia peak0 : JsNum) (p : Profile) : Contrib :=
  let peak := exponentialPeak p peak0
  let end_ := dia * 60
  if minsAgo <ʲ end_ then
    let tau := peak * (1 - peak / end_) / (1 - 2 * peak / end_)
    let a := 2 * tau / end_
    let S := 1 / (1 - a + (1 + a) * Exp.jsExp (-end_ / tau))
    let e := Exp.jsExp (-minsAgo / tau)
    { activityContrib := insulin * (S / (tau * tau)) * minsAgo * (1 - minsAgo / end_) * e,
      iobContrib := insulin * (1 - S * (1 - a) * ((minsAgo * minsAgo / (tau * end_ * (1 - a)) - minsAgo / tau - 1) * e + 1)) }
  else { activityContrib := 0, iobContrib := 0 }

/-- A treatment as produced by `find_insulin` (history.js): an insulin dose
    (`insulin` set) or a temp basal record (`rate`, `duration` set). -/
structure Treatment where
  insulin : Option JsNum := none
  /-- `treatment.date` (may be fractional for temp-basal micro-boluses) -/
  date : JsNum
  /-- `treatment.started_at` time value, for boluses (index.js lastBolusTime) -/
  startedAt : Option Int := none
  rate : Option JsNum := none
  duration : Option JsNum := none
  timestamp : Option String := none
  deriving Repr, Inhabited

/-- `iobCalc(treatment, time, curve, dia, peak, profile)`, calculate.js lines 3-37. -/
def iobCalc (t : Treatment) (timeMs : Int) (curve : String) (dia peak : JsNum) (p : Profile) : Option Contrib :=
  if t.insulin.truthyN then
    let bolusTime := DateFmt.timeClip t.date
    let minsAgo := mathRound ((.fin timeMs - bolusTime) / 1000 / 60)
    if curve == "bilinear" then some (iobCalcBilinear t.insulin.js minsAgo dia)
    else some (iobCalcExponential t.insulin.js minsAgo dia peak p)
  else none

/-! ### lib/iob/total.js -/

/-- The result of `iobTotal`. -/
structure IobSum where
  iob : JsNum
  activity : JsNum
  basaliob : JsNum
  bolusiob : JsNum
  netbasalinsulin : JsNum
  bolusinsulin : JsNum
  time : Int
  deriving Repr, Inhabited

/-- The curve name and DIA after total.js's defaults (lines 20-58):
    DIA at least 3 h; at least 5 h for the exponential curves; unknown curve
    names fall back to "rapid-acting". Returns (curve, dia, default peak). -/
def curveSetup (p : Profile) : String × JsNum × JsNum :=
  let dia0 := p.dia.js
  let dia1 := if dia0 <ʲ 3 then 3 else dia0
  let curve0 := match p.curve with
    | some c => c.toLower
    | none => "bilinear"
  let curve := if curve0 == "bilinear" || curve0 == "rapid-acting" || curve0 == "ultra-rapid" then curve0
    else "rapid-acting"
  let requireLongDia := curve != "bilinear"
  let peak : JsNum := if curve == "ultra-rapid" then 55 else 75
  let dia := if requireLongDia && dia1 <ʲ 5 then 5 else dia1
  (curve, dia, peak)

/-- `iobTotal(opts, time)`, total.js lines 3-102. -/
def iobTotal (treatments : List Treatment) (p : Profile) (timeMs : Int) : IobSum :=
  let now : JsNum := .fin timeMs
  let (curve, dia, peak) := curveSetup p
  let step := fun (acc : JsNum × JsNum × JsNum × JsNum × JsNum × JsNum) (t : Treatment) =>
    let (iob, activity, basaliob, bolusiob, netbasalinsulin, bolusinsulin) := acc
    if t.date ≤ʲ now then
      let dia_ago := now - dia * 60 * 60 * 1000
      if t.date >ʲ dia_ago then
        match iobCalc t timeMs curve dia peak p with
        | some c =>
          let iob := if c.iobContrib.truthy then iob + c.iobContrib else iob
          let activity := if c.activityContrib.truthy then activity + c.activityContrib else activity
          if t.insulin.truthyN && c.iobContrib.truthy then
            if t.insulin.js <ʲ 0.1 then
              (iob, activity, basaliob + c.iobContrib, bolusiob, netbasalinsulin + t.insulin.js, bolusinsulin)
            else (iob, activity, basaliob, bolusiob + c.iobContrib, netbasalinsulin, bolusinsulin + t.insulin.js)
          else (iob, activity, basaliob, bolusiob, netbasalinsulin, bolusinsulin)
        | none => acc
      else acc
    else acc
  let (iob, activity, basaliob, bolusiob, netbasalinsulin, bolusinsulin) :=
    treatments.foldl step (0, 0, 0, 0, 0, 0)
  let r3 := fun x => mathRound (x * 1000) / 1000
  { iob := r3 iob, activity := mathRound (activity * 10000) / 10000, basaliob := r3 basaliob,
    bolusiob := r3 bolusiob, netbasalinsulin := r3 netbasalinsulin, bolusinsulin := r3 bolusinsulin, time := timeMs }

/-! ### lib/iob/history.js -/

/-- The fields of a pump-history record that history.js reads. -/
structure PumpFields where
  type_ : Option String := none
  eventType : Option String := none
  enteredBy : Option String := none
  /-- `timestamp`, as a string (compared with `===`) and as a time value
      (`new Date(tz(timestamp))`; `none` = invalid/undefined) -/
  timestamp : Option String := none
  timestampMs : Option Int := none
  created_at : Option String := none
  created_atMs : Option Int := none
  amount : Option JsNum := none
  insulin : Option JsNum := none
  rate : Option JsNum := none
  absolute : Option JsNum := none
  duration : Option JsNum := none
  /-- `duration` is JSON `null` (AndroidAPS "cancel TBR" records) -/
  durationNull : Bool := false
  /-- `"duration (min)"` -/
  durationMin : Option JsNum := none
  temp : Option String := none
  deriving Repr, Inhabited

/-- A pump-history record; `bolus` is the nested `bolus` object of
    `{bolus: {_type: "Bolus", ...}}` records. -/
structure PumpRecord extends PumpFields where
  bolus : Option PumpFields := none
  deriving Repr, Inhabited

/-- A temp basal event during splitting (history.js `temp` objects). -/
structure TempEvent where
  rate : JsNum
  duration : JsNum
  /-- `started_at` time value -/
  startedAt : Int
  date : JsNum
  timestamp : Option String := none
  /-- `new Date(event.timestamp)` (used for the basal lookup, line 498) -/
  timestampMs : Option Int := none
  /-- JavaScript `null` duration (AndroidAPS cancel records); distinct from 0 -/
  durationNull : Bool := false
  /-- QUIRK Q8 (aliasing): `some k` when this event is the very object stored at
      index `k` of `tempHistory` (an event that `splitTimespan` did not split is
      returned as the same object). `splitAroundSuspends` mutates such events in
      place, and the mutation shows up in the `tempHistory` entries that
      history.js returns (and from which index.js takes `lastTemp`). Copies
      (`_.cloneDeep`) have `none`. -/
  origin : Option Nat := none
  deriving Repr, Inhabited

/-- `moment(t).add(m, 'minutes').format()` parsed back with `new Date(...)`:
    the time value moves by `m` minutes (JavaScript `Date` truncates fractional
    milliseconds) and `format()` drops the milliseconds. -/
def addMinutesFormatted (t : Int) (m : JsNum) : Option Int :=
  match DateFmt.timeClip (.fin t + m * 60000) with
  | .fin q => some ((q.floor / 1000) * 1000)
  | .nan => none

/-- Local minutes since midnight, `d.getHours() * 60 + d.getMinutes()`. -/
def localMinutes (t : Int) (tz : Int) : JsNum :=
  .fin ((DateFmt.getHours t tz) * 60 + DateFmt.getMinutes t tz : Nat)

/-- `splitTimespanWithOneSplitter(event, splitter)`, history.js lines 8-48
    (only `recurring` splitters exist). -/
def splitOne (e : TempEvent) (splitterMinutes : JsNum) (tz : Int) : List TempEvent :=
  let startMinutes := localMinutes e.startedAt tz
  let endMinutes := startMinutes + e.duration
  if e.duration >ʲ 30 || (startMinutes <ʲ splitterMinutes && endMinutes >ʲ splitterMinutes) ||
     (endMinutes >ʲ 1440 && splitterMinutes <ʲ (endMinutes - 1440)) then
    let event1Duration : JsNum :=
      if e.duration >ʲ 30 then 30
      else
        let splitPoint := if endMinutes >ʲ 1440 then 1440 else splitterMinutes
        splitPoint - startMinutes
    match addMinutesFormatted e.startedAt event1Duration with
    | some t2 =>
      [{ e with duration := event1Duration, origin := none },
       { e with duration := e.duration - event1Duration, timestamp := some "(split)", timestampMs := some t2,
                startedAt := t2, date := .fin t2, origin := none }]
    | none => [e]
  else [e]

/-- One pass of `splitTimespan`'s `while` loop (history.js lines 58-77).
    QUIRK Q6: `splitFound` is shared across the elements of a pass, so once one
    element has been split, every later element of the same pass that does not
    split is dropped. -/
def splitPass (splitters : List JsNum) (tz : Int) (results : List TempEvent) : List TempEvent × Bool :=
  results.foldl (fun (acc, splitFound) o =>
    let rec tryAll : List JsNum → Option (List TempEvent)
      | [] => none
      | s :: ss => let r := splitOne o s tz; if r.length > 1 then some r else tryAll ss
    match tryAll splitters with
    | some r => (acc ++ r, true)
    | none => if !splitFound then (acc ++ [o], splitFound) else (acc, splitFound)) ([], false)

/-- `splitTimespan(event, splitterMoments)`, history.js lines 50-80. The `while`
    loop terminates in oref0 because every split shortens an event; here it has
    a fuel bound of 10 000 passes (never reached: each pass that splits produces
    events of at most 30 minutes after the first pass, and a day has 48). -/
def splitTimespan (e : TempEvent) (splitters : List JsNum) (tz : Int) : List TempEvent :=
  go 10000 [e]
where
  go : Nat → List TempEvent → List TempEvent
    | 0, rs => rs
    | fuel + 1, rs =>
      let (rs', found) := splitPass splitters tz rs
      if found then go fuel rs' else rs'

/-- A pump suspend with its matched duration (minutes; `none` if unmatched). -/
structure Suspend where
  timestamp : Option String
  startedAt : Option Int
  date : JsNum
  duration : Option JsNum := none
  deriving Repr, Inhabited

/-- `splitAroundSuspends(...)`, history.js lines 85-157. -/
def splitAroundSuspends (ev : TempEvent) (suspends : List Suspend) (firstResumeMs : Option Int)
    (suspendedPrior : Bool) (lastSuspendTimeNum : JsNum) (currentlySuspended : Bool) : List TempEvent :=
  let firstResumeDate : JsNum := match firstResumeMs with | some t => .fin t | none => .nan
  -- lines 94-104
  let ev :=
    if suspendedPrior && ev.date <ʲ firstResumeDate then
      if ev.date + ev.duration * 60 * 1000 <ʲ firstResumeDate then { ev with duration := 0 }
      else
        match firstResumeMs with
        | some fr => { ev with duration := (ev.date + ev.duration * 60 * 1000 - firstResumeDate) / 60 / 1000, startedAt := fr, date := firstResumeDate }
        | none => ev
    else ev
  -- lines 106-112. QUIRK Q7: `lastSuspendTime` is a timestamp string, so these
  -- numeric comparisons are with NaN and never hold for ISO timestamps.
  let ev :=
    if currentlySuspended && ev.date + ev.duration * 60 * 1000 >ʲ lastSuspendTimeNum then
      if ev.date >ʲ lastSuspendTimeNum then { ev with duration := 0 }
      else { ev with duration := (firstResumeDate - ev.date) / 60 / 1000 }
    else ev
  if ev.duration =ʲ 0 then [ev]
  else
    -- lines 121-154: for each suspend, adjust every event (the array grows while iterating)
    suspends.foldl (fun events s =>
      let sd := s.duration.js
      let rec walk (j : Nat) (events : Array TempEvent) (fuel : Nat) : Array TempEvent :=
        match fuel with
        | 0 => events
        | fuel + 1 =>
          if h : j < events.size then
            let e := events[j]
            let eEnd := e.date + e.duration * 60 * 1000
            let sEnd := s.date + sd * 60 * 1000
            if e.date ≤ʲ s.date && eEnd >ʲ s.date then
              let events :=
                if eEnd >ʲ sEnd then
                  match s.startedAt.bind (fun st => addMinutesFormatted st sd) with
                  | some t2 => events.push { e with timestamp := some "(split)", timestampMs := some t2, startedAt := t2, date := sEnd, duration := (eEnd - sEnd) / 60 / 1000, origin := none }
                  | none => events
                else events
              let events := events.set! j { e with duration := (s.date - e.date) / 60 / 1000 }
              walk (j + 1) events fuel
            else if s.date ≤ʲ e.date && sEnd >ʲ e.date then
              let e' := match s.startedAt.bind (fun st => addMinutesFormatted st sd) with
                | some t2 => { e with duration := (eEnd - sEnd) / 60 / 1000, timestamp := some "(split)", timestampMs := some t2, startedAt := t2, date := sEnd }
                | none => { e with duration := (eEnd - sEnd) / 60 / 1000, date := sEnd }
              walk (j + 1) (events.set! j e') fuel
            else walk (j + 1) events fuel
          else events
      walk 0 events (events.size * 4 + 64)) #[ev] |>.toList

/-- Inputs of `calcTempTreatments` (history.js `inputs`). -/
structure HistoryInputs where
  history : List PumpRecord
  history24 : Option (List PumpRecord) := none
  profile : Profile
  /-- `inputs.autosens`; `none` = undefined -/
  autosens : Option Autosens := none
  /-- `new Date(tz(inputs.clock))` -/
  clockMs : Int
  tzOffsetMin : Int := 0
  deriving Repr, Inhabited

/-- `Number(s)` for a timestamp string: numeric strings convert, others are NaN. -/
def numberOfString (s : String) : JsNum :=
  match s.toInt? with
  | some i => .fin i
  | none => .nan

/-- Time value of a record's `timestamp` for `new Date(tz(...))`; moment(undefined)
    is the current time. -/
def recTime (r : PumpFields) (now : Int) : Option Int :=
  match r.timestamp with
  | none => some now
  | some _ => r.timestampMs

/-- The result of `calcTempTreatments` and the history after its in-place
    mutation (`current.timestamp = current.created_at`, line 291), which a
    second call sees. -/
structure HistoryOut where
  treatments : List Treatment
  history : List PumpRecord

/-- `calcTempTreatments(inputs, zeroTempDuration)`, history.js lines 159-569. -/
def calcTempTreatments (inp : HistoryInputs) (zeroTempDuration : Option JsNum) : HistoryOut := Id.run do
  let p := inp.profile
  let tz := inp.tzOffsetMin
  let nowMs := inp.clockMs
  let now : JsNum := .fin nowMs
  let mut pumpHistory : Array PumpRecord :=
    (inp.history ++ (inp.history24.getD [])).toArray
  -- lines 181-198: suspends and resumes
  let mut pumpSuspends : List Suspend := []
  let mut pumpResumes : List Suspend := []
  for cur in pumpHistory do
    let t := recTime cur.toPumpFields nowMs
    let d : JsNum := match t with | some t => .fin t | none => .nan
    if cur.type_ == some "PumpSuspend" then
      pumpSuspends := pumpSuspends ++ [{ timestamp := cur.timestamp, startedAt := t, date := d }]
    else if cur.type_ == some "PumpResume" then
      pumpResumes := pumpResumes ++ [{ timestamp := cur.timestamp, startedAt := t, date := d }]
  pumpSuspends := sortByKey (·.date) pumpSuspends
  pumpResumes := sortByKey (·.date) pumpResumes
  let resumesA := pumpResumes.toArray
  let mut suspendedPrior := false
  let mut firstResumeMs : Option Int := none
  if h : 0 < resumesA.size then
    firstResumeMs := resumesA[0].startedAt
    if pumpSuspends.isEmpty || resumesA[0].date <ʲ (pumpSuspends.head!).date then suspendedPrior := true
  -- lines 210-232: match resumes with suspends
  let mut susA := pumpSuspends.toArray
  let mut j := 0
  let mut currentlySuspended := false
  let mut lastSuspendTime : Option String := none
  let mut iStop := susA.size
  for i in [0:susA.size] do
    while j < resumesA.size && !(resumesA[j]!.date >ʲ susA[i]!.date) do
      j := j + 1
    if j ≥ resumesA.size && !currentlySuspended then
      currentlySuspended := true
      lastSuspendTime := susA[i]!.timestamp
      iStop := i
      break
    susA := susA.set! i { susA[i]! with duration := some ((resumesA[j]!.date - susA[i]!.date) / 60 / 1000) }
  -- lines 249-253: truncate extra suspends
  if iStop + 1 < susA.size then susA := susA.extract 0 (iStop + 1)
  let suspends := susA.toList
  -- lines 257-385: relevant events
  let mut tempHistory : Array TempEvent := #[]
  let mut tempBoluses : Array Treatment := #[]
  let mut lastRecordTime : JsNum := now
  for i in [0:pumpHistory.size] do
    let rec0 := pumpHistory[i]!
    let mut cur : PumpFields := match rec0.bolus with
      | some b => if b.type_ == some "Bolus" then b else rec0.toPumpFields
      | none => rec0.toPumpFields
    -- line 290-292: in-place mutation of the record
    if cur.created_at.isSome then
      cur := { cur with timestamp := cur.created_at, timestampMs := cur.created_atMs }
      pumpHistory := pumpHistory.set! i (match rec0.bolus with
        | some b => if b.type_ == some "Bolus" then { rec0 with bolus := some cur } else { rec0 with toPumpFields := cur }
        | none => { rec0 with toPumpFields := cur })
    let currentRecordTime : JsNum := match recTime cur nowMs with | some t => .fin t | none => .nan
    if currentRecordTime >ʲ lastRecordTime then continue
    lastRecordTime := currentRecordTime
    let ts := recTime cur nowMs
    let tsJ : JsNum := match ts with | some t => .fin t | none => .nan
    let createdMs : Option Int := match cur.created_at with | some _ => cur.created_atMs | none => some nowMs
    let createdJ : JsNum := match createdMs with | some t => .fin t | none => .nan
    if cur.type_ == some "Bolus" then
      if tsJ >ʲ now then pure ()    -- future bolus: ignored (lines 306-308)
      else tempBoluses := tempBoluses.push { insulin := cur.amount, date := tsJ, startedAt := ts, timestamp := cur.timestamp }
    else if cur.eventType == some "Meal Bolus" || cur.eventType == some "Correction Bolus" ||
            cur.eventType == some "Snack Bolus" || cur.eventType == some "Bolus Wizard" then
      tempBoluses := tempBoluses.push { insulin := cur.insulin, date := createdJ, startedAt := createdMs, timestamp := cur.created_at }
    else if cur.enteredBy == some "xdrip" then
      tempBoluses := tempBoluses.push { insulin := cur.insulin, date := tsJ, startedAt := ts, timestamp := cur.timestamp }
    else if cur.enteredBy == some "HAPP_App" && cur.insulin.truthyN then
      tempBoluses := tempBoluses.push { insulin := cur.insulin, date := createdJ, startedAt := createdMs, timestamp := cur.created_at }
    else if cur.eventType == some "Temp Basal" && (cur.enteredBy == some "HAPP_App" || cur.enteredBy == some "openaps://AndroidAPS") then
      tempHistory := tempHistory.push { rate := cur.absolute.js, duration := cur.duration.js, startedAt := createdMs.getD 0, date := createdJ, timestamp := cur.created_at, timestampMs := createdMs, durationNull := cur.durationNull }
    else if cur.eventType == some "Temp Basal" then
      let rate := if cur.amount.isSome then cur.amount.js / cur.duration.js * 60 else cur.rate.js
      tempHistory := tempHistory.push { rate, duration := cur.duration.js, startedAt := ts.getD 0, date := tsJ, timestamp := cur.timestamp, timestampMs := ts, durationNull := cur.durationNull }
    else if cur.type_ == some "TempBasal" then
      if cur.temp == some "percent" then continue
      -- lines 347-363: find the matching TempBasalDuration record
      let duration : JsNum :=
        if i > 0 && pumpHistory[i-1]!.timestamp == cur.timestamp && pumpHistory[i-1]!.type_ == some "TempBasalDuration" then
          pumpHistory[i-1]!.durationMin.js
        else
          match pumpHistory.toList.find? (fun r => r.timestamp == cur.timestamp && r.type_ == some "TempBasalDuration") with
          | some r => r.durationMin.js
          | none => .nan
      tempHistory := tempHistory.push { rate := cur.rate.js, duration, startedAt := ts.getD 0, date := tsJ, timestamp := cur.timestamp, timestampMs := ts }
    -- lines 374-384: a zero temp starting 1 minute from now, after every record
    tempHistory := tempHistory.push { rate := 0, startedAt := nowMs + 60000, date := .fin (nowMs + 60000), duration := zeroTempDuration.getD 0 }
  -- lines 388-399: sort and trim overlapping temps
  let mut th := (sortByKey (·.date) tempHistory.toList).toArray
  let mut i := 0
  let mut fuel := th.size * 2 + 2
  while i + 1 < th.size && fuel > 0 do
    fuel := fuel - 1
    if th[i]!.date + th[i]!.duration * 60 * 1000 >ʲ th[i+1]!.date then
      th := th.set! i { th[i]! with duration := (th[i+1]!.date - th[i]!.date) / 60 / 1000 }
      if th[i+1]!.durationNull then th := th.eraseIdxIfInBounds (i + 1)
    i := i + 1
  let thO := (th.toList.zipIdx.map fun (e, k) => { e with origin := some k }).toArray
  let tempHistoryFinal := thO.toList
  -- lines 404-421: split at basal schedule changes
  let splitters := p.basalprofile.map (·.minutes)
  let splitHistoryByBasal := tempHistoryFinal.flatMap (fun o => splitTimespan o splitters tz)
  -- lines 425-479: suspends
  let lastSuspendTimeNum : JsNum := match lastSuspendTime with | some s => numberOfString s | none => .nan
  let (splitHistory, tempHistoryFinal) :=
    if p.suspend_zeros_iob.truthy then
      let sh := splitHistoryByBasal.flatMap fun o =>
        splitAroundSuspends o suspends firstResumeMs suspendedPrior lastSuspendTimeNum currentlySuspended
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
      -- QUIRK Q8: write the in-place mutations back to the aliased tempHistory entries
      let thMut := sh.foldl (fun (acc : Array TempEvent) e => match e.origin with
        | some k => acc.set! k { acc[k]! with duration := e.duration, date := e.date, startedAt := e.startedAt }
        | none => acc) thO
      (sh ++ (zSuspend ++ zPrior ++ zCurrent).flatMap (fun o => splitTimespan o splitters tz), thMut.toList)
    else (splitHistoryByBasal, tempHistoryFinal)
  let splitHistory := sortByKey (·.date) splitHistory
  -- lines 486-564: temp basals → 0.05 U micro-boluses
  for item in splitHistory do
    if item.duration >ʲ 0 then
      let currentRate0 : Option JsNum :=
        if p.basalprofile.isEmpty then p.current_basal
        else basalLookup p.basalprofile (match item.timestampMs with | some t => .fin t | none => .nan) tz
      let target_bg : JsNum :=
        if p.min_bg.isSome && p.max_bg.isSome then (p.min_bg.js + p.max_bg.js) / 2 else .nan
      let halfBasalTarget : JsNum := if p.half_basal_exercise_target.truthyN then p.half_basal_exercise_target.js else 160
      let sensitivityRatio : Option JsNum :=
        if p.exercise_mode.truthy && p.temptargetSet.truthy && target_bg ≥ʲ 105 then
          let c := halfBasalTarget - 100
          some (c / (c + target_bg - 100))
        else inp.autosens.bind (·.ratio)
      let currentRate := if sensitivityRatio.truthyN then currentRate0.js * sensitivityRatio.js else currentRate0.js
      let netBasalRate := item.rate - currentRate
      let tempBolusSize : JsNum := if netBasalRate <ʲ 0 then -0.05 else 0.05
      let netBasalAmount := mathRound (netBasalRate * item.duration * 10 / 6) / 100
      let tempBolusCount := mathRound (netBasalAmount / tempBolusSize)
      let tempBolusSpacing := item.duration / tempBolusCount
      match tempBolusCount with
      | .fin c =>
        let n := if c > 0 then c.floor.toNat else 0
        for k in [0:n] do
          tempBoluses := tempBoluses.push
            { insulin := some tempBolusSize, date := item.date + .fin (k : Nat) * tempBolusSpacing * 60 * 1000 }
      | .nan => pure ()
  -- lines 565-568
  let tempAsTreatments : List Treatment := tempHistoryFinal.map fun e =>
    { date := e.date, rate := some e.rate, duration := some e.duration, timestamp := e.timestamp,
      startedAt := some e.startedAt }
  let all := sortByKey (·.date) (tempBoluses.toList ++ tempAsTreatments)
  return { treatments := all, history := pumpHistory.toList }

/-! ### lib/iob/index.js -/

/-- One element of the IOB array. -/
structure IobArrayElem where
  sum : IobSum
  withZeroTemp : IobSum
  deriving Repr, Inhabited

/-- `lastTemp` as index.js builds it. -/
structure LastTempOut where
  date : JsNum
  rate : Option JsNum := none
  duration : Option JsNum := none
  timestamp : Option String := none
  startedAt : Option Int := none
  deriving Repr, Inhabited

/-- The output of `generate(inputs, currentIOBOnly)`. -/
structure IobOut where
  ticks : List IobArrayElem
  lastBolusTime : JsNum
  lastTemp : LastTempOut
  deriving Repr, Inhabited

/-- `generate(inputs, currentIOBOnly)`, index.js lines 8-82. -/
def generate (inp : HistoryInputs) (currentIOBOnly : Bool := false) : IobOut :=
  let r1 := calcTempTreatments inp none
  let treatments := r1.treatments
  -- the second call sees the history as mutated by the first
  let r2 := calcTempTreatments { inp with history := r1.history, history24 := none } (some 240)
  let treatmentsWithZeroTemp := r2.treatments
  let (lastBolusTime, lastTemp) := treatments.foldl (fun (lbt, lt) t =>
    if t.insulin.truthyN && t.startedAt.isSome then
      (JsNum.max lbt (.fin t.startedAt.get!), lt)
    else if t.rate.isSome && t.duration.truthyN then
      if t.date >ʲ lt.date then
        (lbt, { date := t.date, rate := t.rate, duration := some (mathRound (t.duration.js * 100) / 100),
                timestamp := t.timestamp, startedAt := t.startedAt })
      else (lbt, lt)
    else (lbt, lt)) ((0 : JsNum), ({ date := 0 } : LastTempOut))
  let iStop := if currentIOBOnly then 1 else 4 * 60
  let ticks := (List.range ((iStop + 4) / 5)).map fun k =>
    let t := inp.clockMs + (k * 5 : Nat) * 60000
    { sum := iobTotal treatments inp.profile t, withZeroTemp := iobTotal treatmentsWithZeroTemp inp.profile t }
  { ticks, lastBolusTime, lastTemp }

end LeanAID.Iob
