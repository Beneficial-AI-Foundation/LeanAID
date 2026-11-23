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

/-- The order of `sortByKey`: ascending by a numeric key, `NaN` last. -/
def keyLe {α : Type} (key : α → JsNum) (a b : α) : Bool :=
  match key a, key b with
    | .fin x, .fin y => decide (x ≤ y)
    | .fin _, .nan => true
    | .nan, .fin _ => false
    | .nan, .nan => true

/-- Insert `a` before the first element `b` with `le a b`. -/
def insertBy {α : Type} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: bs => if le a b then a :: b :: bs else b :: insertBy le a bs

/-- Insertion sort by `le`. It recurses structurally, so the kernel can evaluate it. -/
def insertionSortBy {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => insertBy le a (insertionSortBy le l)

/-- Stable sort by a numeric key, ascending, `NaN` last (lodash `_.sortBy`).
    Defined by insertion sort, which the kernel can evaluate;
    `sortByKey_eq_merge` proves it equal to `List.mergeSort`, and compiled code uses
    the merge sort. -/
def sortByKey {α : Type} (key : α → JsNum) (xs : List α) : List α :=
  insertionSortBy (keyLe key) xs

/-- `sortByKey` as a merge sort. Compiled code runs `sortByKey` as this function
    (`sortByKey_eq_merge` is a `@[csimp]` lemma). -/
def sortByKeyMerge {α : Type} (key : α → JsNum) (xs : List α) : List α :=
  xs.mergeSort (keyLe key)

theorem keyLe_trans {α : Type} (key : α → JsNum) (a b c : α) :
    keyLe key a b → keyLe key b c → keyLe key a c := by
  unfold keyLe
  cases key a <;> cases key b <;> cases key c <;> intro h1 h2 <;>
    simp only [decide_eq_true_eq, Bool.false_eq_true] at * <;>
    first | exact Rat.le_trans h1 h2 | trivial

theorem keyLe_total {α : Type} (key : α → JsNum) (a b : α) : keyLe key a b || keyLe key b a := by
  unfold keyLe
  cases key a <;> cases key b <;> simp_all [Rat.le_total]

theorem insertBy_append {α : Type} (le : α → α → Bool) (a : α) :
    ∀ (l₁ l₂ : List α), (∀ b ∈ l₁, le a b = false) → (∀ b ∈ l₂.head?, le a b = true) →
      insertBy le a (l₁ ++ l₂) = l₁ ++ a :: l₂
  | [], [], _, _ => rfl
  | [], b :: bs, _, h2 => by simp [insertBy, h2 b rfl]
  | b :: l₁, l₂, h1, h2 => by
    have hb : le a b = false := h1 b (by simp)
    simp only [List.cons_append, insertBy, hb]
    rw [insertBy_append le a l₁ l₂ (fun x hx => h1 x (by simp [hx])) h2]
    simp

theorem insertionSortBy_eq_mergeSort {α : Type} (le : α → α → Bool)
    (trans : ∀ (a b c : α), le a b → le b c → le a c) (total : ∀ (a b : α), le a b || le b a) :
    ∀ (l : List α), insertionSortBy le l = l.mergeSort le
  | [] => by simp [insertionSortBy]
  | a :: l => by
    obtain ⟨l₁, l₂, h, h', hl₁⟩ := List.mergeSort_cons trans total a l
    have hs := List.pairwise_mergeSort trans total (a :: l)
    rw [h] at hs
    have hl₂ : ∀ b ∈ l₂, le a b = true := by
      have := List.pairwise_append.mp hs
      exact (List.pairwise_cons.mp this.2.1).1
    simp only [insertionSortBy, insertionSortBy_eq_mergeSort le trans total l, h', h]
    apply insertBy_append
    · intro b hb; simpa using hl₁ b hb
    · intro b hb; exact hl₂ b (List.mem_of_mem_head? hb)

/-- `sortByKey` equals the merge sort. As a `@[csimp]` lemma it makes compiled code
    (the `aid-lean` binary, `native_decide`) use the merge sort. -/
@[csimp] theorem sortByKey_eq_merge : @sortByKey = @sortByKeyMerge := by
  funext α key xs
  exact insertionSortBy_eq_mergeSort _ (keyLe_trans key) (keyLe_total key) xs

theorem mem_sortByKey {α : Type} (key : α → JsNum) (xs : List α) (a : α) :
    a ∈ sortByKey key xs ↔ a ∈ xs := by
  rw [sortByKey_eq_merge]
  simp [sortByKeyMerge]

theorem length_sortByKey {α : Type} (key : α → JsNum) (xs : List α) :
    (sortByKey key xs).length = xs.length := by
  rw [sortByKey_eq_merge]
  simp [sortByKeyMerge]

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

/-- The six running sums of `iobTotal` (iob, activity, basaliob, bolusiob,
    netbasalinsulin, bolusinsulin). -/
abbrev IobAcc := JsNum × JsNum × JsNum × JsNum × JsNum × JsNum

/-- One iteration of `iobTotal`'s loop over the treatments, total.js lines 67-92. -/
def iobStep (p : Profile) (timeMs : Int) (curve : String) (dia peak : JsNum)
    (acc : IobAcc) (t : Treatment) : IobAcc :=
  let now : JsNum := .fin timeMs
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

/-- The running sums of `iobTotal` after all treatments, before rounding. -/
def iobRaw (treatments : List Treatment) (p : Profile) (timeMs : Int) : IobAcc :=
  let cs := curveSetup p
  treatments.foldl (iobStep p timeMs cs.1 cs.2.1 cs.2.2) (0, 0, 0, 0, 0, 0)

/-- `iobTotal(opts, time)`, total.js lines 3-103. -/
def iobTotal (treatments : List Treatment) (p : Profile) (timeMs : Int) : IobSum :=
  let (iob, activity, basaliob, bolusiob, netbasalinsulin, bolusinsulin) := iobRaw treatments p timeMs
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
  /-- `new Date(event.timestamp)` (used for the basal lookup, line 522) -/
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

/-- `splitTimespanWithOneSplitter(event, splitter)`, history.js lines 8-49
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

/-- `splitAroundSuspends(...)`, history.js lines 85-159. -/
def splitAroundSuspends (ev : TempEvent) (suspends : List Suspend) (firstResumeMs : Option Int)
    (suspendedPrior : Bool) (lastSuspendTimeNum : JsNum) (currentlySuspended : Bool) : List TempEvent :=
  let firstResumeDate : JsNum := match firstResumeMs with | some t => .fin t | none => .nan
  -- lines 94-103
  let ev :=
    if suspendedPrior && ev.date <ʲ firstResumeDate then
      if ev.date + ev.duration * 60 * 1000 <ʲ firstResumeDate then { ev with duration := 0 }
      else
        match firstResumeMs with
        | some fr => { ev with duration := (ev.date + ev.duration * 60 * 1000 - firstResumeDate) / 60 / 1000, startedAt := fr, date := firstResumeDate }
        | none => ev
    else ev
  -- lines 105-111. QUIRK Q7: `lastSuspendTime` is a timestamp string, so these
  -- numeric comparisons are with NaN and never hold for ISO timestamps.
  let ev :=
    if currentlySuspended && ev.date + ev.duration * 60 * 1000 >ʲ lastSuspendTimeNum then
      if ev.date >ʲ lastSuspendTimeNum then { ev with duration := 0 }
      else { ev with duration := (firstResumeDate - ev.date) / 60 / 1000 }
    else ev
  if ev.duration =ʲ 0 then [ev]
  else
    -- lines 120-156: for each suspend, adjust every event (the array grows while iterating)
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

/-! #### Stages of `calcTempTreatments`

`calcTempTreatments` is split into stages with explicit inputs and outputs. Each loop
of history.js is a fold over a list or a recursion on a fuel bound, so that the kernel
can unfold every stage. -/

/-- Lines 184-200: the pump suspends and the pump resumes of the history, in history order.
    They are not sorted. -/
def collectSuspends (hist : List PumpRecord) (nowMs : Int) : List Suspend × List Suspend :=
  hist.foldl (fun (sus, res) cur =>
    let t := recTime cur.toPumpFields nowMs
    let d : JsNum := match t with | some t => .fin t | none => .nan
    if cur.type_ == some "PumpSuspend" then
      (sus ++ [{ timestamp := cur.timestamp, startedAt := t, date := d }], res)
    else if cur.type_ == some "PumpResume" then
      (sus, res ++ [{ timestamp := cur.timestamp, startedAt := t, date := d }])
    else (sus, res)) ([], [])

/-- Lines 221-225, the inner `for` loop that advances `j` to the first resume after the
    suspend: the first index `k ≥ j` with `resumes[k].date > d`, or `resumes.size`. The loop
    runs at most `resumes.size` times, so the fuel `resumes.size` never stops it. -/
def nextResume (resumes : Array Suspend) (d : JsNum) : Nat → Nat → Nat
  | 0, j => j
  | fuel + 1, j =>
    if j < resumes.size && !(resumes[j]!.date >ʲ d) then nextResume resumes d fuel (j + 1) else j

/-- The state of the suspend-matching loop, lines 217-241: the suspends with the durations
    set so far, the resume index `j`, `currentlySuspended`, `lastSuspendTime`, and `iStop`,
    the suspend index at which the loop broke, or the number of suspends if it did not. -/
structure SuspendMatch where
  suspends : Array Suspend
  j : Nat := 0
  currentlySuspended : Bool := false
  lastSuspendTime : Option String := none
  iStop : Nat
  deriving Repr, Inhabited

/-- Lines 220-241: give each suspend the duration until the next resume. The loop over
    the suspend indices `is` stops (`break`, line 236) at the first suspend with no
    later resume. -/
def matchSuspends (resumes : Array Suspend) : List Nat → SuspendMatch → SuspendMatch
  | [], m => m
  | i :: is, m =>
    let j := nextResume resumes m.suspends[i]!.date resumes.size m.j
    if j ≥ resumes.size && !m.currentlySuspended then
      { m with j := j, currentlySuspended := true, lastSuspendTime := m.suspends[i]!.timestamp, iStop := i }
    else
      let s := m.suspends[i]!
      matchSuspends resumes is
        { m with j := j, suspends := m.suspends.set! i { s with duration := some ((resumes[j]!.date - s.date) / 60 / 1000) } }

/-- Lines 265-268: the fields that history.js reads from a record: the nested `bolus`
    object of a `{bolus: {_type: "Bolus"}}` record, else the record itself. -/
def recordFields (r : PumpRecord) : PumpFields :=
  match r.bolus with
  | some b => if b.type_ == some "Bolus" then b else r.toPumpFields
  | none => r.toPumpFields

/-- Lines 269-271: write the mutated fields back into the record they came from, the nested
    `bolus` object or the record itself. -/
def withFields (r : PumpRecord) (cur : PumpFields) : PumpRecord :=
  match r.bolus with
  | some b => if b.type_ == some "Bolus" then { r with bolus := some cur } else { r with toPumpFields := cur }
  | none => { r with toPumpFields := cur }

/-- What one history record contributes, lines 283-367. -/
inductive RecordKind where
  /-- a bolus treatment -/
  | bolus (t : Treatment)
  /-- a temp basal event -/
  | temp (e : TempEvent)
  /-- a percent temp: `continue` at line 341, before the zero temp of lines 368-379 -/
  | percent
  /-- nothing: a record of another kind, or a future bolus, lines 287-289 -/
  | other
  deriving Repr, Inhabited

/-- Lines 283-367: classify the record `cur` at index `i`. The search for the matching
    `"TempBasalDuration"` record, lines 346-354, reads `hist`, the history after the in-place
    mutation of lines 269-271. -/
def classifyRecord (hist : Array PumpRecord) (i : Nat) (cur : PumpFields) (nowMs : Int) : RecordKind :=
  let now : JsNum := .fin nowMs
  let ts := recTime cur nowMs
  let tsJ : JsNum := match ts with | some t => .fin t | none => .nan
  let createdMs : Option Int := match cur.created_at with | some _ => cur.created_atMs | none => some nowMs
  let createdJ : JsNum := match createdMs with | some t => .fin t | none => .nan
  if cur.type_ == some "Bolus" then
    if tsJ >ʲ now then .other    -- future bolus: ignored (lines 287-289)
    else .bolus { insulin := cur.amount, date := tsJ, startedAt := ts, timestamp := cur.timestamp }
  else if cur.eventType == some "Meal Bolus" || cur.eventType == some "Correction Bolus" ||
          cur.eventType == some "Snack Bolus" || cur.eventType == some "Bolus Wizard" then
    .bolus { insulin := cur.insulin, date := createdJ, startedAt := createdMs, timestamp := cur.created_at }
  else if cur.enteredBy == some "xdrip" then
    .bolus { insulin := cur.insulin, date := tsJ, startedAt := ts, timestamp := cur.timestamp }
  else if cur.enteredBy == some "HAPP_App" && cur.insulin.truthyN then
    .bolus { insulin := cur.insulin, date := createdJ, startedAt := createdMs, timestamp := cur.created_at }
  else if cur.eventType == some "Temp Basal" && (cur.enteredBy == some "HAPP_App" || cur.enteredBy == some "openaps://AndroidAPS") then
    .temp { rate := cur.absolute.js, duration := cur.duration.js, startedAt := createdMs.getD 0, date := createdJ, timestamp := cur.created_at, timestampMs := createdMs, durationNull := cur.durationNull }
  else if cur.eventType == some "Temp Basal" then
    let rate := if cur.amount.isSome then cur.amount.js / cur.duration.js * 60 else cur.rate.js
    .temp { rate, duration := cur.duration.js, startedAt := ts.getD 0, date := tsJ, timestamp := cur.timestamp, timestampMs := ts, durationNull := cur.durationNull }
  else if cur.type_ == some "TempBasal" then
    if cur.temp == some "percent" then .percent
    else
      -- lines 346-354: find the matching TempBasalDuration record
      let duration : JsNum :=
        if i > 0 && hist[i-1]!.timestamp == cur.timestamp && hist[i-1]!.type_ == some "TempBasalDuration" then
          hist[i-1]!.durationMin.js
        else
          match hist.toList.find? (fun r => r.timestamp == cur.timestamp && r.type_ == some "TempBasalDuration") with
          | some r => r.durationMin.js
          | none => .nan
      .temp { rate := cur.rate.js, duration, startedAt := ts.getD 0, date := tsJ, timestamp := cur.timestamp, timestampMs := ts }
  else .other

/-- The state of the record scan, lines 263-380. -/
structure ScanState where
  /-- the history, with the in-place mutations of lines 269-271 so far -/
  history : Array PumpRecord
  temps : Array TempEvent := #[]
  boluses : Array Treatment := #[]
  lastRecordTime : JsNum
  deriving Repr, Inhabited

/-- The zero temp starting one minute from now, lines 368-379. -/
def zeroTempEvent (nowMs : Int) (zeroTempDuration : Option JsNum) : TempEvent :=
  { rate := 0, startedAt := nowMs + 60000, date := .fin (nowMs + 60000), duration := zeroTempDuration.getD 0 }

/-- One iteration of the record scan, lines 264-379, for the record at index `i`. A record
    later than `lastRecordTime`, initially now and then the time of the last kept record, is
    skipped (`continue`, line 279). -/
def scanRecord (nowMs : Int) (zeroTempDuration : Option JsNum) (st : ScanState) (i : Nat) : ScanState :=
  let rec0 := st.history[i]!
  let cur0 := recordFields rec0
  -- lines 269-271: in-place mutation of the record
  let cur := if cur0.created_at.isSome then { cur0 with timestamp := cur0.created_at, timestampMs := cur0.created_atMs } else cur0
  let hist := if cur0.created_at.isSome then st.history.set! i (withFields rec0 cur) else st.history
  let currentRecordTime : JsNum := match recTime cur nowMs with | some t => .fin t | none => .nan
  if currentRecordTime >ʲ st.lastRecordTime then { st with history := hist }
  else
    let zero := zeroTempEvent nowMs zeroTempDuration
    match classifyRecord hist i cur nowMs with
    | .bolus b => { history := hist, temps := st.temps.push zero, boluses := st.boluses.push b, lastRecordTime := currentRecordTime }
    | .temp e => { history := hist, temps := (st.temps.push e).push zero, boluses := st.boluses, lastRecordTime := currentRecordTime }
    | .percent => { history := hist, temps := st.temps, boluses := st.boluses, lastRecordTime := currentRecordTime }
    | .other => { history := hist, temps := st.temps.push zero, boluses := st.boluses, lastRecordTime := currentRecordTime }

/-- Lines 263-380: scan the records in order. -/
def scanRecords (nowMs : Int) (zeroTempDuration : Option JsNum) (hist : Array PumpRecord) : ScanState :=
  (List.range hist.size).foldl (scanRecord nowMs zeroTempDuration) { history := hist, lastRecordTime := .fin nowMs }

/-- Lines 386-394, the loop over the sorted temps: a temp that overlaps the next one is cut
    at the next one's start, and that next temp is removed if its duration is `null`. Each
    pass increments `i` and no pass grows the array, so fuel `th.size` or more never stops
    the loop. -/
def trimTemps : Nat → Nat → Array TempEvent → Array TempEvent
  | 0, _, th => th
  | fuel + 1, i, th =>
    if i + 1 < th.size then
      let th :=
        if th[i]!.date + th[i]!.duration * 60 * 1000 >ʲ th[i+1]!.date then
          let th := th.set! i { th[i]! with duration := (th[i+1]!.date - th[i]!.date) / 60 / 1000 }
          if th[i+1]!.durationNull then th.eraseIdxIfInBounds (i + 1) else th
        else th
      trimTemps fuel (i + 1) th
    else th

/-- Lines 396-503: split the temps at basal schedule changes and, with
    `suspend_zeros_iob`, around suspends. Returns the unsorted split history and the temp
    history as history.js returns it, with the aliased mutations of quirk Q8. -/
def splitStage (inp : HistoryInputs) (thO : Array TempEvent) (suspends : List Suspend)
    (firstResumeMs : Option Int) (suspendedPrior currentlySuspended : Bool)
    (lastSuspendTime : Option String) : List TempEvent × List TempEvent :=
  let p := inp.profile
  let tz := inp.tzOffsetMin
  let nowMs := inp.clockMs
  let now : JsNum := .fin nowMs
  let tempHistoryFinal := thO.toList
  let splitters := p.basalprofile.map (·.minutes)
  let splitHistoryByBasal := tempHistoryFinal.flatMap (fun o => splitTimespan o splitters tz)
  -- lines 424-503: suspends
  let lastSuspendTimeNum : JsNum := match lastSuspendTime with | some s => numberOfString s | none => .nan
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

/-- Lines 513-567: each temp of `splitHistory` with positive duration becomes boluses of
    0.05 U, spaced evenly over the temp and appended to `acc`. The boluses are −0.05 U when
    the temp rate is below the scheduled basal times the sensitivity ratio. -/
def tempBolusesOf (inp : HistoryInputs) (splitHistory : List TempEvent) (acc : Array Treatment) : Array Treatment :=
  let p := inp.profile
  let tz := inp.tzOffsetMin
  splitHistory.foldl (fun acc item =>
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
        (List.range n).foldl (fun acc k =>
          acc.push { insulin := some tempBolusSize, date := item.date + .fin (k : Nat) * tempBolusSpacing * 60 * 1000 }) acc
      | .nan => acc
    else acc) acc

/-- `calcTempTreatments(inputs, zeroTempDuration)`, history.js lines 161-571. -/
def calcTempTreatments (inp : HistoryInputs) (zeroTempDuration : Option JsNum) : HistoryOut :=
  let nowMs := inp.clockMs
  let pumpHistory : Array PumpRecord := (inp.history ++ (inp.history24.getD [])).toArray
  -- lines 184-200: suspends and resumes
  let sr := collectSuspends pumpHistory.toList nowMs
  let pumpSuspends := sortByKey (·.date) sr.1
  let resumesA := (sortByKey (·.date) sr.2).toArray
  let firstResumeMs : Option Int := if h : 0 < resumesA.size then resumesA[0].startedAt else none
  let suspendedPrior : Bool :=
    if h : 0 < resumesA.size then pumpSuspends.isEmpty || resumesA[0].date <ʲ (pumpSuspends.head!).date else false
  -- lines 217-241: match resumes with suspends
  let susA0 := pumpSuspends.toArray
  let m := matchSuspends resumesA (List.range susA0.size) { suspends := susA0, iStop := susA0.size }
  -- lines 255-259: truncate extra suspends
  let susA := if m.iStop + 1 < m.suspends.size then m.suspends.extract 0 (m.iStop + 1) else m.suspends
  let suspends := susA.toList
  -- lines 263-380: relevant events
  let sc := scanRecords nowMs zeroTempDuration pumpHistory
  -- lines 384-394: sort and trim overlapping temps
  let th0 := (sortByKey (·.date) sc.temps.toList).toArray
  let th := trimTemps (th0.size * 2 + 2) 0 th0
  let thO := (th.toList.zipIdx.map fun (e, k) => { e with origin := some k }).toArray
  -- lines 396-503: split at basal schedule changes and around suspends
  let sp := splitStage inp thO suspends firstResumeMs suspendedPrior m.currentlySuspended m.lastSuspendTime
  let splitHistory := sortByKey (·.date) sp.1
  -- lines 509-567: temp basals → 0.05 U micro-boluses
  let tempBoluses := tempBolusesOf inp splitHistory sc.boluses
  -- lines 568-570
  let tempAsTreatments : List Treatment := sp.2.map fun e =>
    { date := e.date, rate := some e.rate, duration := some e.duration, timestamp := e.timestamp,
      startedAt := some e.startedAt }
  { treatments := sortByKey (·.date) (tempBoluses.toList ++ tempAsTreatments), history := sc.history.toList }

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

/-- One step of the scan for `lastBolusTime` and `lastTemp` over the treatments,
    index.js lines 45-59. -/
def lastStep (acc : JsNum × LastTempOut) (t : Treatment) : JsNum × LastTempOut :=
  let (lbt, lt) := acc
  if t.insulin.truthyN && t.startedAt.isSome then
    (JsNum.max lbt (.fin t.startedAt.get!), lt)
  else if t.rate.isSome && t.duration.truthyN then
    if t.date >ʲ lt.date then
      (lbt, { date := t.date, rate := t.rate, duration := some (mathRound (t.duration.js * 100) / 100),
              timestamp := t.timestamp, startedAt := t.startedAt })
    else (lbt, lt)
  else (lbt, lt)

/-- `generate(inputs, currentIOBOnly)`, index.js lines 8-82. -/
def generate (inp : HistoryInputs) (currentIOBOnly : Bool := false) : IobOut :=
  let r1 := calcTempTreatments inp none
  let treatments := r1.treatments
  -- the second call sees the history as mutated by the first
  let r2 := calcTempTreatments { inp with history := r1.history, history24 := none } (some 240)
  let treatmentsWithZeroTemp := r2.treatments
  let last := treatments.foldl lastStep ((0 : JsNum), ({ date := 0 } : LastTempOut))
  let lastBolusTime := last.1
  let lastTemp := last.2
  let iStop := if currentIOBOnly then 1 else 4 * 60
  let ticks := (List.range ((iStop + 4) / 5)).map fun k =>
    let t := inp.clockMs + (k * 5 : Nat) * 60000
    { sum := iobTotal treatments inp.profile t, withZeroTemp := iobTotal treatmentsWithZeroTemp inp.profile t }
  { ticks, lastBolusTime, lastTemp }

end LeanAID.Iob
