/-
  LeanAID.Time.System — the transition system of the timing properties
  (docs/timing-plan.md, section 5, item T2).

  First milestone: a fixed profile and atomic cycles. A step is an ordered list
  of events at one time: environment events (CGM readings, user boluses) and then
  at most one cycle. In a cycle the loop reads its inputs, `LeanAID.step` decides,
  and the pump accepts or loses the whole command. The pump validates an accepted
  command and rejects it if a value is non-finite or out of range.

  The inputs of a cycle are fixed by the run:
  - `clock.now` is the step time,
  - the profile is the fixed profile with `current_basal` from its schedule,
  - `iob_data` is `Iob.generate` on the initial history plus the encoded actions
    that the pump accepted before the cycle (newest first, as pump history is),
  - `currenttemp` comes from the pump state,
  - `glucose_status` is `Glucose.getLastGlucose` on the readings so far.
  Meal data, autosens data and `microBolusAllowed` are free inputs of the run.

  Out of scope for now (plan, section 6): profile changes, concurrent loops,
  delayed execution, lost acknowledgements, forged commands. The pump is an
  idealized exactly-once pump: a command is executed whole or not at all.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import LeanAID.Time.Run
import LeanAID.Core.Step
import LeanAID.Core.Iob
import LeanAID.Core.Glucose

namespace LeanAID.Time

open LeanAID LeanAID.Iob

/-! ### Events -/

/-- A CGM reading. -/
structure Reading where
  /-- the glucose value, mg/dL -/
  value : JsNum
  /-- the true time of the reading, ms -/
  trueTime : Int
  /-- the date the CGM records for it, ms (`none`: undated, F-11) -/
  recorded : Option JsNum
  deriving Repr

/-- What happened to the command of a cycle. Lost means never executed. -/
inductive Outcome where
  | accepted
  | lost
  deriving Repr, DecidableEq

/-- The events of a run. -/
inductive Event where
  | reading (r : Reading)
  /-- a user bolus (meal or correction), executed at once -/
  | userBolus (u : Rat)
  /-- one loop cycle: the inputs, the result of `LeanAID.step`, and the outcome -/
  | cycle (inp : DBInputs) (res : Result) (out : Outcome)

def Event.isCycle : Event → Bool
  | .cycle .. => true
  | _ => false

/-! ### Validation -/

/-- A command after validation: an optional temp (rate in U/h, duration in whole
    minutes) and an optional bolus (units). -/
structure Cmd where
  temp : Option (Rat × Int) := none
  bolus : Option Rat := none
  deriving Repr, DecidableEq

/-- The pump accepts a temp duration of 0 (cancel) or 30 to 120 whole minutes. -/
def validDuration (d : Rat) : Bool := d.den == 1 && (d == 0 || (30 ≤ d && d ≤ 120))

/-- The temp part of a result. `none` = the result sets no temp; `some none` = rejected. -/
def validateTemp (res : Result) : Option (Option (Rat × Int)) :=
  match res.rate, res.duration with
  | none, none => some none
  | some (.fin r), some (.fin d) => if 0 ≤ r && validDuration d then some (some (r, d.num)) else none
  | _, _ => none

/-- The bolus part of a result: `some none` = no bolus, `none` = rejected. -/
def validateBolus (res : Result) : Option (Option Rat) :=
  match res.units with
  | none => some none
  | some (.fin u) => if 0 < u then some (some u) else none
  | some .nan => none

/-- Pump validation: the whole command is rejected (`none`) if any part is
    non-finite or out of range. An error result carries no command. -/
def validate (res : Result) : Option Cmd := do
  let t ← validateTemp res
  let b ← validateBolus res
  pure { temp := t, bolus := b }

/-! ### Pump state -/

/-- An accepted temp basal: rate (U/h), start and deadline (ms). -/
structure Temp where
  rate : Rat
  start : Int
  deadline : Int
  deriving Repr, DecidableEq

/-- An accepted action, for the pump history. -/
inductive Action where
  | temp (time : Int) (rate : Rat) (minutes : Int)
  | bolus (time : Int) (units : Rat) (smb : Bool)
  deriving Repr, DecidableEq

/-- The state after a prefix of a run. -/
structure PState where
  /-- the last accepted temp, `none` after a cancel. It may have expired. -/
  temp : Option Temp
  /-- accepted actions, newest first -/
  log : List Action := []
  /-- CGM readings, newest first -/
  readings : List Reading := []
  /-- cycles whose command the pump rejected (time), newest first -/
  rejected : List Int := []

/-- The fixed environment of a run. -/
structure Env where
  /-- the fixed profile; `basalprofile` is the pump schedule -/
  profile : Profile
  /-- local time-zone offset, minutes -/
  tz : Int := 0
  /-- pump history before the run, newest first -/
  initHistory : List PumpRecord := []
  /-- a temp running when the run starts -/
  initTemp : Option Temp := none

/-- The scheduled basal at time `t` (ms): oref0's `basalLookup` on the schedule. -/
def Env.schedJs (env : Env) (t : Int) : Option JsNum :=
  basalLookup env.profile.basalprofile (.fin t) env.tz

/-- The scheduled rate as a number (0 when the lookup gives none or NaN). -/
def Env.sched (env : Env) (t : Int) : Rat :=
  match env.schedJs t with
  | some (.fin r) => r
  | _ => 0

/-- The profile a cycle at time `t` sees: the fixed profile with `current_basal`
    from the schedule. -/
def Env.profileAt (env : Env) (t : Int) : Profile :=
  { env.profile with current_basal := env.schedJs t }

def Env.init (env : Env) : PState := { temp := env.initTemp }

/-- Apply a validated command at time `t`. Duration 0 cancels the temp. -/
def applyCmd (t : Int) (s : PState) (c : Cmd) : PState :=
  let s := match c.temp with
    | none => s
    | some (r, d) =>
      { s with temp := if d = 0 then none else some { rate := r, start := t, deadline := t + d * 60000 },
               log := .temp t r d :: s.log }
  match c.bolus with
  | none => s
  | some u => { s with log := .bolus t u true :: s.log }

/-- The effect of one event at time `t`. -/
def applyEvent (t : Int) (s : PState) : Event → PState
  | .reading r => { s with readings := r :: s.readings }
  | .userBolus u => if 0 < u then { s with log := .bolus t u false :: s.log } else s
  | .cycle _ res out =>
    match out with
    | .lost => s
    | .accepted =>
      match validate res with
      | some c => applyCmd t s c
      | none => { s with rejected := t :: s.rejected }

/-- The effect of a step. -/
def applyStep (s : PState) (st : Step Event) : PState := st.events.foldl (applyEvent st.time) s

/-- The pump state after the steps at or before `t`. -/
def pumpAt (env : Env) (r : Run Event) (t : Int) : PState := stateAt env.init applyStep r t

/-- The rate (U/h) the pump runs at time `k` in state `s`: the temp until its
    deadline, then the scheduled basal. -/
def rateIn (env : Env) (s : PState) (k : Int) : Rat :=
  match s.temp with
  | some tp => if k < tp.deadline then tp.rate else env.sched k
  | none => env.sched k

/-- The pump rate at time `k` of a run. Temp expiry is a change of this function,
    not an event. -/
def rateAt (env : Env) (r : Run Event) (k : Int) : Rat := rateIn env (pumpAt env r k) k

/-! ### Inputs of a cycle -/

/-- The pump-history records of one accepted action, newest first, in the format
    of oref0's Medtronic pump history (as `sim/harness.py` writes it). The
    timestamp string is the decimal millisecond time, so that a `TempBasal` and its
    `TempBasalDuration` share it. -/
def encodeAction : Action → List PumpRecord
  | .temp t r d =>
    [{ type_ := some "TempBasal", temp := some "absolute", rate := some (.fin r),
       timestamp := some (toString t), timestampMs := some t },
     { type_ := some "TempBasalDuration", durationMin := some (.fin d),
       timestamp := some (toString t), timestampMs := some t }]
  | .bolus t u _ =>
    [{ type_ := some "Bolus", amount := some (.fin u), timestamp := some (toString t), timestampMs := some t }]

/-- The pump history a cycle sees: the encoded actions, newest first, then the
    initial history. -/
def history (env : Env) (s : PState) : List PumpRecord :=
  s.log.flatMap encodeAction ++ env.initHistory

/-- The IOB array as `determine_basal` receives it (as `App.Serve.iobInput`). -/
def iobInputOf (o : IobOut) : IobInput :=
  .array (o.ticks.zipIdx.map fun (t, k) =>
    { iob := some t.sum.iob, activity := some t.sum.activity,
      iobWithZeroTemp := some (some t.withZeroTemp.activity),
      lastTemp := if k == 0 then some { date := some o.lastTemp.date, rate := o.lastTemp.rate,
                                         duration := o.lastTemp.duration } else none,
      lastBolusTime := if k == 0 then some o.lastBolusTime else none })

/-- `Iob.generate` at time `t` on the history of state `s`. -/
def iobOut (env : Env) (s : PState) (t : Int) (auto : Option Autosens) : IobOut :=
  generate { history := history env s, profile := env.profileAt t, autosens := auto,
             clockMs := t, tzOffsetMin := env.tz }

/-- `currenttemp` as the pump reports it at time `t`: the running temp with its
    remaining minutes rounded up, or no temp (duration 0, rate 0). -/
def currentTempAt (s : PState) (t : Int) : CurrentTemp :=
  match s.temp with
  | some tp =>
    if t < tp.deadline then
      { duration := some (.fin ((tp.deadline - t + 59999) / 60000 : Int)), rate := some (.fin tp.rate),
        temp := some "absolute" }
    else { duration := some 0, rate := some 0, temp := some "absolute" }
  | none => { duration := some 0, rate := some 0, temp := some "absolute" }

/-- The CGM entries of the readings (newest first). -/
def entries (s : PState) : List Glucose.Entry :=
  s.readings.map fun r => { glucose := some r.value, date := r.recorded }

/-- A cycle at time `t` in state `s` (the state after the earlier events of the
    run, including those earlier in the same step) is legal when its inputs are
    those of the run and its result is `LeanAID.step` of them. -/
structure LegalCycle (env : Env) (t : Int) (s : PState) (inp : DBInputs) (res : Result) : Prop where
  now : inp.clock.now = t
  tz : inp.clock.tzOffsetMin = env.tz
  profile : inp.profile = some (env.profileAt t)
  iob : inp.iob_data = some (iobInputOf (iobOut env s t inp.autosens_data))
  currenttemp : inp.currenttemp = some (currentTempAt s t)
  glucose : inp.glucose_status = Glucose.getLastGlucose (entries s)
  result : res = LeanAID.step inp

/-- The events of one step are legal from state `s`. -/
def LegalEvents (env : Env) (t : Int) : PState → List Event → Prop
  | _, [] => True
  | s, e :: es =>
    (match e with
     | .cycle inp res _ => LegalCycle env t s inp res
     | _ => True) ∧ LegalEvents env t (applyEvent t s e) es

/-- Environment events first, then at most one cycle. -/
def CycleLast : List Event → Prop
  | [] => True
  | [_] => True
  | e :: es => e.isCycle = false ∧ CycleLast es

/-- The steps of a run are legal from state `s`. -/
def LegalFrom (env : Env) : PState → Run Event → Prop
  | _, [] => True
  | s, st :: r => st.events ≠ [] ∧ CycleLast st.events ∧ LegalEvents env st.time s st.events ∧
      LegalFrom env (applyStep s st) r

/-- A legal run of the T2 model. -/
structure Legal (env : Env) (r : Run Event) : Prop where
  increasing : Increasing r
  steps : LegalFrom env env.init r

/-! ### The cycles of a run -/

/-- A cycle with its time and the state just before it. -/
structure CycleAt where
  time : Int
  pre : PState
  inp : DBInputs
  res : Result
  out : Outcome

/-- The cycles among the events of one step. -/
def cyclesEvents (t : Int) : PState → List Event → List CycleAt
  | _, [] => []
  | s, e :: es =>
    (match e with
     | .cycle inp res out => [{ time := t, pre := s, inp, res, out }]
     | _ => []) ++ cyclesEvents t (applyEvent t s e) es

/-- The cycles of a run from state `s`, in order. -/
def cyclesFrom : PState → Run Event → List CycleAt
  | _, [] => []
  | s, st :: r => cyclesEvents st.time s st.events ++ cyclesFrom (applyStep s st) r

def cycles (env : Env) (r : Run Event) : List CycleAt := cyclesFrom env.init r

theorem legal_cyclesEvents {env : Env} {t : Int} :
    ∀ {s : PState} {es : List Event}, LegalEvents env t s es →
      ∀ c ∈ cyclesEvents t s es, c.time = t ∧ LegalCycle env c.time c.pre c.inp c.res
  | _, [], _, c, h => by simp [cyclesEvents] at h
  | s, e :: es, hl, c, hc => by
    simp only [cyclesEvents, List.mem_append] at hc
    rcases hc with hc | hc
    · cases e with
      | cycle inp res out =>
        simp only [List.mem_singleton] at hc; subst hc
        exact ⟨rfl, hl.1⟩
      | _ => simp at hc
    · exact legal_cyclesEvents hl.2 c hc

theorem legal_cyclesFrom {env : Env} :
    ∀ {s : PState} {r : Run Event}, LegalFrom env s r →
      ∀ c ∈ cyclesFrom s r, LegalCycle env c.time c.pre c.inp c.res
  | _, [], _, c, h => by simp [cyclesFrom] at h
  | s, st :: r, hl, c, hc => by
    simp only [cyclesFrom, List.mem_append] at hc
    rcases hc with hc | hc
    · exact (legal_cyclesEvents hl.2.2.1 c hc).2
    · exact legal_cyclesFrom hl.2.2.2 c hc

/-- **Every cycle of a legal run is legal**: its inputs are those of the run and its
    result is `LeanAID.step` of them. This lifts per-call theorems to runs. -/
theorem Legal.cycle {env : Env} {r : Run Event} (h : Legal env r) :
    ∀ c ∈ cycles env r, LegalCycle env c.time c.pre c.inp c.res :=
  legal_cyclesFrom h.steps

end LeanAID.Time
