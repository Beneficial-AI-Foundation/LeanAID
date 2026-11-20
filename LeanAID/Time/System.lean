import LeanAID.Time.Run
import LeanAID.Core.Step
import LeanAID.Core.Iob
import LeanAID.Core.Glucose

/-!
# The transition system of a closed loop

**Setting.** A fixed environment `env : Env` holds the profile, the time-zone offset, the
pump history before the run and a temp running at its start. A run `r : Run Event` is a list
of steps whose events are CGM readings, user boluses and loop cycles. A legal step is
nonempty and holds environment events followed by at most one cycle (`CycleLast`).

- In a cycle the loop computes `LeanAID.step inp`, and the pump either receives the whole
  command or loses it. `validate` rejects a received command that has a NaN or out-of-range
  value, or a rate without a duration; the rejection is recorded in `PState.rejected`.
  `applyCmd` executes a validated command at once.
- `rateIn env s k` is the pump rate at millisecond `k`: the stored temp before its
  deadline, and the schedule `env.sched k` otherwise.
- `LegalCycle env t s inp res` fixes the inputs of a cycle at time `t` from the state `s`
  before it: `clock.now = t`, `clock.tzOffsetMin = env.tz`, the profile `env.profileAt t`,
  `iob_data` from `Iob.generate` on the history of the accepted actions, `currenttemp` from
  the stored temp, `glucose_status` from `Glucose.getLastGlucose` on the readings, and
  `res = LeanAID.step inp`. `meal_data`, `autosens_data`, `reservoir_data` and
  `microBolusAllowed` are free.
- `Legal env r` states that the step times of `r` increase and every step is legal from the
  state before it.

**Theorem** (`Legal.cycle`). Every cycle of a legal run satisfies `LegalCycle`.

**Restrictions of the model.**
- The controller's `current_basal` and the pump's fallback rate both come from
  `env.profile.basalprofile`. In oref0 an autotuned profile can replace the controller's
  basals (`bin/oref0-get-profile.js:239`) while the pump keeps its programmed schedule;
  the timing theorems do not cover that configuration.
- The pump history is a list of decoded `PumpRecord`s (`encodeAction`). Its timestamp
  strings are decimal milliseconds, not the ISO strings of a real pump history, and
  `timestampMs` is set directly. No theorem relates these records to parsed pump history.
- `Reading.trueTime` does not enter any cycle input: the controller sees `recorded` only.
- Out of scope: profile changes, concurrent loops, delayed execution, lost
  acknowledgements, forged commands. A command executes whole or not at all.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Iob

/-! ### Events -/

/-- A CGM reading. -/
structure Reading where
  /-- the glucose value, mg/dL -/
  value : JsNum
  /-- the true time of the reading, ms -/
  trueTime : Int
  /-- the date the CGM records for the reading, ms. `none` is an undated reading, which
      disables oref0's staleness check (F-11). -/
  recorded : Option JsNum
  deriving Repr

/-- Whether the pump receives the command of a cycle. An `accepted` command goes to
    `validate`; a `lost` command is never executed. -/
inductive Outcome where
  | accepted
  | lost
  deriving Repr, DecidableEq

/-- The events of a run. -/
inductive Event where
  | reading (r : Reading)
  /-- a user bolus of `u` units, for a meal or a correction. It executes at once when
      `u > 0` and is ignored otherwise. -/
  | userBolus (u : Rat)
  /-- one loop cycle: the inputs, the controller's result and the outcome. A legal run
      has `res = LeanAID.step inp` (`LegalCycle`). -/
  | cycle (inp : DBInputs) (res : Result) (out : Outcome)

/-- Whether an event is a cycle. -/
def Event.isCycle : Event → Bool
  | .cycle .. => true
  | _ => false

/-! ### Validation -/

/-- A validated command: an optional temp `(r, d)` with rate `r` in U/h and duration `d` in
    whole minutes, and an optional bolus in units. -/
structure Cmd where
  temp : Option (Rat × Int) := none
  bolus : Option Rat := none
  deriving Repr, DecidableEq

/-- The pump accepts a temp duration of 0 (cancel) or 30 to 120 whole minutes. -/
def validDuration (d : Rat) : Bool := d.den == 1 && (d == 0 || (30 ≤ d && d ≤ 120))

/-- The temp part of a result. It is `some none` if the result sets neither rate nor
    duration, and `some (some (r, d))` if the rate `r` is finite with `r ≥ 0` and the
    duration `d` is finite with `validDuration d`. Otherwise it is `none`, a rejection:
    a NaN value, a negative rate, an invalid duration, or only one of rate and duration. -/
def validateTemp (res : Result) : Option (Option (Rat × Int)) :=
  match res.rate, res.duration with
  | none, none => some none
  | some (.fin r), some (.fin d) => if 0 ≤ r && validDuration d then some (some (r, d.num)) else none
  | _, _ => none

/-- The bolus part of a result. It is `some none` if the result sets no units,
    `some (some u)` for finite units `u > 0`, and `none`, a rejection, for NaN or `u ≤ 0`. -/
def validateBolus (res : Result) : Option (Option Rat) :=
  match res.units with
  | none => some none
  | some (.fin u) => if 0 < u then some (some u) else none
  | some .nan => none

/-- The validated command of a result, or `none` if `validateTemp` or `validateBolus`
    rejects it. Only the fields `rate`, `duration` and `units` are read. -/
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
  /-- the times of the cycles whose command the pump received and `validate` rejected,
      newest first -/
  rejected : List Int := []

/-- The fixed environment of a run. -/
structure Env where
  /-- the fixed profile; its `basalprofile` is both the controller's basal schedule and
      the pump's fallback schedule -/
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

/-- The scheduled rate at time `t`, in U/h. It is 0 when the lookup gives `none` or NaN. -/
def Env.sched (env : Env) (t : Int) : Rat :=
  match env.schedJs t with
  | some (.fin r) => r
  | _ => 0

/-- The profile a cycle at time `t` sees: the fixed profile with `current_basal`
    from the schedule. -/
def Env.profileAt (env : Env) (t : Int) : Profile :=
  { env.profile with current_basal := env.schedJs t }

/-- The initial state: the initial temp, no actions, no readings. -/
def Env.init (env : Env) : PState := { temp := env.initTemp }

/-- The state after executing a validated command at time `t`. A temp `(r, d)` with
    `d ≠ 0` becomes the stored temp, at rate `r` from `t` to the deadline `t + 60000·d` ms;
    a temp with `d = 0` cancels the stored temp. A bolus of `u` units is logged as an SMB.
    Each executed part is prepended to the log. -/
def applyCmd (t : Int) (s : PState) (c : Cmd) : PState :=
  let s := match c.temp with
    | none => s
    | some (r, d) =>
      { s with temp := if d = 0 then none else some { rate := r, start := t, deadline := t + d * 60000 },
               log := .temp t r d :: s.log }
  match c.bolus with
  | none => s
  | some u => { s with log := .bolus t u true :: s.log }

/-- The effect of one event at time `t`. A reading is prepended to the readings. A user
    bolus `u > 0` is logged as a non-SMB bolus; `u ≤ 0` changes nothing. A lost cycle
    changes nothing. An accepted cycle applies its command if `validate` accepts it, and
    otherwise records `t` in `rejected`. -/
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

/-- The rate of the stored temp at time `k` in state `s` if `k` is before its deadline.
    It is `none` when there is no stored temp or the deadline has passed. -/
def tempRate (s : PState) (k : Int) : Option Rat :=
  match s.temp with
  | some tp => if k < tp.deadline then some tp.rate else none
  | none => none

/-- The rate (U/h) the pump runs at time `k` in state `s`: the temp until its
    deadline, then the scheduled basal. -/
def rateIn (env : Env) (s : PState) (k : Int) : Rat := (tempRate s k).getD (env.sched k)

/-- The pump rate at time `k` of a run. Temp expiry is a change of this function,
    not an event. -/
def rateAt (env : Env) (r : Run Event) (k : Int) : Rat := rateIn env (pumpAt env r k) k

/-! ### Inputs of a cycle -/

/-- The pump-history records of an accepted action, in the record types of oref0's
    Medtronic history. A temp gives a `TempBasal` record followed by a `TempBasalDuration`
    record; a bolus gives one `Bolus` record, without its SMB flag. The timestamp string is
    the decimal millisecond time and `timestampMs` is set to that time; a real history
    carries ISO timestamp strings. -/
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

/-- The `IobInput` array of an `IobOut`, with `lastTemp` and `lastBolusTime` on its first
    tick (as `App.Serve.iobInput`). -/
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

/-- The `CurrentTemp` of state `s` at time `t`: the stored temp with its remaining
    minutes rounded up, or rate 0 and duration 0 if there is none or it has expired. -/
def currentTempAt (s : PState) (t : Int) : CurrentTemp :=
  match s.temp with
  | some tp =>
    if t < tp.deadline then
      { duration := some (.fin ((tp.deadline - t + 59999) / 60000 : Int)), rate := some (.fin tp.rate),
        temp := some "absolute" }
    else { duration := some 0, rate := some 0, temp := some "absolute" }
  | none => { duration := some 0, rate := some 0, temp := some "absolute" }

/-- The CGM entries of the readings, newest first. Each entry is dated by the reading's
    `recorded` date, not its `trueTime`. -/
def entries (s : PState) : List Glucose.Entry :=
  s.readings.map fun r => { glucose := some r.value, date := r.recorded }

/-- A cycle at time `t` from state `s` with inputs `inp` and result `res` is legal when
    `inp.clock.now = t`, `inp.clock.tzOffsetMin = env.tz`, the profile is `env.profileAt t`,
    `iob_data`, `currenttemp` and `glucose_status` are computed from `s` at time `t`, and
    `res = LeanAID.step inp`. The inputs `autosens_data`, `meal_data`, `reservoir_data` and
    `microBolusAllowed` are free. In a run, `s` is the state after all earlier events,
    including those earlier in the same step. -/
structure LegalCycle (env : Env) (t : Int) (s : PState) (inp : DBInputs) (res : Result) : Prop where
  now : inp.clock.now = t
  tz : inp.clock.tzOffsetMin = env.tz
  profile : inp.profile = some (env.profileAt t)
  iob : inp.iob_data = some (iobInputOf (iobOut env s t inp.autosens_data))
  currenttemp : inp.currenttemp = some (currentTempAt s t)
  glucose : inp.glucose_status = Glucose.getLastGlucose (entries s)
  result : res = LeanAID.step inp

/-- The events `e₁, …, eₙ` of a step at time `t` are legal from state `s` when every cycle
    `eᵢ` satisfies `LegalCycle env t sᵢ`, where `sᵢ` is the state after applying
    `e₁, …, eᵢ₋₁` to `s`. -/
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

/-- The steps of a run are legal from state `s` when every step is nonempty, satisfies
    `CycleLast`, and satisfies `LegalEvents` from the state after the earlier steps. -/
def LegalFrom (env : Env) : PState → Run Event → Prop
  | _, [] => True
  | s, st :: r => st.events ≠ [] ∧ CycleLast st.events ∧ LegalEvents env st.time s st.events ∧
      LegalFrom env (applyStep s st) r

/-- A legal run: increasing step times, and every step nonempty, with `CycleLast` and
    `LegalEvents` from the state before it. -/
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

/-- The cycles of a run from `env.init`, in order. -/
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

/-- **Every cycle of a legal run is legal.** Let `r` be a legal run in the environment
    `env`. Then every cycle `c` in `cycles env r` satisfies
    `LegalCycle env c.time c.pre c.inp c.res`: its inputs are computed from the state before
    it, and its result is `LeanAID.step c.inp`. -/
theorem Legal.cycle {env : Env} {r : Run Event} (h : Legal env r) :
    ∀ c ∈ cycles env r, LegalCycle env c.time c.pre c.inp c.res :=
  legal_cyclesFrom h.steps

end LeanAID.Time
