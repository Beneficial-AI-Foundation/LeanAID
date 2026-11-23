import LeanAID.Time.System

/-!
# Projection of a T2 run for the replay of UPPAAL traces

Work item U3 of `docs/uppaal-plan.md` replays UPPAAL traces on T2. This file defines
the projection that a replay compares with a trace: for each cycle, its time, its
channel outcome, the pump action that `validate` and `applyCmd` give, and whether a
bolus is delivered; and the delivered rate (`rateAt`: the temp, or the schedule) at
given times. `rateAt` reads the schedule with `basalLookup`, which the kernel does not
reduce (F-25), so the replay checks in `LeanAID/Conformance/` use `native_decide`.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time.Replay

open LeanAID

/-- The pump action of a cycle. -/
inductive Act where
  | none
  | cancel
  | temp (rate : Rat) (minutes : Int)
  deriving DecidableEq, Repr

/-- What a trace shows of one cycle. -/
structure CycleObs where
  time : Int
  accepted : Bool
  act : Act
  bolus : Bool
  deriving DecidableEq, Repr

/-- The observation of a cycle at time `t` with result `res` and outcome `o`, as
    `applyEvent` executes it: a lost or rejected command does nothing. -/
def obsOf (t : Int) (res : Result) (o : Outcome) : CycleObs :=
  match o with
  | .lost => { time := t, accepted := false, act := .none, bolus := false }
  | .accepted =>
    match validate res with
    | none => { time := t, accepted := true, act := .none, bolus := false }
    | some c =>
      { time := t, accepted := true, bolus := c.bolus.isSome,
        act := match c.temp with
          | none => .none
          | some (r, d) => if d = 0 then .cancel else .temp r d }

/-- The observations of the cycles of a run, in order. -/
def cycleObs (r : Run Event) : List CycleObs :=
  r.flatMap fun st => st.events.filterMap fun
    | .cycle _ res o => some (obsOf st.time res o)
    | _ => none

/-- The delivered rate at time `k`: the temp rate, or the schedule. -/
def rateObs (env : Env) (r : Run Event) (k : Int) : Rat := rateAt env r k

/-- The run matches a trace: the same cycle observations, and the same delivered rate (`rateAt`) at
    every checkpoint. -/
def traceMatch (env : Env) (r : Run Event) (obs : List CycleObs) (rates : List (Int × Rat)) :
    Bool :=
  cycleObs r == obs && rates.all fun (k, v) => rateObs env r k == v

/-- A cycle with given fields and outcome, and default inputs. -/
def cmd (rate dur units : Option JsNum) (o : Outcome) : Event :=
  .cycle default { rate := rate, duration := dur, units := units } o

end LeanAID.Time.Replay
