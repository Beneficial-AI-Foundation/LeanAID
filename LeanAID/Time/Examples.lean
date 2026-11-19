/-
  LeanAID.Time.Examples — counterexample and boundary cases of the timing plan
  (T0) that the kernel can check by `decide` or `rfl`. Cases whose cycles call
  `Iob.generate`, which the kernel cannot evaluate (a `while` loop and
  `List.mergeSort`), are in `LeanAID/Conformance/TimeRuns.lean`.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import LeanAID.Time.Build
import LeanAID.Proofs.ReviewFindings

namespace LeanAID.Time.Examples

open LeanAID LeanAID.Time

def t0 : Int := 1795003200000
def mn : Int := 60000

/-! ### P1: the stale check compares the age rounded to 0.1 minute -/

/-- A reading 12.04 minutes old is not stale: its age rounds to 12.0. -/
example : cgmStale (gluVals (.fin t0) { glucose := some 200, date := some (.fin (t0 - 722400)) }) = false := by
  decide +kernel

/-- A reading 12.05 minutes old is stale: its age rounds to 12.1. -/
example : cgmStale (gluVals (.fin t0) { glucose := some 200, date := some (.fin (t0 - 723000)) }) = true := by
  decide +kernel

/-! ### P1: a rate above the unrounded basal on a stale reading

With `current_basal = 0.83`, `profile_current_basal = round_basal(0.83) = 0.85`. A
stale reading with a 2 U/h temp running makes oref0 replace the temp by 0.85 U/h,
which is above the scheduled 0.83 U/h. P1 compares with the rounded basal, so this
is allowed; the gap is recorded in FINDINGS (F-19). -/

def staleInput : DBInputs :=
  { glucose_status := some { glucose := some 200, delta := some 5, short_avgdelta := some 5, long_avgdelta := some 5,
                             date := some (.fin (t0 - 20 * mn)) },
    currenttemp := some { duration := some 20, rate := some 2, temp := some "absolute" },
    iob_data := some (.single { iob := some 0, activity := some 0 }),
    profile := some { current_basal := some 0.83, max_basal := some 3, max_daily_basal := some 1, max_iob := some 1,
                      sens := some 50, carb_ratio := some 10, min_bg := some 100, max_bg := some 100 },
    clock := { now := t0 } }

example : (LeanAID.step staleInput).rate = some (.fin (Binary64.rd (85/100))) ∧
    Binary64.rd (83/100) < Binary64.rd (85/100) := by
  decide +kernel

/-! ### P5: the spacing check compares the age rounded to 0.1 minute

`lastBolusAge c = round((now - lastBolusTime) / 60000, 1)`, and a microbolus needs
`lastBolusAge > SMBInterval` (default 3). An age of 3.05 minutes passes, 3.04 minutes
does not. So the real gap between two microboluses is at least 3.05 minutes when the
interval is 3; the plan's derived bound `I − 0.05` is weaker than what the code does. -/

theorem lastBolusAge_def (c : Ctx) :
    lastBolusAge c = JsNum.round ((.fin c.clock.now - c.iobd.lastBolusTime.js) / 60000) 1 := rfl

example : (JsNum.round ((.fin t0 - .fin (t0 - 183000)) / 60000) 1 >ʲ 3) = true ∧
    (JsNum.round ((.fin t0 - .fin (t0 - 182400)) / 60000) 1 >ʲ 3) = false := by
  decide +kernel

/-! ### Replacement of a temp near the deadline of the old one (T2 pump model)

These runs are not legal runs (the results are given, not computed); they show the
pump model alone. A 2 U/h temp for 30 minutes at `t0`, replaced at `t0 + 29 min` by a
1.5 U/h temp for 30 minutes. At `t0 + 30 min` the pump runs the new temp, not the
schedule, and the new temp ends at `t0 + 59 min`. -/

def cmd (rate dur : JsNum) : Event :=
  .cycle default { rate := some rate, duration := some dur } .accepted

def envP : Env := { profile := {} }

def replRun : Run Event :=
  [ { time := t0, events := [cmd 2 30] }, { time := t0 + 29 * mn, events := [cmd 1.5 30] } ]

/-- `tempRate (pumpAt env r k) k`: the running temp's rate at `k`, `none` = schedule. -/
def tempAt (r : Run Event) (k : Int) : Option Rat := tempRate (pumpAt envP r k) k

example : tempAt replRun (t0 + 29 * mn - 1) = some 2 ∧ tempAt replRun (t0 + 29 * mn) = some (3/2) ∧
    tempAt replRun (t0 + 30 * mn) = some (3/2) ∧ tempAt replRun (t0 + 59 * mn - 1) = some (3/2) ∧
    tempAt replRun (t0 + 59 * mn) = none := by
  decide +kernel

/-- A lost replacement changes nothing: the old temp ends at its deadline. -/
def lostRun : Run Event :=
  [ { time := t0, events := [cmd 2 30] },
    { time := t0 + 29 * mn, events := [.cycle default { rate := some 1.5, duration := some 30 } .lost] } ]

example : tempAt lostRun (t0 + 30 * mn - 1) = some 2 ∧ tempAt lostRun (t0 + 30 * mn) = none := by
  decide +kernel

/-- A rejected command (NaN rate, F-06) changes nothing and is logged. -/
def nanRun : Run Event :=
  [ { time := t0, events := [cmd 2 30] }, { time := t0 + 10 * mn, events := [cmd .nan 30] } ]

example : tempAt nanRun (t0 + 10 * mn) = some 2 ∧ (pumpAt envP nanRun (t0 + 10 * mn)).rejected = [t0 + 10 * mn] := by
  decide +kernel

/-- A duration of 0 cancels: the schedule runs from the cancel on. -/
def cancelRun : Run Event :=
  [ { time := t0, events := [cmd 0 120] }, { time := t0 + 10 * mn, events := [cmd 0 0] } ]

example : tempAt cancelRun (t0 + 10 * mn - 1) = some 0 ∧ tempAt cancelRun (t0 + 10 * mn) = none := by
  decide +kernel

end LeanAID.Time.Examples
