import LeanAID.Time.Build
import LeanAID.Proofs.ReviewFindings

/-!
# Boundary cases checked by the kernel

Concrete checks by `decide +kernel`, without `native_decide`:
- the stale check at reported ages 12.04 and 12.05 minutes;
- `staleInput`, where the stale-data response issues the rounded controller basal (F-19);
- the SMB age check at ages 3.05 and 3.04 minutes with interval 3;
- pump transitions with given command results: replacement, loss, rejection, cancel.

Checks whose cycles call `Iob.generate` are in `LeanAID.Conformance.TimeRuns`.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time.Examples

open LeanAID LeanAID.Time

/-- The start time of the examples, epoch ms. -/
def t0 : Int := 1795003200000
/-- One minute, ms. -/
def mn : Int := 60000

/-! ### The stale check compares the age rounded to 0.1 minute -/

/-- A reading 12.04 minutes old is not stale: its age rounds to 12.0. -/
example : cgmStale (gluVals (.fin t0) { glucose := some 200, date := some (.fin (t0 - 722400)) }) = false := by
  decide +kernel

/-- A reading 12.05 minutes old is stale: its age rounds to 12.1. -/
example : cgmStale (gluVals (.fin t0) { glucose := some 200, date := some (.fin (t0 - 723000)) }) = true := by
  decide +kernel

/-! ### A rate above the unrounded controller basal on a stale reading

`staleInput` has the unrounded controller basal `current_basal = 0.83` U/h, a 2 U/h temp
and a reading 20 minutes old. The stale-data response issues
`profile_current_basal = round_basal(0.83) = 0.85` U/h on the default 0.05 grid (F-19). -/

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

/-! ### The SMB check compares the age rounded to 0.1 minute

`lastBolusAge c` is `(now - lastBolusTime) / 60000` rounded to one decimal, the age that the
SMB check compares with `SMBInterval`. With interval 3, a reported age of 3.05 minutes passes
and 3.04 minutes fails. -/

example : (JsNum.round ((.fin t0 - .fin (t0 - 183000)) / 60000) 1 >ʲ 3) = true ∧
    (JsNum.round ((.fin t0 - .fin (t0 - 182400)) / 60000) 1 >ʲ 3) = false := by
  decide +kernel

/-! ### Pump transitions with given command results

These runs are not legal: the results are given, not computed by `LeanAID.step`. In
`replRun` a 2 U/h temp of 30 minutes at `t0` is replaced at `t0 + 29 min` by a 1.5 U/h temp
of 30 minutes, which runs until `t0 + 59 min`. -/

/-- An accepted cycle with the given rate and duration and default inputs. -/
def cmd (rate dur : JsNum) : Event :=
  .cycle default { rate := some rate, duration := some dur } .accepted

/-- An environment with the default profile. -/
def envP : Env := { profile := {} }

/-- A temp replaced one minute before its deadline. -/
def replRun : Run Event :=
  [ { time := t0, events := [cmd 2 30] }, { time := t0 + 29 * mn, events := [cmd 1.5 30] } ]

/-- The rate of the stored temp of run `r` under `envP` at time `k`, `none` if the schedule
    applies. -/
def tempAt (r : Run Event) (k : Int) : Option Rat := tempRate (pumpAt envP r k) k

example : tempAt replRun (t0 + 29 * mn - 1) = some 2 ∧ tempAt replRun (t0 + 29 * mn) = some (3/2) ∧
    tempAt replRun (t0 + 30 * mn) = some (3/2) ∧ tempAt replRun (t0 + 59 * mn - 1) = some (3/2) ∧
    tempAt replRun (t0 + 59 * mn) = none := by
  decide +kernel

/-- A temp whose replacement is lost; the temp ends at its own deadline. -/
def lostRun : Run Event :=
  [ { time := t0, events := [cmd 2 30] },
    { time := t0 + 29 * mn, events := [.cycle default { rate := some 1.5, duration := some 30 } .lost] } ]

example : tempAt lostRun (t0 + 30 * mn - 1) = some 2 ∧ tempAt lostRun (t0 + 30 * mn) = none := by
  decide +kernel

/-- A temp followed by a command with NaN rate (F-06), which the pump rejects and logs. -/
def nanRun : Run Event :=
  [ { time := t0, events := [cmd 2 30] }, { time := t0 + 10 * mn, events := [cmd .nan 30] } ]

example : tempAt nanRun (t0 + 10 * mn) = some 2 ∧ (pumpAt envP nanRun (t0 + 10 * mn)).rejected = [t0 + 10 * mn] := by
  decide +kernel

/-- A zero temp cancelled by a command of duration 0. -/
def cancelRun : Run Event :=
  [ { time := t0, events := [cmd 0 120] }, { time := t0 + 10 * mn, events := [cmd 0 0] } ]

example : tempAt cancelRun (t0 + 10 * mn - 1) = some 0 ∧ tempAt cancelRun (t0 + 10 * mn) = none := by
  decide +kernel

end LeanAID.Time.Examples
