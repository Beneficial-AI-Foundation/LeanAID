/-
  LeanAID.Conformance.TimeRuns — counterexample runs of the timing plan (T0) whose
  cycles call `Iob.generate`. The kernel cannot evaluate `generate` (a `while`
  loop and `List.mergeSort`), so these are checked by `native_decide`, which
  `scripts/check.sh` allows only in `LeanAID/Conformance`. Every run is built by
  `LeanAID.Time.build`, so it is legal (`build_legal`): each cycle's inputs come
  from the run and its result is `LeanAID.step` of them.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import LeanAID.Time.Build

namespace LeanAID.Time.Runs

open LeanAID LeanAID.Time LeanAID.Iob

def t0 : Int := 1795003200000
def mn : Int := 60000

/-- Basal 1 U/h, `max_basal` 3 U/h, `max_iob` 1 U, ISF 50, target 100, bilinear
    curve with DIA 3 h. -/
def prof : Profile :=
  { max_basal := some 3, max_daily_basal := some 1, max_iob := some 1,
    sens := some 50, carb_ratio := some 10, min_bg := some 100, max_bg := some 100, dia := some 3,
    curve := some "bilinear", basalprofile := [{ i := some 0, minutes := 0, rate := 1 }] }

def env : Env := { profile := prof }

def rdAt (ms : Int) (v : JsNum) (dated : Bool := true) : EnvEvent :=
  .reading { value := v, trueTime := ms, recorded := if dated then some (.fin ms) else none }

/-- The results of the cycles of a run, with their times and outcomes. -/
def results (e : Env) (r : Run Event) : List (Int × Result × Outcome) :=
  (cycles e r).map fun c => (c.time, c.res, c.out)

/-! ### P4b: a 120-minute zero temp followed by a stopped loop

Falling glucose (80, 70, 60 mg/dL) makes the cycle at `t0 + 10 min` issue a zero temp
for 120 minutes. The pump accepts it and the loop stops (the run is closed). The pump
delivers nothing until `t0 + 130 min`, then returns to the scheduled 1 U/h. This is
low delivery, not overdose: finding F-20. -/

def zeroScript : List ScriptStep :=
  [ { time := t0, env := [rdAt t0 80] }, { time := t0 + 5 * mn, env := [rdAt (t0 + 5 * mn) 70] },
    { time := t0 + 10 * mn, env := [rdAt (t0 + 10 * mn) 60], cycle := some ({}, .accepted) } ]

def zeroRun : Run Event := build env env.init zeroScript

theorem zeroRun_legal : Legal env zeroRun := build_legal env zeroScript (by decide)

theorem zeroRun_cycle :
    (results env zeroRun).map (fun (t, r, o) => (t, r.rate, r.duration, r.units, o)) =
      [(t0 + 10 * mn, some 0, some 120, none, .accepted)] := by
  native_decide

theorem zeroRun_pump :
    rateAt env zeroRun (t0 + 10 * mn) = 0 ∧ rateAt env zeroRun (t0 + 130 * mn - 1) = 0 ∧
    rateAt env zeroRun (t0 + 130 * mn) = 1 ∧ env.sched (t0 + 130 * mn) = 1 := by
  native_decide

/-! ### P1: a reading 12.04 minutes old passes the stale check

Readings 180, 190, 200 mg/dL five minutes apart; the cycle runs 12.04 minutes after
the last one and issues the maximum rate, 3 U/h. At 12.05 minutes the reading is stale
and nothing is issued. The derived P1 statement has the slack 0.05 minutes for this
reason (F-16). -/

def staleScript (lag : Int) (dated : Bool) : List ScriptStep :=
  [ { time := t0, env := [rdAt t0 180 dated] }, { time := t0 + 5 * mn, env := [rdAt (t0 + 5 * mn) 190 dated] },
    { time := t0 + 10 * mn, env := [rdAt (t0 + 10 * mn) 200 dated] },
    { time := t0 + 10 * mn + lag, cycle := some ({}, .accepted) } ]

theorem stale_1204 :
    (results env (build env env.init (staleScript 722400 true))).map (fun (_, r, _) => (r.rate, r.duration)) =
      [(some 3, some 30)] := by
  native_decide

theorem stale_1205 :
    (results env (build env env.init (staleScript 723000 true))).map (fun (_, r, _) => (r.rate, r.units)) =
      [(none, none)] := by
  native_decide

/-! ### F-11 in a run: undated readings

When the readings carry no date, `getLastGlucose` computes no deltas (every age is
NaN), so delta and the averages are 0 and the cycle sees flat CGM data and does not
increase insulin, even though the stale check is skipped. So F-11 (maximum rate on an
old undated reading) needs a glucose status that `getLastGlucose` does not produce
from the entries of this run model (dated entries only). See FINDINGS F-11. -/

theorem undated_flat :
    (results env (build env env.init (staleScript 3600000 false))).map (fun (_, r, _) => (r.rate, r.units)) =
      [(none, none)] := by
  native_decide

/-! ### A user bolus and a microbolus with the same timestamp

`calcTempTreatments` keeps both records: two bolus treatments of 1 U and 0.5 U at
the same time. -/

def twoBoluses : PState :=
  { temp := none, log := [.bolus (t0 - 10 * mn) (1/2) true, .bolus (t0 - 10 * mn) 1 false] }

theorem same_timestamp_both_kept :
    ((calcTempTreatments { history := history env twoBoluses, profile := prof, clockMs := t0 } none).treatments.filter
      (fun t => t.insulin.isSome)).map (fun t => (t.insulin, t.startedAt)) =
      [(some (.fin (1/2)), some (t0 - 10 * mn)), (some 1, some (t0 - 10 * mn))] := by
  native_decide

/-! ### R21 form I2 fails: zero temps, then microboluses past `max_iob`

Same patient with `max_iob = 0.5` and SMB always enabled. Two hours of glucose at
60 mg/dL make the loop set zero temps; computed IOB falls to about −1.2 U. Then glucose
rises from 150 mg/dL by 15 mg/dL every 5 minutes. The loop gives microboluses of 0.5
and 0.2 U at minutes 130 and 135. At minute 140 the IOB of these microboluses alone is
above 0.69 U, more than `max_iob`. Each microbolus satisfied the guard of its
cycle (I1): computed IOB plus the microbolus was at most `max_iob`. Finding F-21. -/

def profS : Profile := { prof with enableSMB_always := some true, max_iob := some 0.5 }
def envS : Env := { profile := profS }
def smbFree : Free := { microBolusAllowed := true }

def i2Script : List ScriptStep :=
  ((List.range 24).map fun k =>
    { time := t0 + (5 * k : Nat) * mn, env := [rdAt (t0 + (5 * k : Nat) * mn) 60], cycle := some (smbFree, .accepted) }) ++
  ((List.range 8).map fun k =>
    { time := t0 + (120 + 5 * k : Nat) * mn, env := [rdAt (t0 + (120 + 5 * k : Nat) * mn) (.fin (150 + 15 * k : Nat))],
      cycle := some (smbFree, .accepted) })

def i2Run : Run Event := build envS envS.init i2Script

theorem i2Run_legal : Legal envS i2Run := build_legal envS i2Script (by decide)

/-- The accepted microboluses: time and units. -/
def smbs (e : Env) (r : Run Event) : List (Int × Rat) := (cycles e r).filterMap fun c =>
  match c.out, validate c.res with
  | .accepted, some { bolus := some u, .. } => some (c.time, u)
  | _, _ => none

/-- The IOB at time `t` of the accepted microboluses alone (`iobTotal` on them). -/
def smbIob (e : Env) (r : Run Event) (t : Int) : JsNum :=
  (iobTotal ((smbs e r).map fun (tb, u) => ({ insulin := some (.fin u), date := .fin tb } : Treatment))
    e.profile t).iob

theorem i2_smbs :
    (smbs envS i2Run).map (·.1) = [t0 + 130 * mn, t0 + 135 * mn] ∧
    (smbs envS i2Run).map (·.2) = [1/2, Binary64.rd (2/10)] := by
  native_decide

theorem i2_fails : (smbIob envS i2Run (t0 + 140 * mn) >ʲ .fin (69/100)) = true ∧
    profS.max_iob = some 0.5 := by
  native_decide

/-- I1 holds at each microbolus of this run: IOB of the cycle plus the microbolus is
    at most `max_iob`. -/
theorem i2Run_I1 : (cycles envS i2Run).all (fun c =>
    match c.res.units, c.res.IOB with
    | some u, some i => (i + u) ≤ʲ 0.5
    | none, _ => true
    | _, _ => false) = true := by
  native_decide

end LeanAID.Time.Runs
