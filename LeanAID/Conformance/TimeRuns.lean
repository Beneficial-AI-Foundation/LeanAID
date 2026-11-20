import LeanAID.Time.Build
import LeanAID.Time.Pump
import LeanAID.Time.LowGlucose
import LeanAID.Time.Examples

/-!
# Concrete runs with history-derived IOB

Every run here is `build e e.init sc` for a script `sc` with strictly increasing times, and
`build_legal` makes it legal. Its cycles compute IOB from the pump history with
`Iob.generate`. Each check is a statement about one concrete run. `zeroRun_pump`,
`zeroRun_temp`, `keepRun_low`, `stale_1204`, `stale_1205` and `undated_flat` use
`decide +kernel`, which trusts no compiled code. The other checks use `native_decide`, which trusts compiled evaluation (`Lean.ofReduceBool`);
`scripts/check.sh` allows it only in `LeanAID/Conformance`. `keepRun_cycle` and
`keepRun_temp` hold by `decide +kernel` too, but take about 8 s each there.

- `zeroRun_pump`, `zeroRun_zero`: a 120-minute zero temp after a falling trace (F-20).
  `zeroRun_cycle_kernel` (`LeanAID.Conformance.KernelRuns`) checks the cycle.
- `stale_1204`, `stale_1205`: the stale check at reported ages 12.04 and 12.05 minutes.
- `undated_flat`: one run with undated readings issues neither a rate nor a bolus.
- `i2_smbs`, `i2_fails`, `i2Run_I1`: microboluses whose own IOB exceeds `max_iob` (F-21).
- `keepRun_cycle`, `keepRun_low`, `keepRun_temp`, `keepRun_zero`: a running zero temp that
  oref0 leaves in place, the second case of `low_glucose_suspend`.

None of these runs was replayed against oref0 in JavaScript: the pump history is encoded
by `encodeAction`, not as ISO-timestamped records.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time.Runs

open LeanAID LeanAID.Time LeanAID.Iob

export LeanAID.Time.Examples (t0 mn)

/-- A one-entry schedule of 1 U/h from midnight, `max_basal` 3 U/h, `max_daily_basal` 1 U/h,
    `max_iob` 1 U, ISF 50 mg/dL/U, carb ratio 10 g/U, target 100 mg/dL, and the bilinear
    curve with DIA 3 h. -/
def prof : Profile :=
  { max_basal := some 3, max_daily_basal := some 1, max_iob := some 1,
    sens := some 50, carb_ratio := some 10, min_bg := some 100, max_bg := some 100, dia := some 3,
    curve := some "bilinear", basalprofile := [{ i := some 0, minutes := 0, rate := 1 }] }

/-- The environment with profile `prof`. -/
def env : Env := { profile := prof }

/-- A reading of value `v` at time `ms`, recorded with that date if `dated`. -/
def rdAt (ms : Int) (v : JsNum) (dated : Bool := true) : EnvEvent :=
  .reading { value := v, trueTime := ms, recorded := if dated then some (.fin ms) else none }

/-- The results of the cycles of a run, with their times and outcomes. -/
def results (e : Env) (r : Run Event) : List (Int × Result × Outcome) :=
  (cycles e r).map fun c => (c.time, c.res, c.out)

/-! ### A 120-minute zero temp followed by a stopped loop

`zeroRun_cycle_kernel` (`LeanAID.Conformance.KernelRuns`) checks that after readings 80, 70
and 60 mg/dL the cycle at `t0 + 10 min` issues a zero temp of 120 minutes. `zeroRun_pump`
checks the modeled rate at acceptance, one millisecond before expiry and at expiry (F-20). -/

/-- Readings 80, 70, 60 mg/dL five minutes apart, then one accepted cycle. -/
def zeroScript : List ScriptStep :=
  [ { time := t0, env := [rdAt t0 80] }, { time := t0 + 5 * mn, env := [rdAt (t0 + 5 * mn) 70] },
    { time := t0 + 10 * mn, env := [rdAt (t0 + 10 * mn) 60], cycle := some ({}, .accepted) } ]

/-- The run of `zeroScript`. -/
def zeroRun : Run Event := build env env.init zeroScript

theorem zeroRun_legal : Legal env zeroRun := build_legal env zeroScript (by decide)

theorem zeroRun_pump :
    rateAt env zeroRun (t0 + 10 * mn) = 0 ∧ rateAt env zeroRun (t0 + 130 * mn - 1) = 0 ∧
    rateAt env zeroRun (t0 + 130 * mn) = 1 ∧ env.sched (t0 + 130 * mn) = 1 := by
  decide +kernel

/-- The stored temp of `zeroRun` after its cycle: rate 0 from `t0 + 10 min` to
    `t0 + 130 min`. -/
theorem zeroRun_temp :
    (pumpAt env zeroRun (t0 + 10 * mn)).temp =
      some { rate := 0, start := t0 + 10 * mn, deadline := t0 + 130 * mn } := by
  decide +kernel

/-- Let `sc` be a script whose steps are all at or before `t`, such that the run
    `build env env.init sc` has strictly increasing times. If the stored temp at `t` is a zero
    temp with deadline `D`, then the modeled rate is 0 at every `k` with `t ≤ k < D`. -/
theorem zero_after_last {sc : List ScriptStep} (hinc : Increasing (build env env.init sc)) {t s D k : Int}
    (hlast : ∀ ss ∈ sc, ss.time ≤ t)
    (htemp : (pumpAt env (build env env.init sc) t).temp = some { rate := 0, start := s, deadline := D })
    (h1 : t ≤ k) (h2 : k < D) : rateAt env (build env env.init sc) k = 0 := by
  have hno : ∀ st ∈ build env env.init sc, t < st.time → st.time ≤ k → setsTemp st = false := by
    intro st hst ht _
    obtain ⟨ss, hss, heq⟩ := build_sub env env.init sc st hst
    have := hlast ss hss
    omega
  obtain ⟨-, hr⟩ := p4a_expiry (env := env) hinc h1 hno
  rw [hr, htemp]
  simp only [h2, ite_true]

/-- The modeled pump rate of `zeroRun` is 0 at every millisecond of
    `[t0 + 10 min, t0 + 130 min)`. -/
theorem zeroRun_zero (k : Int) (h1 : t0 + 10 * mn ≤ k) (h2 : k < t0 + 130 * mn) :
    rateAt env zeroRun k = 0 :=
  zero_after_last zeroRun_legal.increasing (by decide) zeroRun_temp h1 h2

/-! ### The stale check at 12.04 and 12.05 minutes

`stale_1204` checks that a cycle 12.04 minutes after the last of the readings 180, 190 and
200 mg/dL issues 3 U/h, which is `maxSafeBasal` for `prof`, for 30 minutes. `stale_1205`
checks that a cycle 12.05 minutes after it issues neither a rate nor a bolus. The two ages lie
on either side of the bound of 12.05 minutes in the hypothesis of
`cgm_unreliable_no_increase` (F-16). -/

/-- Readings 180, 190, 200 mg/dL five minutes apart, dated if `dated`, then one accepted
    cycle `lag` ms after the last reading. -/
def staleScript (lag : Int) (dated : Bool) : List ScriptStep :=
  [ { time := t0, env := [rdAt t0 180 dated] }, { time := t0 + 5 * mn, env := [rdAt (t0 + 5 * mn) 190 dated] },
    { time := t0 + 10 * mn, env := [rdAt (t0 + 10 * mn) 200 dated] },
    { time := t0 + 10 * mn + lag, cycle := some ({}, .accepted) } ]

theorem stale_1204 :
    (results env (build env env.init (staleScript 722400 true))).map (fun (_, r, _) => (r.rate, r.duration)) =
      [(some 3, some 30)] := by
  decide +kernel

theorem stale_1205 :
    (results env (build env env.init (staleScript 723000 true))).map (fun (_, r, _) => (r.rate, r.units)) =
      [(none, none)] := by
  decide +kernel

/-! ### F-11 in a run: undated readings

`undated_flat` checks that the run of `staleScript 3600000 false` issues neither a rate nor a
bolus. Its readings carry no date, its last BG is 200 mg/dL, and its cycle is one hour after
that reading. `getLastGlucose` finds no deltas, and the flat-CGM check (F-18), which needs
BG above 60 mg/dL, applies. This is one run, not a result for every undated status. -/

theorem undated_flat :
    (results env (build env env.init (staleScript 3600000 false))).map (fun (_, r, _) => (r.rate, r.units)) =
      [(none, none)] := by
  decide +kernel

/-! ### A user bolus and a microbolus with the same timestamp

`same_timestamp_both_kept_kernel` (`LeanAID.Conformance.KernelRuns`) checks that
`calcTempTreatments` keeps both boluses of `twoBoluses` (1 U and 0.5 U at the same time). -/

/-- A user bolus of 1 U and a microbolus of 0.5 U with the same time. -/
def twoBoluses : PState :=
  { temp := none, log := [.bolus (t0 - 10 * mn) (1/2) true, .bolus (t0 - 10 * mn) 1 false] }

/-! ### R21 fails for the IOB of microboluses alone after zero temps

`i2Run` has `max_iob = 0.5` U and SMB always enabled. Glucose stays at 60 mg/dL for two hours,
so the loop issues zero temps and net IOB falls to about −1.2 U. Glucose then rises from
150 mg/dL by 15 mg/dL every 5 minutes. `i2_smbs` checks microboluses of 0.5 U and 0.2 U at
minutes 130 and 135, and `i2_fails` checks that their IOB alone exceeds 0.69 U at minute 140.
`i2Run_I1` checks that oref0's guard `IOB + units ≤ 0.5`, computed in JavaScript arithmetic,
held at each microbolus cycle (F-21). -/

/-- `prof` with `max_iob = 0.5` and SMB always enabled. -/
def profS : Profile := { prof with enableSMB_always := some true, max_iob := some 0.5 }
/-- The environment with profile `profS`. -/
def envSmb : Env := { profile := profS }
/-- Free inputs with microboluses allowed. -/
def smbFree : Free := { microBolusAllowed := true }

/-- 24 cycles at 60 mg/dL, then 8 cycles rising from 150 mg/dL by 15 mg/dL, 5 minutes
    apart. -/
def i2Script : List ScriptStep :=
  ((List.range 24).map fun k =>
    { time := t0 + (5 * k : Nat) * mn, env := [rdAt (t0 + (5 * k : Nat) * mn) 60], cycle := some (smbFree, .accepted) }) ++
  ((List.range 8).map fun k =>
    { time := t0 + (120 + 5 * k : Nat) * mn, env := [rdAt (t0 + (120 + 5 * k : Nat) * mn) (.fin (150 + 15 * k : Nat))],
      cycle := some (smbFree, .accepted) })

/-- The run of `i2Script`. -/
def i2Run : Run Event := build envSmb envSmb.init i2Script

theorem i2Run_legal : Legal envSmb i2Run := build_legal envSmb i2Script (by decide)

/-- The accepted microboluses: time and units. -/
def smbs (e : Env) (r : Run Event) : List (Int × Rat) := (cycles e r).filterMap fun c =>
  match c.out, validate c.res with
  | .accepted, some { bolus := some u, .. } => some (c.time, u)
  | _, _ => none

/-- The IOB at time `t` that `iobTotal` computes, with profile `e.profile`, from the accepted
    microboluses of `r` alone. -/
def smbIob (e : Env) (r : Run Event) (t : Int) : JsNum :=
  (iobTotal ((smbs e r).map fun (tb, u) => ({ insulin := some (.fin u), date := .fin tb } : Treatment))
    e.profile t).iob

/-- The three `i2Run` checks, evaluated once. -/
theorem i2_checks :
    ((smbs envSmb i2Run).map (·.1) = [t0 + 130 * mn, t0 + 135 * mn] ∧
      (smbs envSmb i2Run).map (·.2) = [1/2, Binary64.rd (2/10)]) ∧
    ((smbIob envSmb i2Run (t0 + 140 * mn) >ʲ .fin (69/100)) = true ∧ profS.max_iob = some 0.5) ∧
    (cycles envSmb i2Run).all (fun c =>
      match c.res.units, c.res.IOB with
      | some u, some i => (i + u) ≤ʲ 0.5
      | none, _ => true
      | _, _ => false) = true := by
  native_decide

theorem i2_smbs :
    (smbs envSmb i2Run).map (·.1) = [t0 + 130 * mn, t0 + 135 * mn] ∧
    (smbs envSmb i2Run).map (·.2) = [1/2, Binary64.rd (2/10)] :=
  i2_checks.1

theorem i2_fails : (smbIob envSmb i2Run (t0 + 140 * mn) >ʲ .fin (69/100)) = true ∧
    profS.max_iob = some 0.5 :=
  i2_checks.2.1

/-- At every cycle of `i2Run` that issues `u` units, the result reports an IOB `i`, and
    `i + u ≤ 0.5` in JavaScript arithmetic. -/
theorem i2Run_I1 : (cycles envSmb i2Run).all (fun c =>
    match c.res.units, c.res.IOB with
    | some u, some i => (i + u) ≤ʲ 0.5
    | none, _ => true
    | _, _ => false) = true :=
  i2_checks.2.2

/-! ### Low glucose suspend: a running zero temp left in place

`keepRun` extends `zeroScript` by a reading of 55 mg/dL and a second accepted cycle at
`t0 + 15 min`. `keepRun_cycle` checks that the first cycle sets a zero temp of 120 minutes
and the second issues no rate, no duration and no units. oref0's reason for the second cycle
is "115m left and 0 ~ req 0U/hr: no temp required". `keepRun_low` checks that both cycles meet
`LowCycle`. `keepRun_temp` checks that the pump keeps the zero temp of the first cycle, and
`keepRun_zero` that the rate is 0 from `t0 + 15 min` to `t0 + 130 min`. -/

/-- `zeroScript`, then a reading of 55 mg/dL and an accepted cycle at `t0 + 15 min`. -/
def keepScript : List ScriptStep := zeroScript ++
  [ { time := t0 + 15 * mn, env := [rdAt (t0 + 15 * mn) 55], cycle := some ({}, .accepted) } ]

/-- The run of `keepScript`. -/
def keepRun : Run Event := build env env.init keepScript

theorem keepRun_legal : Legal env keepRun := build_legal env keepScript (by decide)

theorem keepRun_cycle :
    (results env keepRun).map (fun (t, r, o) => (t, r.rate, r.duration, r.units, o)) =
      [(t0 + 10 * mn, some 0, some 120, none, .accepted), (t0 + 15 * mn, none, none, none, .accepted)] := by
  native_decide

theorem keepRun_low : ∀ c ∈ cycles env keepRun, LowCycle c := by
  have h : (cycles env keepRun).all lowCycleB = true := by decide +kernel
  exact fun c hc => lowCycle_of_b (List.all_eq_true.mp h c hc)

theorem keepRun_temp :
    (pumpAt env keepRun (t0 + 15 * mn)).temp =
      some { rate := 0, start := t0 + 10 * mn, deadline := t0 + 130 * mn } := by
  native_decide

/-- The modeled pump rate of `keepRun` is 0 at every millisecond of
    `[t0 + 15 min, t0 + 130 min)`. -/
theorem keepRun_zero (k : Int) (h1 : t0 + 15 * mn ≤ k) (h2 : k < t0 + 130 * mn) :
    rateAt env keepRun k = 0 :=
  zero_after_last keepRun_legal.increasing (by decide) keepRun_temp h1 h2

end LeanAID.Time.Runs
