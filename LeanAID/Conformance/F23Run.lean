import LeanAID.Time.Build
import LeanAID.Time.LowGlucose
import LeanAID.Time.Examples
import LeanAID.Time.Config

/-!
# F-23 in a legal run: a rejected zero temp at low, rising glucose

`f23Run` is a legal run (`build_legal`). A 2 U/h temp runs from the start, with deadline
`t0 + 20 min` (`env23.initTemp`). Readings of 54, 57 and 60 mg/dL arrive five minutes apart.
The profile has a 1 U/h schedule, target 100 mg/dL (threshold 70 mg/dL), ISF 50 mg/dL/U and
`enableUAM`. The pump history holds the records of the running temp, so IOB is computed from
it. At `t0 + 10 min` one accepted cycle runs with `mealCOB` 20 and no `carbs`, the input of
case A of `scripts/probe-lgs-nan.js`.

- `f23Run_cycle`: at that cycle, BG is 60 mg/dL, below `threshold` 70, and rising
  (`minDelta = 3`); the carb impact `minDelta − bgi` is positive; `minGuardBG` is NaN; the first
  branch of the dose phase is not taken; `LowCycle` holds. oref0 requests rate 0 with a NaN
  duration and no units, and `validate` rejects it. The stored temp after the cycle is the
  2 U/h temp, and the pump records the rejection.
- `f23Run_low`: the cycle meets `LowCycle`, the hypothesis of `low_glucose_pump`.
- `f23Run_second`: the cycle is accepted and meets `LowCycle`, `ZeroFrom` fails at its time,
  and the second disjunct of `low_glucose_pump` holds.
- `f23Run_rate`: the modeled pump rate is 2 U/h at every millisecond of
  `[t0 + 10 min, t0 + 20 min)`, and 1 U/h, the schedule, at `t0 + 20 min`.
- `f23Run_hyps`, `f23Run_covered`: the run meets every hypothesis of `low_glucose_pump`, and the
  theorem applied to it gives the case of `f23Run_second`.
- `f23RunC_checks`: the same run with `carbs` 30 has a finite `minGuardBG`, and the pump accepts
  its zero temp. So the missing carbs cause the NaN.

The checks use `decide +kernel`. The carb-impact branch condition of `dbPredict` (`cid > 0` or
`remainingCIpeak > 0`, `determine-basal.js:729-740`) is a local value, so it is not checked by
name. The contrast run checks that adding carbs makes `minGuardBG` finite.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time.F23Run

open LeanAID LeanAID.Time LeanAID.Proofs

export LeanAID.Time.Examples (t0 mn)

/-- A one-entry schedule of 1 U/h from midnight, `max_basal` 3 U/h, `max_daily_basal`
    1 U/h, `max_iob` 1 U, ISF 50 mg/dL/U, carb ratio 10 g/U, target 100 mg/dL, the bilinear
    curve with DIA 3 h, and `enableUAM`. -/
def prof23 : Profile :=
  { max_basal := some 3, max_daily_basal := some 1, max_iob := some 1,
    sens := some 50, carb_ratio := some 10, min_bg := some 100, max_bg := some 100, dia := some 3,
    curve := some "bilinear", enableUAM := some true,
    basalprofile := [{ i := some 0, minutes := 0, rate := 1 }] }

/-- The environment with profile `prof23` and a 2 U/h temp from `t0 − 10 min` to
    `t0 + 20 min`, which is also in the initial pump history. -/
def env23 : Env :=
  { profile := prof23, initTemp := some { rate := 2, start := t0 - 10 * mn, deadline := t0 + 20 * mn },
    initHistory := encodeAction (.temp (t0 - 10 * mn) 2 30) }

/-- A reading of value `v` at time `ms`, recorded with that date. -/
def rdAt (ms : Int) (v : JsNum) : EnvEvent :=
  .reading { value := v, trueTime := ms, recorded := some (.fin ms) }

/-- Free inputs with `mealCOB` 20 and no `carbs`. -/
def meal24 : Free := { meal_data := some { mealCOB := some 20 } }

/-- Free inputs with `mealCOB` 20 and `carbs` 30. -/
def meal24C : Free := { meal_data := some { mealCOB := some 20, carbs := some 30 } }

/-- Readings 54, 57, 60 mg/dL five minutes apart, then one accepted cycle with meal data `m`. -/
def f23ScriptWith (m : Free) : List ScriptStep :=
  [ { time := t0, env := [rdAt t0 54] }, { time := t0 + 5 * mn, env := [rdAt (t0 + 5 * mn) 57] },
    { time := t0 + 10 * mn, env := [rdAt (t0 + 10 * mn) 60], cycle := some (m, .accepted) } ]

/-- The F-23 script: `f23ScriptWith meal24`. -/
def f23Script : List ScriptStep := f23ScriptWith meal24

/-- The run of `f23Script`. -/
def f23Run : Run Event := build env23 env23.init f23Script

theorem f23Run_legal : Legal env23 f23Run := build_legal env23 f23Script (by decide)

/-- The facts of the F-23 cycle `c`, as a decision procedure. -/
def f23Facts (c : CycleAt) : Bool :=
  (match dbPrelude c.inp with
   | .ok pre => pre.bg == 60 && pre.threshold == 70 && pre.minDelta == 3 && (pre.minDelta - pre.bgi >ʲ 0) &&
       (dbPredict c.inp pre).minGuardBG == .nan && !doseFirstBranch pre
   | .error _ => false) &&
  c.inp.profile.bind (·.enableUAM) == some true &&
  c.inp.meal_data.map (·.mealCOB) == some (some 20) && c.inp.meal_data.map (·.carbs) == some none &&
  c.inp.autosens_data.isNone && lowCycleB c

/-- One evaluation of all facts about `f23Run`. -/
theorem f23Run_checks :
    (cycles env23 f23Run).map (fun c => (c.time, c.res.rate, c.res.duration, c.res.units, c.out)) =
      [(t0 + 10 * mn, some 0, some .nan, none, .accepted)] ∧
    (cycles env23 f23Run).map (fun c => (validate c.res, f23Facts c, c.pre.temp)) =
      [(none, true, env23.initTemp)] ∧
    (pumpAt env23 f23Run (t0 + 10 * mn)).temp = env23.initTemp ∧
    (pumpAt env23 f23Run (t0 + 10 * mn)).rejected = [t0 + 10 * mn] ∧
    env23.sched (t0 + 20 * mn) = 1 := by
  decide +kernel

/-- **The F-23 cycle.** `f23Run` has one cycle `c`, at `t0 + 10 min`. Its prelude succeeds
    with `pre`, where BG is 60 mg/dL, `threshold` is 70 mg/dL, `minDelta` is 3, the carb
    impact `minDelta − bgi` is positive, `minGuardBG` is NaN and `doseFirstBranch pre = false`.
    Its input has `enableUAM`, `mealCOB` 20 and no `carbs`. oref0 requests rate 0 with a NaN
    duration and no units; the command is accepted and `validate` rejects it. The stored
    temp before and after the cycle is the 2 U/h temp of `env23.initTemp`, and the pump
    records the rejection at `t0 + 10 min`. -/
theorem f23Run_cycle :
    (cycles env23 f23Run).map (fun c => (c.time, c.res.rate, c.res.duration, c.res.units, c.out)) =
      [(t0 + 10 * mn, some 0, some .nan, none, .accepted)] ∧
    (cycles env23 f23Run).map (fun c => (validate c.res, f23Facts c, c.pre.temp)) =
      [(none, true, env23.initTemp)] ∧
    (pumpAt env23 f23Run (t0 + 10 * mn)).temp = some { rate := 2, start := t0 - 10 * mn, deadline := t0 + 20 * mn } ∧
    (pumpAt env23 f23Run (t0 + 10 * mn)).rejected = [t0 + 10 * mn] :=
  ⟨f23Run_checks.1, f23Run_checks.2.1, f23Run_checks.2.2.1, f23Run_checks.2.2.2.1⟩

/-- Every cycle `c` of `f23Run` is at `t0 + 10 min`, requests rate 0 with a NaN duration, is
    accepted, has `f23Facts c = true`, and has `env23.initTemp` as the stored temp before it. -/
theorem f23Run_mem {c : CycleAt} (hc : c ∈ cycles env23 f23Run) :
    c.time = t0 + 10 * mn ∧ c.res.rate = some 0 ∧ c.res.duration = some .nan ∧ c.out = .accepted ∧
      f23Facts c = true ∧ c.pre.temp = env23.initTemp := by
  have h1 := congrArg (fun l => (c.time, c.res.rate, c.res.duration, c.res.units, c.out) ∈ l) f23Run_checks.1
  have h2 := congrArg (fun l => (validate c.res, f23Facts c, c.pre.temp) ∈ l) f23Run_checks.2.1
  simp only [List.mem_map, List.mem_singleton, eq_iff_iff] at h1 h2
  have a := h1.mp ⟨c, hc, rfl⟩
  have b := h2.mp ⟨c, hc, rfl⟩
  simp only [Prod.mk.injEq] at a b
  exact ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.2, b.2.1, b.2.2⟩

/-- Every cycle of `f23Run` meets `LowCycle`. -/
theorem f23Run_low : ∀ c ∈ cycles env23 f23Run, LowCycle c := by
  intro c hc
  have h := (f23Run_mem hc).2.2.2.2.1
  unfold f23Facts at h
  simp only [Bool.and_eq_true] at h
  exact lowCycle_of_b h.2

/-- **`low_glucose_pump` reaches its second case.** Every cycle `c` of `f23Run` is accepted
    and meets `LowCycle`, `ZeroFrom env23 f23Run c.time` is false, and `c.res` has rate 0
    and a NaN duration while the stored temp at `c.time` is `c.pre.temp`. -/
theorem f23Run_second : ∀ c ∈ cycles env23 f23Run,
    c.out = .accepted ∧ LowCycle c ∧ ¬ ZeroFrom env23 f23Run c.time ∧
    (c.res.rate = some 0 ∧ c.res.duration = some .nan ∧ (pumpAt env23 f23Run c.time).temp = c.pre.temp) := by
  intro c hc
  obtain ⟨ht, hr, hd, ho, -, hpre⟩ := f23Run_mem hc
  have htemp := f23Run_checks.2.2.1
  refine ⟨ho, f23Run_low c hc, ?_, hr, hd, by rw [ht, htemp, hpre]⟩
  rintro ⟨tp, htp, h0, -⟩
  rw [ht, htemp] at htp
  simp only [env23, Option.some.injEq] at htp
  subst htp
  simp at h0

/-- **The positive temp keeps running.** The modeled pump rate of `f23Run` is 2 U/h at every
    millisecond of `[t0 + 10 min, t0 + 20 min)`, and 1 U/h at `t0 + 20 min`. -/
theorem f23Run_rate :
    (∀ k, t0 + 10 * mn ≤ k → k < t0 + 20 * mn → rateAt env23 f23Run k = 2) ∧
    rateAt env23 f23Run (t0 + 20 * mn) = 1 := by
  have hinc := f23Run_legal.increasing
  have hmn : mn = 60000 := rfl
  have hno : ∀ k, ∀ st ∈ f23Run, t0 + 10 * mn < st.time → st.time ≤ k → setsTemp st = false := by
    intro k st hst ht _
    obtain ⟨ss, hss, heq⟩ := build_sub env23 env23.init f23Script st hst
    simp only [f23Script, f23ScriptWith, List.mem_cons, List.not_mem_nil, or_false] at hss
    rcases hss with h | h | h <;> subst h <;> simp only at heq <;> omega
  have hr : ∀ k, t0 + 10 * mn ≤ k → rateAt env23 f23Run k =
      if k < t0 + 20 * mn then 2 else env23.sched k := by
    intro k hk
    obtain ⟨-, h⟩ := p4a_expiry (env := env23) hinc hk (hno k)
    rw [h, f23Run_checks.2.2.1]
    rfl
  refine ⟨fun k h1 h2 => ?_, ?_⟩
  · rw [hr k h1]; simp only [h2, ↓reduceIte]
  · rw [hr _ (by omega)]; simp only [Int.lt_irrefl, ↓reduceIte]; exact f23Run_checks.2.2.2.2

/-- `f23Run` meets the hypotheses of `low_glucose_pump`: `ValidEnv env23` (from
    `ValidSchedule env23`), `AutosensOk env23 f23Run` (no cycle has autosens data) and
    `InitDouble env23` (the initial rate 2 U/h is a double). -/
theorem f23Run_hyps : ValidEnv env23 ∧ AutosensOk env23 f23Run ∧ InitDouble env23 := by
  refine ⟨validEnv_of_schedule (by decide +kernel), ?_, ?_⟩
  · intro c hc a ha
    have h := (f23Run_mem hc).2.2.2.2.1
    unfold f23Facts at h
    simp only [Bool.and_eq_true] at h
    rw [ha] at h
    simp at h
  · intro tp h
    simp only [env23, Option.some.injEq] at h
    subst h
    decide +kernel

/-- **`low_glucose_pump` covers the F-23 run.** For every cycle `c` of `f23Run`, the theorem
    applies and gives `ZeroFrom env23 f23Run c.time`, or rate 0 with a NaN duration and the
    stored temp `c.pre.temp`; `f23Run_second` shows that the second case holds. -/
theorem f23Run_covered : ∀ c ∈ cycles env23 f23Run,
    ZeroFrom env23 f23Run c.time ∨
    (c.res.rate = some 0 ∧ c.res.duration = some .nan ∧ (pumpAt env23 f23Run c.time).temp = c.pre.temp) :=
  fun c hc => low_glucose_pump f23Run_legal f23Run_hyps.1 f23Run_hyps.2.1 f23Run_hyps.2.2 hc
    (f23Run_mem hc).2.2.2.1 (f23Run_low c hc)

/-- The contrast run: `f23ScriptWith meal24C`, the F-23 input with `carbs` 30. -/
def f23RunC : Run Event := build env23 env23.init (f23ScriptWith meal24C)

/-- `minGuardBG` of a cycle is finite. -/
def guardFinite (c : CycleAt) : Bool :=
  match dbPrelude c.inp with
  | .ok pre => (dbPredict c.inp pre).minGuardBG != .nan && lowCycleB c
  | .error _ => false

/-- **With carbs the guard is finite.** The single cycle of `f23RunC` has a finite
    `minGuardBG`, meets `LowCycle`, and requests rate 0 with a duration that the pump accepts;
    the stored temp after it has rate 0. -/
theorem f23RunC_checks :
    (cycles env23 f23RunC).map (fun c => (guardFinite c, c.res.rate, (validate c.res).isSome)) =
      [(true, some 0, true)] ∧
    (pumpAt env23 f23RunC (t0 + 10 * mn)).temp.map (·.rate) = some 0 := by
  decide +kernel

end LeanAID.Time.F23Run
