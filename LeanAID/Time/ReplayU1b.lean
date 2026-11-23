import LeanAID.Time.Replay
import LeanAID.Time.Issued
import LeanAID.Proofs.ValidCheck
import LeanAID.Time.Delivery

/-!
# Projection of a legal T2 run for the replay of the U1b UPPAAL traces

Work item U3b of `docs/uppaal-plan.md` replays the U1b traces, whose controller is the
contract. The T2 run is built by `build`, so `LeanAID.step` computes every issued
output. The projection gives, for each step, whether it has a reading and a positive
user bolus, and for its cycle the issued fields as the codes of `uppaal/model.py` and
the execution (`Replay.obsOf`). It also gives the checks of section 7 that the run is
in R_U: `ValidRun` (`validRunB`, with `validRun_of_B`), BolusSeen (`bolusSeenB`), and the
reading and interval conditions of section 3 (`readingsOkB`, `smbThreeB`).

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time.Replay

open LeanAID LeanAID.Time LeanAID.Proofs JsNum

/-- The issued fields as the codes of `uppaal/model.py`: rate, duration kind and value,
    units. -/
structure Issued where
  rc : Nat
  dk : Nat
  dv : Int
  uk : Nat
  deriving DecidableEq, Repr

/-- The rate class: 0 absent, 1 NaN, 2 negative, 3 zero, 4 low (at most `pcb`),
    5 high (above `pcb`, as `Increase` counts it). -/
def rateCode (pcb : JsNum) : Option JsNum → Nat
  | none => 0
  | some .nan => 1
  | some (.fin r) => if r < 0 then 2 else if r = 0 then 3 else if (JsNum.fin r >ʲ pcb) then 5 else 4

/-- The duration kind and value: 0 absent, 1 NaN, 2 not whole in [30, 120], 3 whole
    (value clamped to −1..121, as the model's representatives), 4 not whole outside
    [30, 120]. -/
def durCode : Option JsNum → Nat × Int
  | none => (0, 0)
  | some .nan => (1, 0)
  | some (.fin d) =>
    if d.den = 1 then (3, max (-1) (min 121 d.num))
    else if 30 ≤ d ∧ d ≤ 120 then (2, 0) else (4, 0)

/-- The units class: 0 absent, 1 NaN, 2 finite and at most 0, 3 positive. -/
def unitsCode : Option JsNum → Nat
  | none => 0
  | some .nan => 1
  | some (.fin u) => if u ≤ 0 then 2 else 3

/-- The issued fields of a result at time `t`. -/
def issuedOf (env : Env) (t : Int) (res : Result) : Issued :=
  let (dk, dv) := durCode res.duration
  { rc := rateCode (profileCurrentBasal (env.profileAt t)) res.rate, dk, dv,
    uk := unitsCode res.units }

/-- The representative rate of a rate class in the replay files: zero 0, low 1/2,
    high 2 (`uppaal/replay.py`). Other codes keep the rate. -/
def classRate (code : Nat) (r : Rat) : Rat :=
  match code with
  | 3 => 0
  | 4 => 1 / 2
  | 5 => 2
  | _ => r

/-- An observation with its temp rate replaced by the representative of its class: a
    trace shows the class of a rate, not the rate. -/
def classObs (pcb : JsNum) (o : CycleObs) : CycleObs :=
  match o.act with
  | .temp r d => { o with act := .temp (classRate (rateCode pcb (some (.fin r))) r) d }
  | _ => o

/-- What a trace shows of one step: a reading, a positive user bolus, and its cycle with
    the issued fields and, if the trace has it, the execution. -/
structure StepObs where
  time : Int
  reading : Bool
  userBolus : Bool
  cycle : Option (Issued × Option CycleObs)
  deriving DecidableEq, Repr

/-- The projection of one step of a T2 run. -/
def stepObs (env : Env) (st : Step Event) : StepObs :=
  { time := st.time,
    reading := st.events.any fun | .reading _ => true | _ => false,
    userBolus := st.events.any fun | .userBolus u => decide (0 < u) | _ => false,
    cycle := (st.events.filterMap fun
      | .cycle _ res o => some (issuedOf env st.time res,
          some (classObs (profileCurrentBasal (env.profileAt st.time)) (obsOf st.time res o)))
      | _ => none).head? }

/-- A T2 step matches a trace step. If the trace ends inside the cycle (no execution),
    only the issued fields are compared. -/
def stepMatch (t2 tr : StepObs) : Bool :=
  t2.time == tr.time && t2.reading == tr.reading && t2.userBolus == tr.userBolus &&
  match t2.cycle, tr.cycle with
  | none, none => true
  | some (i, o), some (i', o') => i == i' && (o' == none || o == o')
  | _, _ => false

/-- The run matches a U1b trace: the same steps, and the same delivered rate at every
    checkpoint. -/
def traceMatchU1b (env : Env) (r : Run Event) (steps : List StepObs) (rates : List (Int × Rat)) :
    Bool :=
  r.length == steps.length && (List.zip (r.map (stepObs env)) steps).all (fun (a, b) => stepMatch a b) &&
  rates.all fun (k, v) => rateObs env r k == v

/-! ### R_U: the conditions of section 3 of the plan -/

/-- Every cycle has valid input (decided by `validInputB`). -/
def validRunB (env : Env) (r : Run Event) : Bool := (cycles env r).all fun c => validInputB c.inp

theorem validRun_of_B {env : Env} {r : Run Event} (h : validRunB env r = true) : ValidRun env r := by
  intro c hc
  exact validInputB_sound (List.all_eq_true.mp h c hc)

/-- BolusSeen: at every cycle, the `lastBolusTime` that `Iob.generate` finds is at or
    after every bolus in the pump log before the cycle (accepted microboluses and
    positive user boluses, the earlier ones in the same step included). -/
def bolusSeenB (env : Env) (r : Run Event) : Bool :=
  (cycles env r).all fun c =>
    let lbt := (iobOut env c.pre c.time c.inp.autosens_data).lastBolusTime
    c.pre.log.all fun
      | .bolus tb _ _ => (JsNum.fin tb ≤ʲ lbt)
      | _ => true

/-- Every reading is dated with the time of its step, its value is finite and above 38,
    and readings are at least 150 s apart. -/
def readingsOkB (r : Run Event) : Bool :=
  let rs := r.flatMap fun st => st.events.filterMap fun
    | .reading x => some (st.time, x)
    | _ => none
  rs.all (fun (t, x) => x.trueTime == t && x.recorded == some (.fin t) &&
    match x.value with | .fin v => decide (38 < v) | .nan => false) &&
  (List.zip rs rs.tail).all fun ((t1, _), (t2, _)) => decide (t1 + 150000 ≤ t2)

/-- The SMB interval of every cycle is 3 minutes. -/
def smbThreeB (env : Env) (r : Run Event) : Bool :=
  (cycles env r).all fun c => smbInterval (env.profileAt c.time) == 3

/-! ### A schedule with one entry

`basalLookup` on a one-entry schedule does not read the time. So `profileAt` and
`sched` are the same at every time, and the conditions of R_U "at every time" reduce to
one check. -/

theorem basalLookup_single (e : BasalEntry) (now : JsNum) (tz : Int) :
    Iob.basalLookup [e] now tz =
      (if e.rate =ʲ 0 then none else some (JsNum.mathRound (e.rate * 1000) / 1000)) := by
  unfold Iob.basalLookup
  simp [Iob.sortByKey]
  rfl

theorem profileAt_single {env : Env} {e : BasalEntry} (h : env.profile.basalprofile = [e]) (t u : Int) :
    env.profileAt t = env.profileAt u := by
  unfold Env.profileAt Env.schedJs
  rw [h, basalLookup_single, basalLookup_single]

theorem sched_single {env : Env} {e : BasalEntry} (h : env.profile.basalprofile = [e]) (t u : Int) :
    env.sched t = env.sched u := by
  unfold Env.sched Env.schedJs
  rw [h, basalLookup_single, basalLookup_single]

/-! ### R_U -/

/-- The conditions of R_U (`docs/uppaal-plan.md`, section 3) for a run with origin `t0`
    and rate bound `B`, except BolusSeen, the reading conditions and the SMB interval,
    which `ruB` checks as Booleans. -/
structure RU (env : Env) (r : Run Event) (t0 : Int) (B : Rat) : Prop where
  validRun : ValidRun env r
  profile : ∀ t, ValidProfile (env.profileAt t)
  schedPos : ∀ t, 0 < env.sched t
  schedConst : ∀ t u, env.sched t = env.sched u
  rateCap : RateCap env B
  schedCap : ∀ t, env.sched t ≤ B
  invTemp : InvTemp env.init
  invRate : InvRate B env.init
  initTemp : ∀ tp, env.initTemp = some tp → tp.start ≤ t0 ∧ 0 ≤ tp.rate
  origin : ∀ st ∈ r, t0 ≤ st.time

/-- BolusSeen with the boluses of the initial history at times `pre`. -/
def bolusSeenPreB (env : Env) (r : Run Event) (pre : List Int) : Bool :=
  bolusSeenB env r && (cycles env r).all fun c =>
    let lbt := (iobOut env c.pre c.time c.inp.autosens_data).lastBolusTime
    pre.all fun tb => (JsNum.fin tb ≤ʲ lbt)

/-- Readings also have positive times. -/
def readingsPosB (r : Run Event) : Bool :=
  r.all fun st => st.events.all fun | .reading x => decide (0 < x.trueTime) | _ => true

/-- The Boolean check of R_U at the origin `t0`, with rate bound `B` and the times `pre`
    of the boluses in the initial history. -/
def ruB (env : Env) (r : Run Event) (t0 : Int) (B : Rat) (pre : List Int) : Bool :=
  validRunB env r && validProfileB (env.profileAt t0) && decide (0 < env.sched t0) &&
  decide (env.sched t0 ≤ B) &&
  (match getMaxSafeBasal (env.profileAt t0) with
   | .fin M => decide (rbR M env.profile.model ≤ B)
   | .nan => true) &&
  (match env.initTemp with
   | none => true
   | some tp => decide (tp.deadline ≤ tp.start + 120 * 60000) &&
       decide (0 < tp.rate → tp.deadline ≤ tp.start + 30 * 60000) &&
       decide (tp.rate ≤ B) && decide (tp.start ≤ t0) && decide (0 ≤ tp.rate)) &&
  r.all (fun st => decide (t0 ≤ st.time)) &&
  bolusSeenPreB env r pre && readingsOkB r && readingsPosB r && smbThreeB env r

theorem ru_of {env : Env} {r : Run Event} {t0 : Int} {B : Rat} {pre : List Int} {e : BasalEntry}
    (he : env.profile.basalprofile = [e]) (h : ruB env r t0 B pre = true) : RU env r t0 B := by
  unfold ruB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hp⟩, hpos⟩, hcap⟩, hM⟩, hit⟩, horig⟩, -⟩, -⟩, -⟩, -⟩ := h
  refine ⟨validRun_of_B hv, fun t => ?_, fun t => ?_, fun t u => sched_single he t u, ?_,
    fun t => ?_, ?_, ?_, ?_, ?_⟩
  · rw [profileAt_single he t t0]; exact validProfileB_sound hp
  · rw [sched_single he t t0]; exact hpos
  · intro t M hMt
    rw [profileAt_single he t t0] at hMt
    rw [hMt] at hM
    simpa using hM
  · rw [sched_single he t t0]; exact hcap
  · intro tp htp
    simp only [Env.init] at htp
    rw [htp] at hit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hit
    exact ⟨hit.1.1.1.1, hit.1.1.1.2⟩
  · intro tp htp
    simp only [Env.init] at htp
    rw [htp] at hit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hit
    exact hit.1.1.2
  · intro tp htp
    rw [htp] at hit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hit
    exact ⟨hit.1.2, hit.2⟩
  · intro st hst
    exact of_decide_eq_true (List.all_eq_true.mp horig st hst)

/-! ### T2 predicates of the witness queries -/

/-- The times of the boluses in a log. -/
def bolusTimes (s : PState) : List Int := s.log.filterMap fun | .bolus t _ _ => some t | _ => none

/-- A cycle before the first reading (P1-w-noread). -/
def noReadCycleB (env : Env) (r : Run Event) : Bool :=
  (cycles env r).any fun c => c.pre.readings.isEmpty

/-- An issued Increase with a fresh glucose status (P1-w-inc): units, or a rate above
    `profileCurrentBasal`, and the status of the readings, not stale. -/
def increaseFreshB (env : Env) (r : Run Event) : Bool :=
  (cycles env r).any fun c =>
    (c.res.units.isSome ||
      (match c.res.rate with
       | some x => (x >ʲ profileCurrentBasal (env.profileAt c.time))
       | none => false)) &&
    (match c.inp.glucose_status with
     | some gs => !cgmStale (gluVals (.fin c.time) gs)
     | none => false)

/-- Issued finite units with no earlier bolus in the log or the initial history
    (P5-w-first). -/
def firstUnitsB (env : Env) (r : Run Event) (pre : List Int) : Bool :=
  pre.isEmpty && (cycles env r).any fun c =>
    (match c.res.units with | some (.fin _) => true | _ => false) && (bolusTimes c.pre).isEmpty

/-- Issued finite units at least `gap` ms after the newest earlier bolus
    (P5-w-spaced). -/
def spacedUnitsB (env : Env) (r : Run Event) (pre : List Int) (gap : Int) : Bool :=
  (cycles env r).any fun c =>
    let bs := bolusTimes c.pre ++ pre
    (match c.res.units with | some (.fin _) => true | _ => false) && !bs.isEmpty &&
    bs.all fun tb => decide (tb + gap ≤ c.time)

/-- A cycle less than `gap` ms after a bolus that issues no units (P5-w-early). -/
def earlyNoUnitsB (env : Env) (r : Run Event) (pre : List Int) (gap : Int) : Bool :=
  (cycles env r).any fun c =>
    c.res.units.isNone && (bolusTimes c.pre ++ pre).any fun tb => decide (c.time < tb + gap)

/-- The accepted, valid microboluses of a run: their times. -/
def smbTimes (env : Env) (r : Run Event) : List Int := (cycles env r).filterMap fun c =>
  match c.out, validate c.res with
  | .accepted, some { bolus := some _u, .. } => some c.time
  | _, _ => none

/-- A positive user bolus and a cycle in the same step (P5-w-user-cycle). -/
def userBolusCycleB (r : Run Event) : Bool :=
  r.any fun st => (st.events.any fun | .userBolus u => decide (0 < u) | _ => false) &&
    (st.events.any fun | .cycle .. => true | _ => false)

/-- A step with a reading (cgm-w). -/
def readingStepB (r : Run Event) : Bool :=
  r.any fun st => st.events.any fun | .reading _ => true | _ => false

/-- An accepted zero temp of 120 minutes from a cycle, still delivered `after` ms after
    the close at the last step (F-20). -/
def f20B (env : Env) (r : Run Event) (after : Int) : Bool :=
  ((cycles env r).any fun c => c.out == .accepted &&
    (validate c.res).any fun cmd => cmd.temp == some (0, 120)) &&
  (match r.getLast? with
   | some st => rateAt env r (st.time + after) == 0
   | none => false)

end LeanAID.Time.Replay
