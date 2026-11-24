import LeanAID.Time.Duration

/-!
# Temp expiry in the pump model

**Setting.** The pump model of `LeanAID.Time.System`: the stored temp sets the rate before
its deadline, and the schedule `env.sched` sets it afterwards.

**Objects.**
- `setsTemp st`: some event of step `st` is an accepted cycle whose validated command has a
  temp part, which sets or cancels the stored temp.
- `TempBound tp`: `tp` lasts at most 120 minutes, and at most 30 minutes if its rate is
  positive. `InvTemp s`: the stored temp of `s`, if any, satisfies `TempBound`.
- `InitRemaining env t0`: the initial temp ends at most 120 minutes after `t0`, and at most
  30 minutes after `t0` if its rate is positive. For `t0`, take the time of the first step.
- `TempBoundFrom t0 tp`: `TempBound tp` with the start replaced by `max tp.start t0`.

**Theorems.**
- `p4a_expiry`: in an increasing run, if no step in `(t, k]` satisfies `setsTemp`, the
  stored temp at `k` is the one at `t`, and `rateAt env r k` is its rate before its
  deadline and `env.sched k` afterwards.
- `temp_bound`: in a legal run with `ValidEnv`, `AutosensOk` and `InitRemaining env t0`,
  every stored temp satisfies `TempBoundFrom t0`. `initRemaining_of_invTemp` derives
  `InitRemaining env t0` from `InvTemp env.init` when the initial temp started at or
  before `t0`.
- `p4b_fail_safe`: under the same hypotheses, `rateAt env r k = env.sched k` once
  `max tp.start t0` is 120 minutes before `k`, or 30 minutes if the rate is positive.

These are theorems about the modeled pump, not about pump firmware.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Proofs

/-! ### Which events change the temp -/

/-- An accepted cycle whose validated command has a temp part. -/
def isTempCmd : Event → Bool
  | .cycle _ res .accepted =>
    match validate res with
    | some c => c.temp.isSome
    | none => false
  | _ => false

/-- Some event of the step satisfies `isTempCmd`. -/
def setsTemp (st : Step Event) : Bool := st.events.any isTempCmd

theorem applyCmd_temp (t : Int) (s : PState) (c : Cmd) :
    (applyCmd t s c).temp = match c.temp with
      | none => s.temp
      | some (r, d) => if d = 0 then none else some { rate := r, start := t, deadline := t + d * 60000 } := by
  obtain ⟨tmp, b⟩ := c
  cases tmp with
  | none => cases b <;> rfl
  | some rd => obtain ⟨r, d⟩ := rd; cases b <;> rfl

theorem applyEvent_temp_of_not (t : Int) (s : PState) (e : Event) (h : isTempCmd e = false) :
    (applyEvent t s e).temp = s.temp := by
  cases e with
  | reading r => rfl
  | userBolus u => simp only [applyEvent]; split <;> rfl
  | cycle inp res out =>
    cases out with
    | lost => rfl
    | accepted =>
      simp only [applyEvent]
      simp only [isTempCmd] at h
      cases hv : validate res with
      | none => rfl
      | some c =>
        rw [hv] at h
        rw [applyCmd_temp]
        cases hct : c.temp with
        | none => rfl
        | some _ => simp [hct] at h

theorem foldl_events_temp (t : Int) : ∀ (s : PState) (es : List Event), es.any isTempCmd = false →
    (es.foldl (applyEvent t) s).temp = s.temp
  | _, [], _ => rfl
  | s, e :: es, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp only [List.foldl]
    rw [foldl_events_temp t _ es h.2, applyEvent_temp_of_not t s e h.1]

theorem foldl_steps_temp : ∀ (s : PState) (r : Run Event), (∀ st ∈ r, setsTemp st = false) →
    (r.foldl applyStep s).temp = s.temp
  | _, [], _ => rfl
  | s, st :: r, h => by
    simp only [List.foldl]
    rw [foldl_steps_temp _ r (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    exact foldl_events_temp st.time s st.events (h st List.mem_cons_self)

/-- Let `r` be an increasing run, `t ≤ k`, and suppose no step of `r` with time in `(t, k]`
    satisfies `setsTemp`. Then the stored temp at `k` is the stored temp at `t`, and
    `rateAt env r k` is its rate if `k` is before its deadline, and `env.sched k` if `k` is
    at or after the deadline or no temp is stored. -/
theorem p4a_expiry {env : Env} {r : Run Event} (hinc : Increasing r) {t k : Int} (htk : t ≤ k)
    (hno : ∀ st ∈ r, t < st.time → st.time ≤ k → setsTemp st = false) :
    (pumpAt env r k).temp = (pumpAt env r t).temp ∧
    rateAt env r k = (match (pumpAt env r t).temp with
      | some tp => if k < tp.deadline then tp.rate else env.sched k
      | none => env.sched k) := by
  have htemp : (pumpAt env r k).temp = (pumpAt env r t).temp := by
    unfold pumpAt stateAt
    rw [upTo_split hinc htk, List.foldl_append]
    apply foldl_steps_temp
    intro st hst
    rw [List.mem_filter] at hst
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hst
    exact hno st hst.1 hst.2.1 hst.2.2
  refine ⟨htemp, ?_⟩
  unfold rateAt rateIn tempRate
  rw [htemp]
  cases (pumpAt env r t).temp with
  | none => rfl
  | some tp => simp only; split <;> rfl

/-- Let `validate res` give a command with temp part `(r, d)`, with `d` in minutes.
    Accepting the cycle at time `t` clears the stored temp if `d = 0`, and otherwise stores
    the temp of rate `r`, start `t` and deadline `t + 60000·d`. -/
theorem accepted_temp {t : Int} {s : PState} {inp : DBInputs} {res : Result} {c : Cmd} {r : Rat} {d : Int}
    (hv : validate res = some c) (ht : c.temp = some (r, d)) :
    (applyEvent t s (.cycle inp res .accepted)).temp =
      if d = 0 then none else some { rate := r, start := t, deadline := t + d * 60000 } := by
  simp only [applyEvent, hv, applyCmd_temp, ht]

/-! ### The bound on every temp of a legal run -/

/-- `tp` lasts at most 120 minutes, and at most 30 minutes if its rate is positive. -/
def TempBound (tp : Temp) : Prop :=
  tp.deadline ≤ tp.start + 120 * 60000 ∧ (0 < tp.rate → tp.deadline ≤ tp.start + 30 * 60000)

/-- The stored temp of `s`, if any, satisfies `P`. -/
def InvWith (P : Temp → Prop) (s : PState) : Prop := ∀ tp, s.temp = some tp → P tp

/-- The stored temp of `s`, if any, satisfies `TempBound`. -/
def InvTemp (s : PState) : Prop := InvWith TempBound s

theorem validate_temp {res : Result} {c : Cmd} (h : validate res = some c) {r : Rat} {d : Int}
    (ht : c.temp = some (r, d)) :
    ∃ dq : Rat, res.rate = some (.fin r) ∧ res.duration = some (.fin dq) ∧ (dq : Rat) = (d : Rat) ∧ dq ≤ 120 := by
  unfold validate at h
  cases hvt : validateTemp res with
  | none => simp [hvt] at h
  | some tm =>
    cases hvb : validateBolus res with
    | none => simp [hvt, hvb] at h
    | some b =>
      simp only [hvt, hvb, bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      simp only at ht; subst ht
      unfold validateTemp at hvt
      split at hvt
      · cases hvt
      · rename_i rr dd hr hd
        split at hvt
        · rename_i hc
          simp only [Option.some.injEq] at hvt
          cases hvt
          simp only [validDuration, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hc
          obtain ⟨-, hden, hdd⟩ := hc
          refine ⟨dd, hr, hd, ?_, ?_⟩
          · exact Rat.ext (by simp) (by simp [hden])
          · rcases hdd with h0 | ⟨-, h2⟩
            · subst h0; decide
            · exact h2
        · cases hvt
      · cases hvt

/-- Every temp that cycle `c` stores when accepted satisfies `P`: whenever `validate c.res`
    gives a command with temp part `(r, d)` and `d ≠ 0`, the temp of rate `r`, start `c.time`
    and deadline `c.time + 60000·d` satisfies `P`. -/
def StoresOk (P : Temp → Prop) (c : CycleAt) : Prop :=
  ∀ cmd r d, validate c.res = some cmd → cmd.temp = some (r, d) → d ≠ 0 →
    P { rate := r, start := c.time, deadline := c.time + d * 60000 }

theorem storesOk_mono {P Q : Temp → Prop} (hPQ : ∀ tp, P tp → Q tp) {c : CycleAt} (h : StoresOk P c) :
    StoresOk Q c :=
  fun cmd r d hv ht hd => hPQ _ (h cmd r d hv ht hd)

theorem inv_applyEvent {P : Temp → Prop} {t : Int} {s : PState} {e : Event} (hs : InvWith P s)
    (hc : ∀ c ∈ cyclesEvents t s [e], StoresOk P c) : InvWith P (applyEvent t s e) := by
  cases he : isTempCmd e with
  | false => intro tp htp; rw [applyEvent_temp_of_not t s e he] at htp; exact hs tp htp
  | true =>
    cases e with
    | reading => cases he
    | userBolus => cases he
    | cycle inp res out =>
      cases out with
      | lost => cases he
      | accepted =>
        simp only [isTempCmd] at he
        cases hv : validate res with
        | none => rw [hv] at he; cases he
        | some c =>
          rw [hv] at he
          cases hct : c.temp with
          | none => simp [hct] at he
          | some rd =>
            obtain ⟨r, d⟩ := rd
            intro tp htp
            rw [accepted_temp hv hct] at htp
            split at htp
            · cases htp
            · rename_i hd0
              simp only [Option.some.injEq] at htp; subst htp
              exact hc { time := t, pre := s, inp, res, out := .accepted } (by simp [cyclesEvents]) c r d hv hct hd0

theorem inv_foldl_events {P : Temp → Prop} {t : Int} :
    ∀ {s : PState} {es : List Event}, InvWith P s →
    (∀ c ∈ cyclesEvents t s es, StoresOk P c) → InvWith P (es.foldl (applyEvent t) s)
  | _, [], hs, _ => hs
  | s, e :: es, hs, hc => by
    simp only [List.foldl]
    apply inv_foldl_events (inv_applyEvent hs ?_)
    · intro c hc'; exact hc c (by simp only [cyclesEvents, List.mem_append]; right; exact hc')
    · intro c hc'; exact hc c (by simp only [cyclesEvents] at hc' ⊢; simp only [List.mem_append]; left; simpa using hc')

theorem inv_take {P : Temp → Prop} :
    ∀ {s : PState} {r : Run Event}, InvWith P s → (∀ c ∈ cyclesFrom s r, StoresOk P c) →
    ∀ n, InvWith P ((r.take n).foldl applyStep s)
  | _, [], hs, _, n => by simpa using hs
  | _, _ :: _, hs, _, 0 => by simpa using hs
  | s, st :: r, hs, hc, n + 1 => by
    simp only [List.take_succ_cons, List.foldl]
    apply inv_take
    · exact inv_foldl_events hs (fun c h => hc c (by simp only [cyclesFrom, List.mem_append]; left; exact h))
    · exact fun c h => hc c (by simp only [cyclesFrom, List.mem_append]; right; exact h)

/-- In an increasing run, if the initial state satisfies `InvWith P` and every cycle
    satisfies `StoresOk P`, the state at every time satisfies `InvWith P`. -/
theorem inv_pumpAt {P : Temp → Prop} {env : Env} {r : Run Event} (hinc : Increasing r)
    (hinit : InvWith P env.init) (hc : ∀ c ∈ cycles env r, StoresOk P c) (k : Int) :
    InvWith P (pumpAt env r k) := by
  obtain ⟨n, hn⟩ := upTo_take hinc k
  unfold pumpAt stateAt
  rw [hn]
  exact inv_take hinit hc n

/-- A cycle whose result satisfies `TempOk` stores only temps that satisfy `TempBound`. -/
theorem storesOk_of_tempOk {c : CycleAt} (hok : TempOk c.res) : StoresOk TempBound c := by
  intro cmd r d hv hct hd0
  obtain ⟨dq, hr, hdur, hdq, hle⟩ := validate_temp hv hct
  obtain ⟨-, hrate⟩ := hok dq hdur
  have hd120 : d ≤ 120 := by
    have : (d : Rat) ≤ 120 := by rw [← hdq]; exact hle
    exact_mod_cast this
  refine ⟨by simp only; omega, fun hpos => ?_⟩
  simp only at hpos ⊢
  rcases hrate r hr with h | ⟨-, -, h⟩ | ⟨h, -⟩
  · exfalso; apply hd0; have : (d : Rat) = 0 := by rw [← hdq, h]
    exact_mod_cast this
  · rw [h] at hpos; exact absurd hpos (by decide)
  · have : d = 30 := by
      have : (d : Rat) = 30 := by rw [← hdq, h]
      exact_mod_cast this
    subst this; omega

/-- The stored temp `tp` at `k` gives the scheduled rate once its deadline is at or before `k`. -/
theorem rateAt_of_deadline_le {env : Env} {r : Run Event} {k : Int} {tp : Temp}
    (htp : (pumpAt env r k).temp = some tp) (hk : tp.deadline ≤ k) : rateAt env r k = env.sched k := by
  unfold rateAt rateIn tempRate
  rw [htp]; simp only
  split
  · omega
  · rfl

/-! ### The initial temp bounded from the first step -/

/-- The initial temp, if any, ends at most 120 minutes after `t0`, and at most 30 minutes
    after `t0` if its rate is positive. With `t0` the time of the run's first step, this
    bounds the remaining duration of the initial temp. -/
def InitRemaining (env : Env) (t0 : Int) : Prop :=
  ∀ tp, env.initTemp = some tp →
    tp.deadline ≤ t0 + 120 * 60000 ∧ (0 < tp.rate → tp.deadline ≤ t0 + 30 * 60000)

/-- `tp` ends at most 120 minutes after `max tp.start t0`, and at most 30 minutes after it
    if its rate is positive. -/
def TempBoundFrom (t0 : Int) (tp : Temp) : Prop :=
  tp.deadline ≤ max tp.start t0 + 120 * 60000 ∧
    (0 < tp.rate → tp.deadline ≤ max tp.start t0 + 30 * 60000)

theorem tempBoundFrom_of {t0 : Int} {tp : Temp} (h : TempBound tp) : TempBoundFrom t0 tp :=
  ⟨by have := h.1; omega, fun hp => by have := h.2 hp; omega⟩

/-- `InvTemp env.init` gives `InitRemaining env t0` when the initial temp started at or
    before `t0`. -/
theorem initRemaining_of_invTemp {env : Env} {t0 : Int} (h : InvTemp env.init)
    (hs : ∀ tp, env.initTemp = some tp → tp.start ≤ t0) : InitRemaining env t0 := by
  intro tp htp
  have hb := h tp htp
  have := hs tp htp
  exact ⟨by have := hb.1; omega, fun hp => by have := hb.2 hp; omega⟩

/-- In a legal run with `ValidEnv`, `AutosensOk` and `InitRemaining env t0`, the stored temp
    at every time satisfies `TempBoundFrom t0`. -/
theorem temp_bound {env : Env} {r : Run Event} {t0 : Int} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) (hinit : InitRemaining env t0) (k : Int) :
    InvWith (TempBoundFrom t0) (pumpAt env r k) := by
  refine inv_pumpAt hl.increasing ?_ (fun c hc => ?_) k
  · intro tp htp
    obtain ⟨h1, h2⟩ := hinit tp htp
    exact ⟨by omega, fun hp => by have := h2 hp; omega⟩
  · refine storesOk_mono (fun _ h => tempBoundFrom_of h) (storesOk_of_tempOk ?_)
    rw [(hl.cycle c hc).result]
    exact issued_temp_ok (validRun_of hl he ha c hc)

/-- Let `r` be a legal run with `ValidEnv env`, `AutosensOk env r` and `InitRemaining env t0`,
    and let `tp` be the stored temp at time `k`. Then `rateAt env r k = env.sched k` if
    ```text
    max(tp.start, t0) + 120 min ≤ k,   or   0 < tp.rate  and  max(tp.start, t0) + 30 min ≤ k.
    ```
    For a temp issued in the run at or after `t0`, `max(tp.start, t0) = tp.start`. After the
    last step of a stopped loop, this bounds a running zero temp by 120 minutes (F-20). -/
theorem p4b_fail_safe {env : Env} {r : Run Event} {t0 : Int} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) (hinit : InitRemaining env t0) (k : Int) (tp : Temp)
    (htp : (pumpAt env r k).temp = some tp) :
    (0 < tp.rate → max tp.start t0 + 30 * 60000 ≤ k → rateAt env r k = env.sched k) ∧
    (max tp.start t0 + 120 * 60000 ≤ k → rateAt env r k = env.sched k) := by
  obtain ⟨h120, h30⟩ := temp_bound hl he ha hinit k tp htp
  exact ⟨fun hpos hk => rateAt_of_deadline_le htp (by have := h30 hpos; omega),
    fun hk => rateAt_of_deadline_le htp (by omega)⟩

end LeanAID.Time
