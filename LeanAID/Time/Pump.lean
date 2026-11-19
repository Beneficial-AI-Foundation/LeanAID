/-
  LeanAID.Time.Pump — P4a (temp expiry) and P4b (fail-safe bound) on the pump
  model of T2 (docs/timing-plan.md, item T4).

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import LeanAID.Time.Duration

namespace LeanAID.Time

open LeanAID LeanAID.Proofs

/-! ### Which events change the temp -/

/-- An event that sets or cancels a temp: an accepted cycle whose validated command
    has a temp part. A microbolus alone is not one. -/
def isTempCmd : Event → Bool
  | .cycle _ res .accepted =>
    match validate res with
    | some c => c.temp.isSome
    | none => false
  | _ => false

/-- A step sets or cancels a temp. -/
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

/-! ### Prefixes of an increasing run -/

theorem upTo_split {r : Run Event} (hinc : Increasing r) {t k : Int} (htk : t ≤ k) :
    upTo r k = upTo r t ++ r.filter (fun s => decide (t < s.time) && decide (s.time ≤ k)) := by
  induction r with
  | nil => rfl
  | cons st rest ih =>
    unfold Increasing at hinc
    rw [List.pairwise_cons] at hinc
    have ih := ih hinc.2
    unfold upTo at ih ⊢
    by_cases h1 : st.time ≤ t
    · simp [List.filter_cons, h1, show st.time ≤ k by omega, show ¬ t < st.time by omega, ih]
    · have hrest : ∀ x ∈ rest, t < x.time := fun x hx => by have := hinc.1 x hx; omega
      have e1 : rest.filter (fun s => decide (s.time ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx; have := hrest x hx; simp; omega
      have e2 : rest.filter (fun s => decide (t < s.time) && decide (s.time ≤ k)) =
          rest.filter (fun s => decide (s.time ≤ k)) := by
        apply List.filter_congr; intro x hx; have := hrest x hx; simp; omega
      by_cases h2 : st.time ≤ k
      · simp [List.filter_cons, h1, h2, show t < st.time by omega, e1, e2]
      · have e3 : rest.filter (fun s => decide (s.time ≤ k)) = [] := by
          rw [List.filter_eq_nil_iff]; intro x hx; have := hinc.1 x hx; simp; omega
        simp [List.filter_cons, h1, h2, e1, e3]
        intro x hx _; have := hinc.1 x hx; omega

/-- **P4a (expiry).** In an increasing run, if no step in `(t, k]` sets or cancels a
    temp (a microbolus alone does not), the pump at `k` is in the temp state it had
    at `t`: the temp runs until its deadline and then the schedule runs. -/
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

/-- An accepted temp command at time `t` with duration `d` minutes starts a temp at
    `t` with deadline `t + d` minutes (or cancels when `d = 0`). -/
theorem accepted_temp {t : Int} {s : PState} {inp : DBInputs} {res : Result} {c : Cmd} {r : Rat} {d : Int}
    (hv : validate res = some c) (ht : c.temp = some (r, d)) :
    (applyEvent t s (.cycle inp res .accepted)).temp =
      if d = 0 then none else some { rate := r, start := t, deadline := t + d * 60000 } := by
  simp only [applyEvent, hv, applyCmd_temp, ht]

/-! ### The bound on every temp of a legal run -/

/-- A temp lasts at most 120 minutes, and at most 30 minutes if its rate is positive. -/
def TempBound (tp : Temp) : Prop :=
  tp.deadline ≤ tp.start + 120 * 60000 ∧ (0 < tp.rate → tp.deadline ≤ tp.start + 30 * 60000)

def InvTemp (s : PState) : Prop := ∀ tp, s.temp = some tp → TempBound tp

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

theorem inv_applyEvent {t : Int} {s : PState} {e : Event} (hs : InvTemp s)
    (hc : ∀ c ∈ cyclesEvents t s [e], TempOk c.res) : InvTemp (applyEvent t s e) := by
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
              obtain ⟨dq, hr, hdur, hdq, hle⟩ := validate_temp hv hct
              have hok : TempOk res := hc { time := t, pre := s, inp, res, out := .accepted } (by simp [cyclesEvents])
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

theorem inv_foldl_events {t : Int} : ∀ {s : PState} {es : List Event}, InvTemp s →
    (∀ c ∈ cyclesEvents t s es, TempOk c.res) → InvTemp (es.foldl (applyEvent t) s)
  | _, [], hs, _ => hs
  | s, e :: es, hs, hc => by
    simp only [List.foldl]
    apply inv_foldl_events (inv_applyEvent hs ?_)
    · intro c hc'; exact hc c (by simp only [cyclesEvents, List.mem_append]; right; exact hc')
    · intro c hc'; exact hc c (by simp only [cyclesEvents] at hc' ⊢; simp only [List.mem_append]; left; simpa using hc')

theorem inv_take : ∀ {s : PState} {r : Run Event}, InvTemp s → (∀ c ∈ cyclesFrom s r, TempOk c.res) →
    ∀ n, InvTemp ((r.take n).foldl applyStep s)
  | _, [], hs, _, n => by simpa using hs
  | _, _ :: _, hs, _, 0 => by simpa using hs
  | s, st :: r, hs, hc, n + 1 => by
    simp only [List.take_succ_cons, List.foldl]
    apply inv_take
    · exact inv_foldl_events hs (fun c h => hc c (by simp only [cyclesFrom, List.mem_append]; left; exact h))
    · exact fun c h => hc c (by simp only [cyclesFrom, List.mem_append]; right; exact h)

theorem upTo_take {r : Run Event} (hinc : Increasing r) (k : Int) : ∃ n, upTo r k = r.take n := by
  induction r with
  | nil => exact ⟨0, rfl⟩
  | cons st rest ih =>
    unfold Increasing at hinc
    rw [List.pairwise_cons] at hinc
    obtain ⟨n, hn⟩ := ih hinc.2
    unfold upTo at hn ⊢
    by_cases h : st.time ≤ k
    · exact ⟨n + 1, by simp [List.filter_cons, h, hn]⟩
    · refine ⟨0, ?_⟩
      have : rest.filter (fun s => decide (s.time ≤ k)) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx; have := hinc.1 x hx; simp; omega
      simp [List.filter_cons, h, this]

/-- Every temp the pump runs in a legal run with valid input lasts at most 120
    minutes, and at most 30 minutes if its rate is positive, provided the initial
    temp does. Uses P3 (`p3_temp_ok`) and pump validation. -/
theorem temp_bound {env : Env} {r : Run Event} (hl : Legal env r) (hv : ValidRun env r)
    (hinit : InvTemp env.init) (k : Int) : InvTemp (pumpAt env r k) := by
  obtain ⟨n, hn⟩ := upTo_take hl.increasing k
  unfold pumpAt stateAt
  rw [hn]
  exact inv_take hinit (p3_temp_ok hl hv) n

/-- **P4b (fail-safe bound).** In a legal run with valid input whose initial temp
    obeys the bound, at any time `k` the pump runs the scheduled basal if the temp of
    its state started at least 30 minutes before `k` with a positive rate, or at
    least 120 minutes before `k`. On a closed run (a stopped loop), `k` can be any
    time after the last step: a positive temp ends within 30 minutes and a zero temp
    within 120 minutes of its start (F-20). -/
theorem p4b_fail_safe {env : Env} {r : Run Event} (hl : Legal env r) (hv : ValidRun env r)
    (hinit : InvTemp env.init) (k : Int) (tp : Temp) (htp : (pumpAt env r k).temp = some tp) :
    (0 < tp.rate → tp.start + 30 * 60000 ≤ k → rateAt env r k = env.sched k) ∧
    (tp.start + 120 * 60000 ≤ k → rateAt env r k = env.sched k) := by
  obtain ⟨h120, h30⟩ := temp_bound hl hv hinit k tp htp
  have key : tp.deadline ≤ k → rateAt env r k = env.sched k := by
    intro hk
    unfold rateAt rateIn tempRate
    rw [htp]; simp only
    split
    · omega
    · rfl
  exact ⟨fun hpos hk => key (by have := h30 hpos; omega), fun hk => key (by omega)⟩

end LeanAID.Time
