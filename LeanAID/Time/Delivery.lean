/-
  LeanAID.Time.Delivery — the basal part of P6 (R20, docs/timing-plan.md, item T5):
  the pump rate is bounded at every millisecond of a legal run, so the insulin the
  pump delivers by rate over any window [t, t + W) is at most `B · W`.

  The microbolus part of P6 needs P5 derived (spacing in real time), which needs to
  know that `Iob.generate` reports the last accepted bolus (`lastBolusTime`). The
  kernel cannot look inside `generate` (FINDINGS F-22), so that part is not done
  here; see the handoff in `docs/LOG.md`.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import LeanAID.Time.Pump

namespace LeanAID.Time

open LeanAID LeanAID.Proofs

/-- Every temp of the state has a rate at most `B`. -/
def InvRate (B : Rat) (s : PState) : Prop := ∀ tp, s.temp = some tp → tp.rate ≤ B

/-- The envelope hypothesis on the fixed profile: at every time, the profile the
    cycle sees has a numeric `maxSafeBasal` M with `round_basal(M) ≤ B`. -/
def RateCap (env : Env) (B : Rat) : Prop :=
  ∀ t M, getMaxSafeBasal (env.profileAt t) = .fin M → rbR M env.profile.model ≤ B

theorem invRate_applyEvent {env : Env} {B : Rat} (hB : RateCap env B) {t : Int} {s : PState} {e : Event}
    (hs : InvRate B s)
    (hc : ∀ c ∈ cyclesEvents t s [e], LegalCycle env c.time c.pre c.inp c.res ∧ ValidInput c.inp) :
    InvRate B (applyEvent t s e) := by
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
            · simp only [Option.some.injEq] at htp; subst htp
              obtain ⟨dq, hr, -, -, -⟩ := validate_temp hv hct
              obtain ⟨L, V⟩ := hc { time := t, pre := s, inp, res, out := .accepted } (by simp [cyclesEvents])
              simp only at L V
              have vp := V.validProfile L.profile
              obtain ⟨-, M, -, -, hM, -, hMpos⟩ := maxSafeBasal_exists vp
              rw [L.result] at hr
              have := rate_le_roundBasal_maxSafeBasal V L.profile hM hr
              show r ≤ B
              exact Rat.le_trans this.2 (hB t M hM)

theorem invRate_foldl_events {env : Env} {B : Rat} (hB : RateCap env B) {t : Int} :
    ∀ {s : PState} {es : List Event}, InvRate B s →
      (∀ c ∈ cyclesEvents t s es, LegalCycle env c.time c.pre c.inp c.res ∧ ValidInput c.inp) →
      InvRate B (es.foldl (applyEvent t) s)
  | _, [], hs, _ => hs
  | s, e :: es, hs, hc => by
    simp only [List.foldl]
    apply invRate_foldl_events hB (invRate_applyEvent hB hs ?_)
    · intro c hc'; exact hc c (by simp only [cyclesEvents, List.mem_append]; right; exact hc')
    · intro c hc'; exact hc c (by simp only [cyclesEvents] at hc' ⊢; simp only [List.mem_append]; left; simpa using hc')

theorem invRate_take {env : Env} {B : Rat} (hB : RateCap env B) : ∀ {s : PState} {r : Run Event}, InvRate B s →
    (∀ c ∈ cyclesFrom s r, LegalCycle env c.time c.pre c.inp c.res ∧ ValidInput c.inp) →
    ∀ n, InvRate B ((r.take n).foldl applyStep s)
  | _, [], hs, _, n => by simpa using hs
  | _, _ :: _, hs, _, 0 => by simpa using hs
  | s, st :: r, hs, hc, n + 1 => by
    simp only [List.take_succ_cons, List.foldl]
    apply invRate_take hB
    · exact invRate_foldl_events hB hs (fun c h => hc c (by simp only [cyclesFrom, List.mem_append]; left; exact h))
    · exact fun c h => hc c (by simp only [cyclesFrom, List.mem_append]; right; exact h)

/-- **Rate envelope.** In a legal run with valid input, if `round_basal(maxSafeBasal)`
    is at most `B` at every time (`RateCap`), the schedule is at most `B`, and the
    initial temp's rate is at most `B`, then the pump rate is at most `B` at every
    millisecond. With `B = max(M, S)` this is the rate part of the plan's envelope. -/
theorem rate_envelope {env : Env} {r : Run Event} {B : Rat} (hl : Legal env r) (hv : ValidRun env r)
    (hB : RateCap env B) (hS : ∀ k, env.sched k ≤ B) (hinit : InvRate B env.init) (k : Int) :
    rateAt env r k ≤ B := by
  have hinv : InvRate B (pumpAt env r k) := by
    obtain ⟨n, hn⟩ := upTo_take hl.increasing k
    unfold pumpAt stateAt
    rw [hn]
    exact invRate_take hB hinit (fun c hc => ⟨hl.cycle c hc, hv c hc⟩) n
  unfold rateAt rateIn tempRate
  cases ht : (pumpAt env r k).temp with
  | none => exact hS k
  | some tp =>
    simp only
    split
    · exact hinv tp ht
    · exact hS k

/-- **P6, basal part (R20).** Under the same hypotheses, the insulin the pump
    delivers by rate over any window `[t, t + n)` of `n` milliseconds is at most
    `B · n / 3 600 000` units (`B` in U/h). Microboluses are not included. -/
theorem p6_basal {env : Env} {r : Run Event} {B : Rat} (hl : Legal env r) (hv : ValidRun env r)
    (hB : RateCap env B) (hS : ∀ k, env.sched k ≤ B) (hinit : InvRate B env.init) (t : Int) (n : Nat) :
    integral (rateAt env r) t n ≤ B * n / msPerHour :=
  integral_le_const t n (fun k _ => rate_envelope hl hv hB hS hinit k)

end LeanAID.Time
