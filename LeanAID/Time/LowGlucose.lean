import LeanAID.Time.Pump
import LeanAID.Proofs.RateDouble

/-!
# Low glucose suspend at the pump

`lgs_detail` (`LeanAID.Proofs.Hypo`) is a statement about one call: in oref0's low-glucose
branch oref0 issues no microbolus, and it either requests rate 0 with a duration that is NaN
or in `[30, 120]` minutes, or issues no rate while the `currenttemp` input has more than 20
minutes left and rate 0. This file lifts it to the modeled pump over time.

**Definitions.**
- `LowCycle c`: the cycle `c` enters oref0's low-glucose branch: its prelude succeeds, BG or
  `minGuardBG` is below `threshold`, and the first branch of the dose phase is not taken
  (`doseFirstBranch`). Unlike `low_glucose_suspend`, it allows BG below `threshold` and
  rising.
- `ZeroFrom env r t`: the stored temp at `t` has rate 0 and a deadline more than 20 minutes
  after `t`, and `rateAt env r k = 0` for every `k` in `[t, deadline)` such that no step in
  `(t, k]` sets or cancels a temp (`NoTempIn`).
- `InitDouble env`: the initial temp, if any, has a double rate, `rd(x) = x`.
- `DoubleRates env r`: `InitDouble env`, and every finite rate a cycle issues is a double.
  `doubleRates_of_legal` derives it in a legal run from `InitDouble env` and
  `Proofs.rate_double`.

**Theorems.**
- `pumpAt_cycle`: in a legal run the pump state at a cycle's time is the state just after it.
- `low_glucose_pump`: in a legal run with `ValidEnv`, `AutosensOk` and `InitDouble`, an
  accepted `LowCycle` cycle at `t` gives `ZeroFrom env r t`, or oref0 requests rate 0 with a
  NaN duration and the stored temp stays the one before the cycle (F-23). `f23Run_second`
  (`LeanAID.Conformance.F23Run`) gives a legal run that reaches this case.
- `low_glucose_no_smb`: in a legal run with `ValidEnv` and `AutosensOk`, a `LowCycle` cycle
  adds no bolus to the pump log.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Proofs JsNum

/-! ### The state after a cycle -/

theorem cyclesEvents_last {t : Int} : ∀ {s : PState} {es : List Event}, CycleLast es →
    ∀ c ∈ cyclesEvents t s es, es.foldl (applyEvent t) s = applyEvent t c.pre (.cycle c.inp c.res c.out)
  | _, [], _, c, h => by simp [cyclesEvents] at h
  | s, e :: es, hl, c, hc => by
    simp only [cyclesEvents, List.mem_append] at hc
    rcases hc with hc | hc
    · cases e with
      | cycle inp res out =>
        simp only [List.mem_singleton] at hc; subst hc
        cases es with
        | nil => rfl
        | cons x xs => simp [CycleLast, Event.isCycle] at hl
      | _ => simp at hc
    · cases es with
      | nil => simp [cyclesEvents] at hc
      | cons x xs =>
        simp only [List.foldl]
        exact cyclesEvents_last hl.2 c hc

theorem cyclesFrom_split {env : Env} : ∀ {s : PState} {r : Run Event}, LegalFrom env s r →
    ∀ c ∈ cyclesFrom s r, ∃ r₁ st r₂, r = r₁ ++ st :: r₂ ∧ st.time = c.time ∧
      applyStep (r₁.foldl applyStep s) st = applyEvent c.time c.pre (.cycle c.inp c.res c.out)
  | _, [], _, c, h => by simp [cyclesFrom] at h
  | s, st :: r, hl, c, hc => by
    simp only [cyclesFrom, List.mem_append] at hc
    rcases hc with hc | hc
    · have ht := (legal_cyclesEvents hl.2.2.1 c hc).1
      refine ⟨[], st, r, rfl, ht.symm, ?_⟩
      rw [ht]
      exact cyclesEvents_last hl.2.1 c hc
    · obtain ⟨r₁, st', r₂, h1, h2, h3⟩ := cyclesFrom_split hl.2.2.2 c hc
      exact ⟨st :: r₁, st', r₂, by rw [h1]; rfl, h2, h3⟩

theorem upTo_mid {r₁ r₂ : Run Event} {st : Step Event} (hinc : Increasing (r₁ ++ st :: r₂)) :
    upTo (r₁ ++ st :: r₂) st.time = r₁ ++ [st] := by
  unfold Increasing at hinc
  rw [List.pairwise_append, List.pairwise_cons] at hinc
  obtain ⟨-, ⟨h2, -⟩, h3⟩ := hinc
  unfold upTo
  rw [List.filter_append, List.filter_cons]
  have e1 : r₁.filter (fun s => decide (s.time ≤ st.time)) = r₁ := by
    rw [List.filter_eq_self]; intro a ha; have := h3 a ha st List.mem_cons_self; simp; omega
  have e2 : r₂.filter (fun s => decide (s.time ≤ st.time)) = [] := by
    rw [List.filter_eq_nil_iff]; intro a ha; have := h2 a ha; simp; omega
  simp [e1, e2]

/-- In a legal run, the pump state at the time of a cycle is the state just after the
    cycle: the cycle is the last event of its step (`CycleLast`). -/
theorem pumpAt_cycle {env : Env} {r : Run Event} (hl : Legal env r) {c : CycleAt} (hc : c ∈ cycles env r) :
    pumpAt env r c.time = applyEvent c.time c.pre (.cycle c.inp c.res c.out) := by
  obtain ⟨r₁, st, r₂, h1, h2, h3⟩ := cyclesFrom_split hl.steps c hc
  have hinc := hl.increasing
  rw [h1] at hinc
  unfold pumpAt stateAt
  rw [h1, ← h2, upTo_mid hinc, List.foldl_append, h2]
  exact h3

/-! ### Stored temps have double rates -/

/-- The initial temp, if any, has a double rate: `rd(x) = x`. -/
def InitDouble (env : Env) : Prop := ∀ tp, env.initTemp = some tp → Binary64.rd tp.rate = tp.rate

/-- The initial temp's rate and every finite rate that a cycle of `r` issues are doubles:
    `rd(x) = x`. -/
def DoubleRates (env : Env) (r : Run Event) : Prop :=
  InitDouble env ∧ ∀ c ∈ cycles env r, ∀ x, c.res.rate = some (.fin x) → Binary64.rd x = x

/-- Let `r` be a legal run whose initial temp has a double rate. Then `DoubleRates env r`. -/
theorem doubleRates_of_legal {env : Env} {r : Run Event} (hl : Legal env r) (hi : InitDouble env) :
    DoubleRates env r :=
  ⟨hi, fun c hc x hx => by
    rw [(hl.cycle c hc).result] at hx
    exact Proofs.rate_double hx⟩

/-- The stored temp of `s`, if any, has a double rate. -/
def InvDouble (s : PState) : Prop := InvWith (fun tp => Binary64.rd tp.rate = tp.rate) s

/-- Let `r` be a run with increasing step times (`Increasing r`) and `DoubleRates env r`.
    Then at every time `k` the stored temp, if any, has a double rate. -/
theorem double_rate {env : Env} {r : Run Event} (hinc : Increasing r) (hd : DoubleRates env r) (k : Int) :
    InvDouble (pumpAt env r k) :=
  inv_pumpAt hinc (fun tp h => hd.1 tp h) (fun c hc cmd x _ hv hct _ =>
    let ⟨_, hr, _⟩ := validate_temp hv hct; hd.2 c hc x hr) k

/-! ### Low glucose suspend over time -/

/-- The cycle `c` enters oref0's low-glucose branch (`determine-basal.js:912`): its prelude
    succeeds with `pre`, BG or `minGuardBG` is below oref0's `threshold`, and the first branch
    of the dose phase is not taken, `doseFirstBranch pre = false`. -/
def LowCycle (c : CycleAt) : Prop :=
  ∃ pre, dbPrelude c.inp = .ok pre ∧
    ((pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict c.inp pre).minGuardBG <ʲ pre.threshold) = true) ∧
    doseFirstBranch pre = false

/-- A decision procedure for `LowCycle`, for concrete runs. -/
def lowCycleB (c : CycleAt) : Bool :=
  match dbPrelude c.inp with
  | .ok pre => ((pre.bg <ʲ pre.threshold) || ((dbPredict c.inp pre).minGuardBG <ʲ pre.threshold)) &&
      !doseFirstBranch pre
  | .error _ => false

theorem lowCycle_of_b {c : CycleAt} (h : lowCycleB c = true) : LowCycle c := by
  unfold lowCycleB at h
  split at h
  · rename_i pre hpre
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    exact ⟨pre, hpre, h.1, h.2⟩
  · cases h

/-- No step in `(t, k]` sets or cancels a temp. -/
def NoTempIn (r : Run Event) (t k : Int) : Prop :=
  ∀ st ∈ r, t < st.time → st.time ≤ k → setsTemp st = false

/-- From time `t` the pump runs a zero temp: the stored temp at `t` has rate 0 and a
    deadline more than 20 minutes after `t`, and the pump rate is 0 at every `k` in
    `[t, deadline)` such that no step in `(t, k]` sets or cancels a temp. -/
def ZeroFrom (env : Env) (r : Run Event) (t : Int) : Prop :=
  ∃ tp, (pumpAt env r t).temp = some tp ∧ tp.rate = 0 ∧ t + 20 * 60000 < tp.deadline ∧
    ∀ k, t ≤ k → k < tp.deadline → NoTempIn r t k → rateAt env r k = 0

theorem zeroFrom_of {env : Env} {r : Run Event} (hinc : Increasing r) {t : Int} {tp : Temp}
    (htp : (pumpAt env r t).temp = some tp) (h0 : tp.rate = 0) (hdl : t + 20 * 60000 < tp.deadline) :
    ZeroFrom env r t := by
  refine ⟨tp, htp, h0, hdl, fun k htk hk hno => ?_⟩
  obtain ⟨-, hr⟩ := p4a_expiry (env := env) hinc htk hno
  rw [hr, htp]
  simp only [hk, ite_true, h0]

/-- **Low glucose suspend at the pump.** Let `r` be a legal run with `ValidEnv env`,
    `AutosensOk env r` and `InitDouble env`, and let `c` be an accepted cycle of `r` with
    `LowCycle c`: its prelude succeeds with `pre`, BG or `minGuardBG` is below `threshold`, and
    `doseFirstBranch pre = false`. Then either
    - `ZeroFrom env r c.time`: the stored temp has rate 0 and a deadline more than 20 minutes
      after `c.time`, and the pump rate is 0 from `c.time` until that deadline or the next
      step that sets or cancels a temp, whichever comes first; or
    - `c.res` has rate 0 and a NaN duration, and the stored temp at `c.time` is `c.pre.temp`,
      the one before the cycle (F-23). -/
theorem low_glucose_pump {env : Env} {r : Run Event} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) (hi : InitDouble env) {c : CycleAt} (hc : c ∈ cycles env r)
    (hacc : c.out = .accepted) (hlow : LowCycle c) :
    ZeroFrom env r c.time ∨
    (c.res.rate = some 0 ∧ c.res.duration = some .nan ∧ (pumpAt env r c.time).temp = c.pre.temp) := by
  have hd := doubleRates_of_legal hl hi
  obtain ⟨pre, hpre, hlo, hfirst⟩ := hlow
  have hlc := hl.cycle c hc
  have hv := validRun_of hl he ha c hc
  have hres : determineBasal c.inp = c.res := hlc.result.symm
  obtain ⟨hu, hcase⟩ := lgs_detail hv hpre hlo hfirst
  rw [hres] at hu hcase
  have hpost := pumpAt_cycle hl hc
  rw [hacc] at hpost
  rcases hcase with ⟨hr, D, hdur, hD⟩ | ⟨hr, hdur, ct, ctDur, x, hct, hcd, h20, hcr, hx⟩
  · rcases hD with hD | ⟨q, hq, h30, h120⟩
    · subst hD
      right
      have hval : validate c.res = none := by simp [validate, validateTemp, hr, hdur]
      refine ⟨hr, hdur, ?_⟩
      rw [hpost]; simp [applyEvent, hval]
    · subst hq
      left
      have hval : validate c.res = some { temp := some (0, q), bolus := none } := by
        simp [validate, validateTemp, validateBolus, validDuration, hr, hdur, hu,
          show (30 : Rat) ≤ q by exact_mod_cast h30, show (q : Rat) ≤ 120 by exact_mod_cast h120]
      have htemp := accepted_temp (t := c.time) (s := c.pre) (inp := c.inp) hval rfl
      rw [← hpost] at htemp
      simp only [show q ≠ 0 by omega, ↓reduceIte] at htemp
      exact zeroFrom_of hl.increasing htemp rfl (by simp only; omega)
  · left
    have hval : validate c.res = some { temp := none, bolus := none } := by
      simp [validate, validateTemp, validateBolus, hr, hdur, hu]
    have htemp : (pumpAt env r c.time).temp = c.pre.temp := by
      rw [hpost]; exact applyEvent_temp_of_not _ _ _ (by simp [isTempCmd, hval])
    have hcur := hlc.currenttemp
    rw [hct] at hcur
    injection hcur with hcur
    subst hcur
    unfold currentTempAt at hcd hcr
    cases hpt : c.pre.temp with
    | none =>
      rw [hpt] at hcd; simp at hcd; subst hcd; grind
    | some tp =>
      rw [hpt] at hcd hcr
      by_cases hlt : c.time < tp.deadline
      · simp only [hlt, ite_true, Option.some.injEq, JsNum.fin.injEq] at hcd hcr
        subst hcr
        rw [← hcd] at h20
        generalize hn : (tp.deadline - c.time + 59999) / 60000 = n at h20
        have h20' : (20 : Int) < n := by exact_mod_cast h20
        have hpt' : (pumpAt env r c.time).temp = some tp := by rw [htemp, hpt]
        have h0 : tp.rate = 0 := hx (double_rate hl.increasing hd c.time tp hpt')
        exact zeroFrom_of hl.increasing hpt' h0 (by omega)
      · simp only [hlt, ite_false, Option.some.injEq] at hcd
        have : ctDur = 0 := by injection hcd.symm
        subst this; grind

theorem validate_bolus_none {res : Result} (hu : res.units = none) {cmd : Cmd}
    (h : validate res = some cmd) : cmd.bolus = none := by
  unfold validate at h
  have hb : validateBolus res = some none := by simp [validateBolus, hu]
  cases hvt : validateTemp res with
  | none => simp [hvt] at h
  | some tm =>
    simp only [hvt, hb, bind, Option.bind, pure, Option.some.injEq] at h
    rw [← h]

/-- **No microbolus under low glucose.** Let `r` be a legal run with `ValidEnv env` and
    `AutosensOk env r`, and let `c` be a cycle of `r` with `LowCycle c`. Then every bolus at
    `c.time` in the pump log at `c.time` is in the log before `c`. -/
theorem low_glucose_no_smb {env : Env} {r : Run Event} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) {c : CycleAt} (hc : c ∈ cycles env r) (hlow : LowCycle c) :
    ∀ u smb, Action.bolus c.time u smb ∈ (pumpAt env r c.time).log → Action.bolus c.time u smb ∈ c.pre.log := by
  obtain ⟨pre, hpre, hlo, hfirst⟩ := hlow
  have hres : determineBasal c.inp = c.res := (hl.cycle c hc).result.symm
  have hu := (lgs_detail (validRun_of hl he ha c hc) hpre hlo hfirst).1
  rw [hres] at hu
  intro u smb hm
  rw [pumpAt_cycle hl hc] at hm
  cases hout : c.out with
  | lost => rw [hout] at hm; exact hm
  | accepted =>
    rw [hout] at hm
    simp only [applyEvent] at hm
    cases hv : validate c.res with
    | none => rw [hv] at hm; exact hm
    | some cmd =>
      rw [hv] at hm
      have hb := validate_bolus_none hu hv
      obtain ⟨tmp, b⟩ := cmd
      simp only at hb; subst hb
      cases tmp with
      | none => exact hm
      | some rd =>
        obtain ⟨rr, d⟩ := rd
        simp only [applyCmd, List.mem_cons] at hm
        rcases hm with hm | hm
        · cases hm
        · exact hm

end LeanAID.Time
