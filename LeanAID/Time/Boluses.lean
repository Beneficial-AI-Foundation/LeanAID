import LeanAID.Time.Spacing
import LeanAID.Time.Delivery
import LeanAID.Time.Config

/-!
# Insulin delivered by command in a window

**Setting.** A legal run `r` of `env` with `ValidEnv env` and `AutosensOk env r`, a finite
`SMBInterval` `I` (`smbInterval env.profile = .fin I`), and a bound `U` with `SmbCap env r U`:
at every cycle whose prelude succeeds, `smbMaxBolus` is finite and at most `U`. `smbMaxBolus`
is `round(current_basal · m / 60, 1)` with `m` one of `30`, `maxSMBBasalMinutes` and
`maxUAMSMBBasalMinutes`; the IOB and the COB of the cycle only choose `m`.
`smbCap_of_schedule` derives `SmbCap env r (smbCapOf env)` from the profile. For a window `[t, t + n)` in ms, `S` is the list of accepted
microboluses of the final log with time in the window.

**Theorems.**
- `smbTraced_run`: every accepted microbolus in the final log was issued by a cycle of the
  run at its time, and every older action is in that cycle's log or is a temp at that time.
- `smb_gap`: two accepted microboluses at `t₁` and later `t₂` satisfy
  `60000·I − 3000 − 2⁻³⁰ < (t₂ − t₁) · (1 + 2⁻⁵⁰)`: they are more than `I − 0.05` minutes
  apart up to double rounding.
- `p6_bolus`: `S` is empty or `(|S| − 1) · (60000·I − 3000 − 2⁻³⁰) < n · (1 + 2⁻⁵⁰)`, and the
  units of `S` sum to at most `|S| · (U + U·2⁻⁵⁰ + 2⁻⁹⁰)`.
- `p6_delivered` (R20): under the hypotheses of `p6_basal` as well, the basal integral over
  the window plus the units of `S` is at most `B · n / msPerHour + |S| · (U + U·2⁻⁵⁰ + 2⁻⁹⁰)`.
- `smbCap_of_schedule`: `ValidSchedule env` and `SmbMinutesOk env` give
  `SmbCap env r (smbCapOf env)` in a legal run.
- `p6_delivered_sched` (R20): `p6_delivered` with `B = scheduleCap env` and
  `U = smbCapOf env`, from configuration hypotheses only.

User boluses (`userBolus` events) are not commands of the loop and are not counted.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Iob LeanAID.Proofs

/-- Whether an action is a microbolus: a bolus that `applyCmd` logged from a loop command,
    not a user bolus. -/
def Action.isSmb : Action → Bool
  | .bolus _ _ true => true
  | _ => false

/-- The units of a bolus action, 0 for a temp. -/
def Action.units : Action → Rat
  | .bolus _ u _ => u
  | .temp .. => 0

/-- Every accepted microbolus `bolus t₂ u₂` of the log `L` was issued by a cycle `c ∈ C` at
    time `t₂` whose result has units `u₂ > 0`, and every action older than it in `L` is in
    `c.pre.log` or is a temp at time `t₂`. -/
def SmbTraced (C : List CycleAt) (L : List Action) : Prop :=
  ∀ t2 u2 L2, (Action.bolus t2 u2 true :: L2) <:+ L →
    ∃ c ∈ C, c.time = t2 ∧ c.res.units = some (.fin u2) ∧ 0 < u2 ∧
      ∀ b ∈ L2, b ∈ c.pre.log ∨ ∃ r d, b = .temp t2 r d

theorem SmbTraced.mono {C C' : List CycleAt} {L : List Action} (h : SmbTraced C L)
    (hC : ∀ c ∈ C, c ∈ C') : SmbTraced C' L := by
  intro t2 u2 L2 hs
  obtain ⟨c, hc, rest⟩ := h t2 u2 L2 hs
  exact ⟨c, hC c hc, rest⟩

theorem SmbTraced.cons {C : List CycleAt} {L : List Action} {x : Action} (h : SmbTraced C L)
    (hx : x.isSmb = false) : SmbTraced C (x :: L) := by
  intro t2 u2 L2 hs
  rcases List.suffix_cons_iff.mp hs with he | hs
  · cases he; simp [Action.isSmb] at hx
  · exact h t2 u2 L2 hs

theorem SmbTraced.tail {C : List CycleAt} {L : List Action} {x : Action} (h : SmbTraced C (x :: L)) :
    SmbTraced C L := fun t2 u2 L2 hs => h t2 u2 L2 (hs.trans (List.suffix_cons x L))

theorem validate_bolus {res : Result} {cmd : Cmd} (h : validate res = some cmd) {u : Rat}
    (hb : cmd.bolus = some u) : res.units = some (.fin u) ∧ 0 < u := by
  unfold validate at h
  cases ht : validateTemp res <;> cases hbo : validateBolus res <;> simp [ht, hbo, bind, Option.bind] at h
  subst h
  simp only at hb
  subst hb
  unfold validateBolus at hbo
  split at hbo
  · cases hbo
  · split at hbo
    · cases hbo; exact ⟨by assumption, by assumption⟩
    · cases hbo
  · cases hbo

theorem smbTraced_applyEvent {C : List CycleAt} {t : Int} {s : PState} (e : Event)
    (h : SmbTraced C s.log) : SmbTraced (C ++ cyclesEvents t s [e]) (applyEvent t s e).log := by
  have hC : ∀ c ∈ C, c ∈ C ++ cyclesEvents t s [e] := fun c hc => List.mem_append_left _ hc
  cases e with
  | reading rd => exact h.mono hC
  | userBolus u =>
    by_cases hu : 0 < u
    · simp only [applyEvent, hu, ite_true]
      exact (h.mono hC).cons rfl
    · simp only [applyEvent, hu, ite_false]
      exact h.mono hC
  | cycle inp res out =>
    cases out with
    | lost => exact h.mono hC
    | accepted =>
      have hc0 : ({ time := t, pre := s, inp, res, out := .accepted } : CycleAt) ∈ C ++ cyclesEvents t s [.cycle inp res .accepted] := by
        simp [cyclesEvents]
      cases hv : validate res with
      | none => simp only [applyEvent, hv]; exact h.mono hC
      | some cmd =>
        simp only [applyEvent, hv]
        rcases cmd with ⟨tmp, bol⟩
        have hT : SmbTraced (C ++ cyclesEvents t s [.cycle inp res .accepted])
            (applyCmd t s { temp := tmp, bolus := none }).log := by
          cases tmp with
          | none => exact h.mono hC
          | some rd => exact (h.mono hC).cons rfl
        cases bol with
        | none => exact hT
        | some u =>
          obtain ⟨hun, hupos⟩ := validate_bolus hv (u := u) rfl
          intro t2 u2 L2 hs
          have hlog : (applyCmd t s { temp := tmp, bolus := some u }).log =
              Action.bolus t u true :: (applyCmd t s { temp := tmp, bolus := none }).log := by
            cases tmp <;> rfl
          rw [hlog] at hs
          rcases List.suffix_cons_iff.mp hs with he | hs
          · injection he with he1 he2
            injection he1 with ht hu
            subst ht hu he2
            refine ⟨_, hc0, rfl, hun, hupos, fun b hb => ?_⟩
            cases tmp with
            | none => exact Or.inl hb
            | some rd =>
              simp only [applyCmd, List.mem_cons] at hb
              rcases hb with hb | hb
              · exact Or.inr ⟨rd.1, rd.2, hb⟩
              · exact Or.inl hb
          · exact hT t2 u2 L2 hs

theorem smbTraced_events {t : Int} : ∀ (es : List Event) {C : List CycleAt} {s : PState},
    SmbTraced C s.log → SmbTraced (C ++ cyclesEvents t s es) (es.foldl (applyEvent t) s).log
  | [], C, s, h => by simpa [cyclesEvents] using h
  | e :: es, C, s, h => by
    have h1 := smbTraced_applyEvent (t := t) e h
    have h2 := smbTraced_events (t := t) es h1
    refine h2.mono (fun c hc => ?_)
    simp only [List.mem_append] at hc
    simp only [cyclesEvents, List.mem_append, List.append_nil] at hc ⊢
    rcases hc with (hc | hc) | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

theorem smbTraced_steps : ∀ (r : Run Event) {C : List CycleAt} {s : PState},
    SmbTraced C s.log → SmbTraced (C ++ cyclesFrom s r) (r.foldl applyStep s).log
  | [], C, s, h => by simpa [cyclesFrom] using h
  | st :: r, C, s, h => by
    have h1 := smbTraced_events (t := st.time) st.events h
    have h2 := smbTraced_steps r h1
    refine h2.mono (fun c hc => ?_)
    simp only [cyclesFrom, List.mem_append] at hc ⊢
    rcases hc with (hc | hc) | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

/-- The state after all steps of a run. -/
def finalState (env : Env) (r : Run Event) : PState := r.foldl applyStep env.init

/-- Every accepted microbolus of a run is traced to the cycle that issued it. -/
theorem smbTraced_run (env : Env) (r : Run Event) : SmbTraced (cycles env r) (finalState env r).log := by
  have h0 : SmbTraced [] env.init.log := by
    intro t2 u2 L2 hs
    have := hs.length_le
    simp [Env.init] at this
  simpa [cycles, finalState] using smbTraced_steps r h0

/-- The accepted microboluses of `L` in the window `[t, t + n)` ms. -/
def smbsIn (L : List Action) (t : Int) (n : Nat) : List Action :=
  L.filter fun a => a.isSmb && decide (t ≤ a.time) && decide (a.time < t + n)

/-- At every cycle of the run whose prelude succeeds, `smbMaxBolus` is finite and at most
    `U`. `smbMaxBolus` is `round(current_basal · m / 60, 1)` with `m` one of `30`,
    `maxSMBBasalMinutes` and `maxUAMSMBBasalMinutes`; the IOB and the COB of the cycle only
    choose `m`. `smbCap_of_schedule` derives the cap from the profile. -/
def SmbCap (env : Env) (r : Run Event) (U : Rat) : Prop :=
  ∀ c ∈ cycles env r, ∀ pre, dbPrelude c.inp = .ok pre →
    ∃ mb, smbMaxBolus (dbPredict c.inp pre) = .fin mb ∧ mb ≤ U

theorem isSmb_eq {a : Action} (h : a.isSmb = true) : ∃ t u, a = .bolus t u true := by
  rcases a with ⟨t, r, d⟩ | ⟨t, u, smb⟩
  · simp [Action.isSmb] at h
  · cases smb
    · simp [Action.isSmb] at h
    · exact ⟨t, u, rfl⟩

theorem suffix_of_mem {L : List Action} {a : Action} (h : a ∈ L) : ∃ L2, (a :: L2) <:+ L := by
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem h
  exact ⟨L2, List.suffix_append L1 _⟩

section
variable {env : Env} {r : Run Event} (hl : Legal env r) (he : ValidEnv env) (ha : AutosensOk env r)
  {I : Rat} (hI : smbInterval env.profile = .fin I)
include hl he ha hI

/-- Let `r` be a legal run with `ValidEnv env`, `AutosensOk env r` and
    `smbInterval env.profile = .fin I`, and let the log `L` satisfy `SmbTraced (cycles env r) L`.
    If `bolus t₂ u₂ true :: L₂` is a suffix of `L` and `bolus t₁ u₁ true ∈ L₂`, then
    `60000·I − 3000 − 2⁻³⁰ < (t₂ − t₁) · (1 + 2⁻⁵⁰)`: the two microboluses are more than
    `I − 0.05` minutes apart up to double rounding. -/
theorem smb_gap {L : List Action} (hL : SmbTraced (cycles env r) L) {t2 t1 : Int} {u2 u1 : Rat}
    {L2 : List Action} (hs : (Action.bolus t2 u2 true :: L2) <:+ L) (hb : Action.bolus t1 u1 true ∈ L2) :
    60000 * I - 3000 - 1 / 2 ^ 30 < ((t2 - t1 : Int) : Rat) * (1 + 1 / 2 ^ 50) := by
  obtain ⟨c, hc, hct, hun, -, hold⟩ := hL t2 u2 L2 hs
  obtain ⟨L3, hs3⟩ := suffix_of_mem hb
  obtain ⟨-, -, -, -, hu1, -⟩ := hL t1 u1 L3 (hs3.trans ((List.suffix_cons _ _).trans hs))
  rcases hold _ hb with hb' | ⟨_, _, hb'⟩
  · have := (p5_gap hl he ha hc hun hb' (Rat.ne_of_gt hu1) hI).2
    rwa [hct] at this
  · cases hb'

theorem smbsIn_pairwise {L : List Action} (hL : SmbTraced (cycles env r) L) (t : Int) (n : Nat) :
    (smbsIn L t n).Pairwise (fun a b =>
      60000 * I - 3000 - 1 / 2 ^ 30 < ((a.time - b.time : Int) : Rat) * (1 + 1 / 2 ^ 50)) := by
  induction L with
  | nil => simp [smbsIn]
  | cons x L ih =>
    have ih := ih hL.tail
    unfold smbsIn at ih ⊢
    rw [List.filter_cons]
    split
    · rename_i hx
      refine List.pairwise_cons.mpr ⟨fun b hb => ?_, ih⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      obtain ⟨t2, u2, rfl⟩ := isSmb_eq hx.1.1
      rw [List.mem_filter] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨t1, u1, rfl⟩ := isSmb_eq hb.2.1.1
      exact smb_gap hl he ha hI hL List.suffix_rfl hb.1
    · exact ih

end

/-- Let `c > 0` and let `x :: xs` be actions, all at or after time `t`, with
    `G < (a.time − b.time) · c` for every `a` before `b` in the list. Then
    `|xs| · G ≤ (x.time − t) · c`. -/
theorem count_le {G c : Rat} (hc : 0 < c) (t : Int) :
    ∀ (x : Action) (xs : List Action), (x :: xs).Pairwise (fun a b => G < ((a.time - b.time : Int) : Rat) * c) →
      (∀ a ∈ x :: xs, t ≤ a.time) →
      ((xs.length : Rat)) * G ≤ ((x.time - t : Int) : Rat) * c
  | x, [], _, hw => by
    have := hw x (by simp)
    have h0 : (0 : Rat) ≤ ((x.time - t : Int) : Rat) := by exact_mod_cast (show (0 : Int) ≤ x.time - t by omega)
    have := Rat.mul_le_mul_of_nonneg_right h0 (Rat.le_of_lt hc)
    simp only [List.length_nil]
    grind
  | x, y :: rest, hp, hw => by
    have ih := count_le hc t y rest (List.pairwise_cons.mp hp).2
      (fun a ha => hw a (List.mem_cons_of_mem _ ha))
    have hxy := (List.pairwise_cons.mp hp).1 y (by simp)
    simp only [List.length_cons] at ih ⊢
    push_cast at ih hxy ⊢
    grind

theorem sum_le {Ub : Rat} : ∀ (xs : List Action), (∀ a ∈ xs, a.units ≤ Ub) →
    (xs.map Action.units).sum ≤ xs.length * Ub
  | [], _ => by simp
  | x :: xs, h => by
    have ih := sum_le xs (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have hx := h x (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    grind

/-- **Microboluses in a window.** Let `r` be a legal run with `ValidEnv env`,
    `AutosensOk env r`, `smbInterval env.profile = .fin I` and `SmbCap env r U`, and let `S`
    be the accepted microboluses of the final log with time in `[t, t + n)` ms. Then `S` is
    empty or `(|S| − 1) · (60000·I − 3000 − 2⁻³⁰) < n · (1 + 2⁻⁵⁰)`, and the units of `S` sum
    to at most `|S| · (U + U·2⁻⁵⁰ + 2⁻⁹⁰)`. The slack `U·2⁻⁵⁰ + 2⁻⁹⁰` per bolus is F-16. -/
theorem p6_bolus {env : Env} {r : Run Event} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) {I : Rat} (hI : smbInterval env.profile = .fin I) {U : Rat}
    (hU : SmbCap env r U) (t : Int) (n : Nat) :
    (smbsIn (finalState env r).log t n = [] ∨
      (((smbsIn (finalState env r).log t n).length : Rat) - 1) * (60000 * I - 3000 - 1 / 2 ^ 30) <
        n * (1 + 1 / 2 ^ 50)) ∧
    ((smbsIn (finalState env r).log t n).map Action.units).sum ≤
      (smbsIn (finalState env r).log t n).length * (U + U / 2 ^ 50 + 1 / 2 ^ 90) := by
  have hT := smbTraced_run env r
  constructor
  · cases hS : smbsIn (finalState env r).log t n with
    | nil => exact Or.inl rfl
    | cons x xs =>
      right
      have hp := smbsIn_pairwise hl he ha hI hT t n
      rw [hS] at hp
      have hw : ∀ a ∈ x :: xs, t ≤ a.time ∧ a.time < t + n := by
        intro a ha'
        rw [← hS] at ha'
        simp only [smbsIn, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at ha'
        exact ⟨ha'.2.1.2, ha'.2.2⟩
      have hc := count_le (G := 60000 * I - 3000 - 1 / 2 ^ 30) (c := 1 + 1 / 2 ^ 50)
        (by decide +kernel) t x xs hp (fun a ha' => (hw a ha').1)
      have hx := (hw x (by simp)).2
      have hx' : ((x.time - t : Int) : Rat) < n := by
        have : x.time - t < (n : Int) := by omega
        exact_mod_cast this
      have hcpos : (0 : Rat) < 1 + 1 / 2 ^ 50 := by decide +kernel
      have := Rat.mul_lt_mul_of_pos_right hx' hcpos
      simp only [List.length_cons]
      push_cast
      grind
  · apply sum_le
    intro a ha'
    simp only [smbsIn, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at ha'
    obtain ⟨t2, u2, rfl⟩ := isSmb_eq ha'.2.1.1
    obtain ⟨L2, hs⟩ := suffix_of_mem ha'.1
    obtain ⟨c, hc, -, hun, -, -⟩ := hT t2 u2 L2 hs
    have hv := validRun_of hl he ha c hc
    rw [(hl.cycle c hc).result] at hun
    obtain ⟨pre, hpre, hlim⟩ := microbolus_limits hv hun
    obtain ⟨mb, hmb, hle⟩ := hU c hc pre hpre
    have := hlim.2.1 mb hmb
    simp only [Action.units]
    grind

/-- **Bounded delivery (R20).** Let `r` be a legal run with `ValidEnv env`,
    `AutosensOk env r`, `RateCap env B`, `env.sched k ≤ B` for all `k`, `InvRate B env.init`,
    `smbInterval env.profile = .fin I` and `SmbCap env r U`, and let `S` be the accepted
    microboluses with time in `[t, t + n)` ms. Then the basal integral over the window plus
    the units of `S` is at most `B · n / msPerHour + |S| · (U + U·2⁻⁵⁰ + 2⁻⁹⁰)`. -/
theorem p6_delivered {env : Env} {r : Run Event} {B : Rat} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) (hB : RateCap env B) (hS : ∀ k, env.sched k ≤ B)
    (hinit : InvRate B env.init) {I : Rat} (hI : smbInterval env.profile = .fin I) {U : Rat}
    (hU : SmbCap env r U) (t : Int) (n : Nat) :
    integral (rateAt env r) t n + ((smbsIn (finalState env r).log t n).map Action.units).sum ≤
      B * n / msPerHour + (smbsIn (finalState env r).log t n).length * (U + U / 2 ^ 50 + 1 / 2 ^ 90) := by
  have h1 := p6_basal hl he ha hB hS hinit t n
  have h2 := (p6_bolus hl he ha hI hU t n).2
  grind

/-- Let `r` be a legal run of `env` with `ValidSchedule env` and `SmbMinutesOk env`. Then
    `SmbCap env r (smbCapOf env)`: at every cycle whose prelude succeeds, `smbMaxBolus` is
    finite and at most `smbCapOf env`. -/
theorem smbCap_of_schedule {env : Env} {r : Run Event} (hl : Legal env r) (hs : ValidSchedule env)
    (hm : SmbMinutesOk env) : SmbCap env r (smbCapOf env) := by
  intro c hc pre hpre
  obtain ⟨p, -, -, -, -, -, h1, -, -, -, -, -, hpp, -⟩ := prelude_ok hpre
  have hp := stProfile_ok h1
  rw [(hl.cycle c hc).profile, Option.some.injEq] at hp
  have hcp : (dbPredict c.inp pre).p = env.profileAt c.time := by rw [hp]; exact hpp
  exact smbMaxBolus_sched hs hm hcp

/-- **Bounded delivery from the profile (R20).** Let `r` be a legal run of `env` with
    `ValidSchedule env`, `SmbMinutesOk env` and `AutosensOk env r`, let the initial temp, if
    any, have rate at most `scheduleCap env` (`InvRate (scheduleCap env) env.init`), let
    `smbInterval env.profile = .fin I`, and let `S` be the accepted microboluses with time in
    `[t, t + n)` ms. Then the basal integral over the window plus the units of `S` is at most
    `scheduleCap env · n / msPerHour + |S| · (U + U·2⁻⁵⁰ + 2⁻⁹⁰)` with `U = smbCapOf env`,
    where `scheduleCap env` and `smbCapOf env` are computed from `env.profile`. -/
theorem p6_delivered_sched {env : Env} {r : Run Event} (hl : Legal env r) (hs : ValidSchedule env)
    (hm : SmbMinutesOk env) (ha : AutosensOk env r) (hinit : InvRate (scheduleCap env) env.init)
    {I : Rat} (hI : smbInterval env.profile = .fin I) (t : Int) (n : Nat) :
    integral (rateAt env r) t n + ((smbsIn (finalState env r).log t n).map Action.units).sum ≤
      scheduleCap env * n / msPerHour + (smbsIn (finalState env r).log t n).length *
        (smbCapOf env + smbCapOf env / 2 ^ 50 + 1 / 2 ^ 90) :=
  p6_delivered hl (validEnv_of_schedule hs) ha (rateCap_of_schedule hs) (sched_le_of_schedule hs)
    hinit hI (smbCap_of_schedule hl hs hm) t n

end LeanAID.Time
