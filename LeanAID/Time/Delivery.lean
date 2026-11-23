import LeanAID.Time.Pump

/-!
# Basal delivery bounds

**Setting.** A legal run `r` of `env` with `ValidEnv env` and `AutosensOk env r`, a rate
`B` in U/h, and:
- `RateCap env B`: every finite `M` with `getMaxSafeBasal (env.profileAt t) = .fin M`
  satisfies `rbR M env.profile.model ≤ B`;
- the schedule cap `env.sched k ≤ B` for all `k`;
- `InvRate B env.init`: the initial temp, if any, has rate at most `B`.

**Theorems.**
- `rate_envelope`: `rateAt env r k ≤ B` for every millisecond `k`.
- `p6_basal`: the basal insulin delivered over `[t, t + n)` ms is at most
  `B · n / msPerHour` U.

Microboluses are not included here; `LeanAID/Time/Boluses.lean` bounds them.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Proofs

/-- The stored temp of `s`, if any, has rate at most `B`. -/
def InvRate (B : Rat) (s : PState) : Prop := InvWith (fun tp => tp.rate ≤ B) s

/-- Every finite value `M` of `getMaxSafeBasal (env.profileAt t)` satisfies
    `rbR M env.profile.model ≤ B`. -/
def RateCap (env : Env) (B : Rat) : Prop :=
  ∀ t M, getMaxSafeBasal (env.profileAt t) = .fin M → rbR M env.profile.model ≤ B

/-- Under `RateCap env B`, a legal cycle with `ValidInput` stores only temps of rate at
    most `B`. -/
theorem storesOk_rate {env : Env} {B : Rat} (hB : RateCap env B) {c : CycleAt}
    (L : LegalCycle env c.time c.pre c.inp c.res) (V : ValidInput c.inp) :
    StoresOk (fun tp => tp.rate ≤ B) c := by
  intro cmd r d hv hct _
  obtain ⟨dq, hr, -, -, -⟩ := validate_temp hv hct
  have vp := V.validProfile L.profile
  obtain ⟨-, M, -, -, hM, -, hMpos⟩ := maxSafeBasal_exists vp
  rw [L.result] at hr
  have := rate_le_roundBasal_maxSafeBasal V L.profile hM hr
  exact Rat.le_trans this.2 (hB c.time M hM)

/-- **Rate envelope.** Let `r` be a legal run with `ValidEnv env`, `AutosensOk env r`,
    `RateCap env B`, `env.sched k ≤ B` for all `k`, and `InvRate B env.init`. Then
    `rateAt env r k ≤ B` for every `k`. -/
theorem rate_envelope {env : Env} {r : Run Event} {B : Rat} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) (hB : RateCap env B) (hS : ∀ k, env.sched k ≤ B)
    (hinit : InvRate B env.init) (k : Int) :
    rateAt env r k ≤ B := by
  have hv := validRun_of hl he ha
  have hinv : InvRate B (pumpAt env r k) :=
    inv_pumpAt hl.increasing hinit (fun c hc => storesOk_rate hB (hl.cycle c hc) (hv c hc)) k
  unfold rateAt rateIn tempRate
  cases ht : (pumpAt env r k).temp with
  | none => exact hS k
  | some tp =>
    simp only
    split
    · exact hinv tp ht
    · exact hS k

/-- **Basal delivery bound.** Let `r` be a legal run with `ValidEnv env`, `AutosensOk env r`,
    `RateCap env B`, `env.sched k ≤ B` for all `k`, and `InvRate B env.init`. Then the basal
    insulin delivered over `[t, t + n)` ms is at most `B · n / msPerHour` U. Boluses are not
    included. -/
theorem p6_basal {env : Env} {r : Run Event} {B : Rat} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) (hB : RateCap env B) (hS : ∀ k, env.sched k ≤ B)
    (hinit : InvRate B env.init) (t : Int) (n : Nat) :
    integral (rateAt env r) t n ≤ B * n / msPerHour :=
  integral_le_const t n (fun k _ => rate_envelope hl he ha hB hS hinit k)

end LeanAID.Time
