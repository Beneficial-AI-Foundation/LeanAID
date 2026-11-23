import LeanAID.Time.Duration
import LeanAID.Proofs.Headline
import LeanAID.Proofs.ReviewFindings

/-!
# Issued-command properties of legal runs

This module keeps the run theorems of the earlier timing design (`docs/timing-plan.md`)
that the UPPAAL work cites. PR 1 on `main` replaced them with other theorems
(`p1_dated`, `p1_true_age`, `p5_gap`), and the definitions of the run model did not
change. `ValidRun` and `profileCurrentBasal_nonneg` now come from `LeanAID.Time.Duration`.

**Setting.** A legal run `r` of `env` (`Legal env r`) whose cycles have valid input
(`ValidRun env r`). The theorems constrain the `Result` of each cycle, whatever the pump
does with it. `Increase res p` holds if `res` issues a microbolus or a rate above
`profileCurrentBasal p`.

**Theorems.**
- `p1_faithful`: a cycle with `Increase` has the glucose status of the run's readings,
  and `cgmStale` is false for it. A NaN age (undated reading) is not excluded.
- `p1_derived`: if that status has an integral date `d`, the reported age
  `(c.time - d) / 60000` lies in `[-5.05, 12.05)` minutes. Nothing relates `d` to the
  true time of a reading (`Reading.trueTime`).
- `p2_rate_bound`: every finite issued rate lies in `[0, rbR M model]`, where
  `getMaxSafeBasal (env.profileAt c.time) = .fin M`.
- `p3_temp_ok`: every cycle of a legal run with `ValidRun` satisfies `TempOk`.
- `p5_faithful`: a cycle that issues a finite microbolus satisfies
  `lastBolusAge >ʲ smbInterval` in its computed context. This bounds the reported rounded
  age, not the spacing between accepted boluses.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Proofs JsNum

/-- `res` issues a microbolus, or a rate that compares greater than
    `profileCurrentBasal p` (`profile_current_basal`, `determine-basal.js:142`). -/
def Increase (res : Result) (p : Profile) : Prop :=
  (∃ u, res.units = some u) ∨ (∃ x, res.rate = some x ∧ (x >ʲ profileCurrentBasal p) = true)

private theorem gt_self (x : JsNum) : (x >ʲ x) = false := by
  cases x with
  | nan => rfl
  | fin a => simp

/-- Under `ValidInput`, a result of `determineBasal` with `Increase` has a successful
    `dbPrelude`. -/
theorem increase_prelude_ok {inp : DBInputs} (hv : ValidInput inp) {p : Profile} (hp : inp.profile = some p)
    (hi : Increase (determineBasal inp) p) : ∃ pre, dbPrelude inp = .ok pre := by
  cases hpre : dbPrelude inp with
  | ok pre => exact ⟨pre, rfl⟩
  | error e =>
    exfalso
    have hd : determineBasal inp = e := by unfold determineBasal; rw [hpre]
    rw [hd] at hi
    have hM : ∀ p', inp.profile = some p' → ∃ M, getMaxSafeBasal p' = .fin M ∧ 0 ≤ M := by
      intro p' hp'
      obtain ⟨-, M, -, -, hM, -, hMpos⟩ := maxSafeBasal_exists (hv.validProfile hp')
      exact ⟨M, hM, Rat.le_of_lt hMpos⟩
    obtain ⟨hu, hr⟩ := prelude_error hpre hM
    rcases hi with ⟨u, hu'⟩ | ⟨x, hx, hgt⟩
    · rw [hu] at hu'; cases hu'
    · rcases hr with h | h | ⟨p', hp', h⟩
      · rw [h] at hx; cases hx
      · rw [h] at hx; cases hx
        obtain ⟨b, hb, hb0⟩ := profileCurrentBasal_nonneg (hv.validProfile hp)
        rw [hb] at hgt; simp at hgt; grind
      · rw [hp] at hp'; cases hp'
        rw [h] at hx; cases hx
        rw [gt_self] at hgt; cases hgt

/-- Under `ValidInput`, a result of `determineBasal` with `Increase` has a glucose status
    `gs` with `cgmError (gluVals now gs) = false` (`determine-basal.js:198`). -/
theorem increase_cgm_ok {inp : DBInputs} (hv : ValidInput inp) {p : Profile} (hp : inp.profile = some p)
    (hi : Increase (determineBasal inp) p) :
    ∃ gs, inp.glucose_status = some gs ∧ cgmError (gluVals (.fin inp.clock.now) gs) = false := by
  obtain ⟨pre, hpre⟩ := increase_prelude_ok hv hp hi
  obtain ⟨p', g, -, -, -, -, h1, h2, -⟩ := prelude_ok hpre
  unfold stGlucose at h2
  split at h2
  · cases h2
  · rename_i gs hgs
    refine ⟨gs, hgs, ?_⟩
    simp only at h2
    cases hce : cgmError (gluVals (.fin inp.clock.now) gs)
    · rfl
    · rw [hce] at h2; simp at h2

/-- **P1 faithful.** In a legal run with `ValidRun`, every cycle with `Increase` has the
    glucose status `getLastGlucose (entries c.pre)`, and `cgmStale` is false for it: the
    age rounded to 0.1 minute lies in `[-5, 12]` or is NaN (undated, F-11). -/
theorem p1_faithful {env : Env} {r : Run Event} (hl : Legal env r) (hv : ValidRun env r) :
    ∀ c ∈ cycles env r, Increase c.res (env.profileAt c.time) →
      ∃ gs, c.inp.glucose_status = some gs ∧ gs = (Glucose.getLastGlucose (entries c.pre)).get! ∧
        cgmStale (gluVals (.fin c.time) gs) = false := by
  intro c hc hi
  have L := hl.cycle c hc
  rw [L.result] at hi
  obtain ⟨gs, hgs, herr⟩ := increase_cgm_ok (hv c hc) L.profile hi
  refine ⟨gs, hgs, by rw [← L.glucose, hgs]; rfl, ?_⟩
  rw [← L.now]
  unfold cgmError at herr
  simp only [Bool.or_eq_false_iff] at herr
  exact herr.1.2

/-- **P1 derived.** In a legal run with `ValidRun`, if a cycle with `Increase` has a
    glucose status with integral date `d`, then the reported age `(c.time - d) / 60000`
    lies in `[-5.05, 12.05)` minutes; the 0.05 is the rounding of the age to 0.1 minute
    (F-16). The theorem bounds the age of the reported date, not of the reading's true
    time. -/
theorem p1_derived {env : Env} {r : Run Event} (hl : Legal env r) (hv : ValidRun env r) :
    ∀ c ∈ cycles env r, Increase c.res (env.profileAt c.time) →
      ∀ gs (d : Int), c.inp.glucose_status = some gs → gs.date = some (.fin (d : Rat)) →
        -5 - 1/20 ≤ ((c.time - d : Int) : Rat) / 60000 ∧ ((c.time - d : Int) : Rat) / 60000 < 12 + 1/20 := by
  intro c hc hi gs d hgs hd
  have L := hl.cycle c hc
  have hcb : (env.profileAt c.time).current_basal.isSome := by
    obtain ⟨cb, hcb, -⟩ := ((hv c hc).validProfile L.profile).current_basal
    rw [hcb]; rfl
  rw [L.result] at hi
  simp only [LeanAID.step] at hi
  have hz : ((c.time - d : Int) : Rat) = ((c.inp.clock.now : Rat) - (d : Rat)) := by rw [L.now]; push_cast; rfl
  rw [hz]
  rcases Classical.em (-5 - 1/20 ≤ ((c.inp.clock.now : Rat) - d) / 60000 ∧
      ((c.inp.clock.now : Rat) - d) / 60000 < 12 + 1/20) with hok | hne
  · exact hok
  exfalso
  have hbad : ((c.inp.clock.now : Rat) - d) / 60000 ≥ 12 + 1/20 ∨ ((c.inp.clock.now : Rat) - d) / 60000 < -5 - 1/20 := by
    rcases Classical.em (-5 - 1/20 ≤ ((c.inp.clock.now : Rat) - d) / 60000) with h | h
    · left; grind
    · right; grind
  obtain ⟨hu, hr⟩ := cgm_unreliable_no_increase L.profile hcb hgs (Or.inr (Or.inr (Or.inl ⟨d, hd, hbad⟩)))
  rcases hi with ⟨u, hu'⟩ | ⟨x, hx, hgt⟩
  · rw [hu] at hu'; cases hu'
  · obtain ⟨b, hb, hb0⟩ := profileCurrentBasal_nonneg ((hv c hc).validProfile L.profile)
    rcases hr with ⟨ct, -, -, h⟩ | h | ⟨h, -⟩
    · rw [h] at hx; cases hx; rw [gt_self] at hgt; cases hgt
    · rw [h] at hx; cases hx; rw [hb] at hgt; simp at hgt; grind
    · rw [h] at hx; cases hx

/-- **P2.** In a legal run with `ValidRun`, every finite rate `x` issued by a cycle at
    time `t` satisfies `0 ≤ x ≤ rbR M env.profile.model`, where
    `getMaxSafeBasal (env.profileAt t) = .fin M`. -/
theorem p2_rate_bound {env : Env} {r : Run Event} (hl : Legal env r) (hv : ValidRun env r) :
    ∀ c ∈ cycles env r, ∀ (M x : Rat), getMaxSafeBasal (env.profileAt c.time) = .fin M →
      c.res.rate = some (.fin x) → 0 ≤ x ∧ x ≤ rbR M env.profile.model := by
  intro c hc M x hM hx
  have L := hl.cycle c hc
  rw [L.result] at hx
  exact rate_le_roundBasal_maxSafeBasal (hv c hc) L.profile hM hx

/-- **P5 faithful.** In a legal run with `ValidRun`, every cycle that issues a finite
    microbolus satisfies `lastBolusAge >ʲ smbInterval` in its computed context, where the
    last bolus time is the one `Iob.generate` finds in the run's history. This bounds the
    reported rounded age, not the spacing between accepted boluses. -/
theorem p5_faithful {env : Env} {r : Run Event} (hl : Legal env r) (hv : ValidRun env r) :
    ∀ c ∈ cycles env r, ∀ u : Rat, c.res.units = some (.fin u) →
      ∃ pre, dbPrelude c.inp = .ok pre ∧ pre.p = env.profileAt c.time ∧
        (lastBolusAge (dbPredict c.inp pre) >ʲ smbInterval (env.profileAt c.time)) = true := by
  intro c hc u hu
  have L := hl.cycle c hc
  rw [L.result] at hu
  obtain ⟨pre, hpre, -, -, -, hage⟩ := microbolus_limits (hv c hc) hu
  obtain ⟨p, -, -, -, -, -, h1, -, -, -, -, -, hpp, -⟩ := prelude_ok hpre
  have hp := stProfile_ok h1
  rw [L.profile] at hp
  have hpe : env.profileAt c.time = p := Option.some.inj hp
  refine ⟨pre, hpre, by rw [hpp, hpe], ?_⟩
  rw [hpe, ← hpp]; exact hage

/-- **P3 over runs.** In a legal run with `ValidRun`, every cycle satisfies `TempOk`. -/
theorem p3_temp_ok {env : Env} {r : Run Event} (hl : Legal env r) (hv : ValidRun env r) :
    ∀ c ∈ cycles env r, TempOk c.res := by
  intro c hc
  rw [(hl.cycle c hc).result]
  exact issued_temp_ok (hv c hc)

end LeanAID.Time
