/-
  LeanAID.Time.Lift — per-cycle properties lifted to runs (docs/timing-plan.md,
  item T3): P1 (freshness, faithful and derived), P2 (rate ceiling) and P5 faithful
  (microbolus spacing as oref0 checks it).

  Every theorem is about every cycle of a legal run (`Legal`, T2) whose cycles have
  valid input (`ValidRun`). They are issued-value properties: they speak about the
  `Result` of `LeanAID.step`, whatever the pump does with it.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import LeanAID.Time.System
import LeanAID.Proofs.Headline
import LeanAID.Proofs.ReviewFindings

namespace LeanAID.Time

open LeanAID LeanAID.Proofs JsNum

/-- Valid input (`LeanAID.ValidInput`) at every cycle of the run. -/
def ValidRun (env : Env) (r : Run Event) : Prop := ∀ c ∈ cycles env r, ValidInput c.inp

/-- A result increases insulin: it issues a microbolus, or a rate above the
    profile basal rounded to the pump increment (`profile_current_basal`, oref0
    line 142). -/
def Increase (res : Result) (p : Profile) : Prop :=
  (∃ u, res.units = some u) ∨ (∃ x, res.rate = some x ∧ (x >ʲ profileCurrentBasal p) = true)

theorem gt_self (x : JsNum) : (x >ʲ x) = false := by
  cases x with
  | nan => rfl
  | fin a => simp

theorem profileCurrentBasal_nonneg {p : Profile} (vp : ValidProfile p) :
    ∃ b : Rat, profileCurrentBasal p = .fin b ∧ 0 ≤ b := by
  obtain ⟨cb, hcb, hpos⟩ := vp.current_basal
  refine ⟨rbR cb p.model, ?_, rbR_nonneg _ (Rat.le_of_lt hpos)⟩
  unfold profileCurrentBasal; rw [hcb]; exact roundBasal_fin cb p.model

/-- A result that increases insulin comes from a successful prelude. -/
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

/-- Per call: a result that increases insulin passed the CGM checks of oref0 line
    198 (no error code, noise, stale or flat data). -/
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

/-- **P1 faithful (freshness, as oref0 checks it).** In a legal run with valid
    input, a cycle that issues a microbolus or a rate above `profile_current_basal`
    has a glucose status that passed the CGM checks: in particular the reading is
    not stale, `cgmStale` is false (its age rounded to 0.1 minute is within
    [−5, 12] or is NaN). NaN means an undated reading (F-11). -/
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

/-- **P1 derived (freshness in real time).** If moreover the reading's date is a
    whole number `d` of milliseconds, its real age `(now − d)` is at least −5.05
    minutes and less than 12.05 minutes. The 0.05 minutes are the slack of oref0's
    rounding of the age to 0.1 minute (F-16; the T0 run `stale_1204` shows a reading
    12.04 minutes old giving the maximum rate). -/
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

/-- **P2 (R1 over runs).** In a legal run with valid input, every finite rate issued
    by a cycle is between 0 and `round_basal(maxSafeBasal)` of that cycle's profile. -/
theorem p2_rate_bound {env : Env} {r : Run Event} (hl : Legal env r) (hv : ValidRun env r) :
    ∀ c ∈ cycles env r, ∀ (M x : Rat), getMaxSafeBasal (env.profileAt c.time) = .fin M →
      c.res.rate = some (.fin x) → 0 ≤ x ∧ x ≤ rbR M env.profile.model := by
  intro c hc M x hM hx
  have L := hl.cycle c hc
  rw [L.result] at hx
  exact rate_le_roundBasal_maxSafeBasal (hv c hc) L.profile hM hx

/-- **P5 faithful (microbolus spacing, as oref0 checks it).** In a legal run with
    valid input, a cycle that issues a finite microbolus has `lastBolusAge`, the age
    of the last bolus rounded to 0.1 minute, above `SMBInterval`. The last bolus time
    is the one `Iob.generate` finds in the encoded history of the run. -/
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

end LeanAID.Time
