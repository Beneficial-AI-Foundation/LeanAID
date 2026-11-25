import LeanAID.Fixed.Combined
import LeanAID.Fixed.Proofs.Rounding
import LeanAID.Fixed.Proofs.Undated
import LeanAID.Fixed.Proofs.MaxBasal
import LeanAID.Fixed.Proofs.LowGlucose
import LeanAID.Fixed.Proofs.SplitTimespan

/-!
# The combined fixes: nothing else changed

* `determineBasalFixed_eq`: if none of the triggers of F-04, F-11, F-12, F-23 holds, the
  corrected `determine_basal` is oref0's. No other hypothesis.
* `generateFixed_eq`: if the F-24 trigger does not hold, the corrected IOB is oref0's.
* `validInput_of_fixed`, `validInputFixed_of_valid`: `ValidInputFixed` is `ValidInput`
  without V2, V3, V10 for a missing `max_basal` or `max_daily_basal`; with a numeric
  `maxSafeBasal` the two agree.
* Lemmas on the shape of the corrected result, used in `Fixed/Proofs/Safety.lean`.
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Proofs LeanAID.Time JsNum

theorem capRate_units (p : Profile) (r : Result) : (capRate p r).units = r.units := by
  unfold capRate; split
  · dsimp only; split <;> rfl
  · rfl

theorem capRate_duration (p : Profile) (r : Result) : (capRate p r).duration = r.duration := by
  unfold capRate; split
  · dsimp only; split <;> rfl
  · rfl

theorem determineBasalFixed_units (inp : DBInputs) :
    (determineBasalFixed inp).units = (determineBasalUncapped inp).units := by
  unfold determineBasalFixed; split
  · exact capRate_units _ _
  · rfl

/-- The F-12 trigger is false exactly when the corrected version does not refuse. -/
theorem uncapped_of_ok {inp : DBInputs} {p : Profile} (hs : stProfile inp = .ok p) (hok : maxSafeOk p = true) :
    determineBasalUncapped inp = (match dbPreludeF11 inp with
      | .error r => r
      | .ok pre => dbDosePatched (dbPredict inp pre)) := by
  unfold determineBasalUncapped
  rw [hs]; simp only [hok, ite_true]
  rfl

/-- **Nothing else changed.** If none of the triggers of F-04, F-11, F-12 and F-23 holds,
    the corrected `determine_basal` returns exactly oref0's result. -/
theorem determineBasalFixed_eq (inp : DBInputs) (h04 : ¬ TriggerF04 inp) (h11 : ¬ TriggerF11 inp)
    (h12 : ¬ TriggerF12 inp) (h23 : ¬ TriggerF23 inp) :
    determineBasalFixed inp = determineBasal inp := by
  have hu : determineBasalUncapped inp = determineBasal inp := by
    cases hs : stProfile inp with
    | error r =>
      unfold determineBasalUncapped; rw [hs]
      exact (determineBasal_of_stProfile_error hs).symm
    | ok p =>
      have hok : maxSafeOk p = true := by
        have := determineBasalF12_eq inp h12
        unfold determineBasalF12 at this
        rw [hs] at this
        cases hm : maxSafeOk p
        · exfalso
          have hp := stProfile_ok hs
          have hcb : p.current_basal.isSome := by
            unfold stProfile at hs; rw [hp] at hs
            cases hc : p.current_basal with
            | none => simp [hc] at hs
            | some _ => rfl
          exact h12 (by simp [TriggerF12, triggerF12, hp, hcb, hm])
        · rfl
      rw [uncapped_of_ok hs hok, dbPreludeF11_eq h11]
      have := determineBasalF23_eq inp h23
      unfold determineBasalF23 determineBasalPatched at this
      exact this
  unfold determineBasalFixed
  rw [hu]
  split
  · rename_i p hp
    have := determineBasalF04_eq inp h04
    unfold determineBasalF04 at this
    rw [hp] at this
    exact this
  · rfl

/-- **Nothing else changed, IOB.** If oref0's `splitTimespan` drops no piece of any temp
    it splits (`¬ TriggerF24`), the corrected IOB is oref0's IOB. -/
theorem generateFixed_eq (inp : Iob.HistoryInputs) (c : Bool) (h : ¬ TriggerF24 inp) :
    generateFixed inp c = Iob.generate inp c :=
  generateF24_eq inp c h

/-- The triggers of `aid-lean --fixed`: the list is empty exactly when no trigger holds. -/
theorem triggers_nil (inp : DBInputs) :
    triggers inp = [] ↔ ¬ TriggerF04 inp ∧ ¬ TriggerF11 inp ∧ ¬ TriggerF12 inp ∧ ¬ TriggerF23 inp := by
  unfold triggers TriggerF04 TriggerF11 TriggerF12 TriggerF23
  cases triggerF04 inp <;> cases triggerF11 inp <;> cases triggerF12 inp <;> cases triggerF23 inp <;> simp

/-! ### Valid input -/

/-- `maxSafeBasal` is NaN when `max_basal` or `max_daily_basal` is missing or NaN. -/
theorem maxSafe_nan {p : Profile} (h : p.max_basal.js = .nan ∨ p.max_daily_basal.js = .nan) :
    getMaxSafeBasal p = .nan := by
  unfold getMaxSafeBasal JsNum.min3
  rcases h with h | h
  · rw [h]; rfl
  · rw [h, mul_nan]
    cases p.max_basal.js <;> rfl

/-- A numeric `maxSafeBasal` needs numeric `max_basal` and `max_daily_basal`. -/
theorem maxSafe_fin_parts {p : Profile} {M : Rat} (hM : getMaxSafeBasal p = .fin M) :
    (∃ mb, p.max_basal = some (.fin mb)) ∧ (∃ mdb, p.max_daily_basal = some (.fin mdb)) := by
  have key : ∀ o : Option JsNum, (∀ x, o ≠ some (.fin x)) → o.js = .nan := by
    intro o ho
    cases o with
    | none => rfl
    | some x => cases x with
      | nan => rfl
      | fin x => exact absurd rfl (ho x)
  constructor
  · by_cases h : ∃ mb, p.max_basal = some (.fin mb)
    · exact h
    · have := maxSafe_nan (Or.inl (key _ (fun x hx => h ⟨x, hx⟩)))
      rw [this] at hM; cases hM
  · by_cases h : ∃ mdb, p.max_daily_basal = some (.fin mdb)
    · exact h
    · have := maxSafe_nan (Or.inr (key _ (fun x hx => h ⟨x, hx⟩)))
      rw [this] at hM; cases hM

theorem validProfile_of_fixed {p : Profile} (vp : ValidProfileFixed p) {M : Rat} (hM : getMaxSafeBasal p = .fin M) :
    ValidProfile p := by
  obtain ⟨⟨mb, hmb⟩, ⟨mdb, hmdb⟩⟩ := maxSafe_fin_parts hM
  obtain ⟨cb, hcb, hcb0⟩ := vp.current_basal
  exact { current_basal := vp.current_basal,
          max_basal := ⟨mb, cb, hmb, hcb, vp.max_basal mb cb hmb hcb⟩,
          max_daily_basal := ⟨mdb, cb, hmdb, hcb, vp.max_daily_basal mdb cb hmdb hcb⟩,
          max_daily_safety_multiplier := vp.max_daily_safety_multiplier,
          current_basal_safety_multiplier := vp.current_basal_safety_multiplier,
          autosens_max := vp.autosens_max, max_iob := vp.max_iob, bolus_increment := vp.bolus_increment,
          sens := vp.sens, current_basal_double := vp.current_basal_double,
          max_basal_double := vp.max_basal_double }

/-- With a numeric `maxSafeBasal`, `ValidInputFixed` is `ValidInput`. -/
theorem validInput_of_fixed {inp : DBInputs} (hv : ValidInputFixed inp) {p : Profile} (hp : inp.profile = some p)
    {M : Rat} (hM : getMaxSafeBasal p = .fin M) : ValidInput inp := by
  obtain ⟨p', hp', vp⟩ := hv.profile
  rw [hp] at hp'; cases hp'
  exact { profile := ⟨p, hp, validProfile_of_fixed vp hM⟩, autosens := hv.autosens }

/-- `ValidInputFixed` is weaker than `ValidInput`. -/
theorem validInputFixed_of_valid {inp : DBInputs} (hv : ValidInput inp) : ValidInputFixed inp := by
  obtain ⟨p, hp, vp⟩ := hv.profile
  refine { profile := ⟨p, hp, ?_⟩, autosens := hv.autosens }
  exact { current_basal := vp.current_basal,
          max_basal := fun mb cb hmb hcb => by
            obtain ⟨mb', cb', h1, h2, h3⟩ := vp.max_basal
            rw [hmb] at h1; rw [hcb] at h2; cases h1; cases h2; exact h3,
          max_daily_basal := fun mdb cb hmdb hcb => by
            obtain ⟨mdb', cb', h1, h2, h3⟩ := vp.max_daily_basal
            rw [hmdb] at h1; rw [hcb] at h2; cases h1; cases h2; exact h3,
          max_daily_safety_multiplier := vp.max_daily_safety_multiplier,
          current_basal_safety_multiplier := vp.current_basal_safety_multiplier,
          autosens_max := vp.autosens_max, max_iob := vp.max_iob, bolus_increment := vp.bolus_increment,
          sens := vp.sens, current_basal_double := vp.current_basal_double,
          max_basal_double := vp.max_basal_double }

/-! ### The shape of the corrected result -/

theorem stProfile_cb {inp : DBInputs} {p : Profile} (hs : stProfile inp = .ok p) : p.current_basal.isSome := by
  have hp := stProfile_ok hs
  unfold stProfile at hs; rw [hp] at hs
  cases hc : p.current_basal with
  | none => simp [hc] at hs
  | some _ => rfl

/-- If the fixed prelude succeeds, so does oref0's, with the same values. -/
theorem dbPreludeF11_ok {inp : DBInputs} {pre : Pre} (h : dbPreludeF11 inp = .ok pre) : dbPrelude inp = .ok pre := by
  by_cases h11 : TriggerF11 inp
  · exfalso
    cases hs : stProfile inp with
    | error r =>
      unfold dbPreludeF11 at h; simp [hs, bind, Except.bind] at h
    | ok p =>
      obtain ⟨gs, hgs, e⟩ := determineBasalF11_undated h11 (stProfile_ok hs) (stProfile_cb hs)
      unfold TriggerF11 triggerF11 at h11
      rw [hgs] at h11; simp only at h11
      have hnan : DateFmt.timeClip gs.date.js = .nan := by
        cases hc : DateFmt.timeClip gs.date.js with
        | nan => rfl
        | fin _ => rw [hc] at h11; cases h11
      have herr : cgmErrorF11 (gluVals (.fin inp.clock.now) gs) = true := by
        unfold cgmErrorF11; rw [cgmStaleF11_undated hnan]; simp
      have h2 : stGlucoseF11 inp p = .error (cgmResultF11 inp p (gluVals (.fin inp.clock.now) gs)) := by
        simp [stGlucoseF11, hgs, herr]
      unfold dbPreludeF11 at h
      simp [hs, h2, bind, Except.bind] at h
  · rw [← dbPreludeF11_eq h11]; exact h

/-- If the fixed prelude fails, its result is oref0's or the stale-data result of an
    undated reading. -/
theorem dbPreludeF11_error {inp : DBInputs} {r : Result} (h : dbPreludeF11 inp = .error r) :
    dbPrelude inp = .error r ∨
    ∃ p gs, inp.profile = some p ∧ inp.glucose_status = some gs ∧
      r = cgmResultF11 inp p (gluVals (.fin inp.clock.now) gs) := by
  by_cases h11 : TriggerF11 inp
  · cases hs : stProfile inp with
    | error r' =>
      left
      unfold dbPreludeF11 at h; unfold dbPrelude
      simp [hs, bind, Except.bind] at h ⊢; exact h
    | ok p =>
      right
      obtain ⟨gs, hgs, e⟩ := determineBasalF11_undated h11 (stProfile_ok hs) (stProfile_cb hs)
      unfold determineBasalF11 at e
      rw [h] at e
      exact ⟨p, gs, stProfile_ok hs, hgs, e⟩
  · left; rw [← dbPreludeF11_eq h11]; exact h

/-- The low-glucose branch of the corrected dose phase, or oref0's dose phase. -/
theorem dbDosePatched_cases (c : Ctx) :
    dbDosePatched c = dbDose c ∨
    ((c.bg <ʲ c.threshold && c.iobd.iob.js <ʲ (-c.p.current_basal.js * 20 / 60) && c.minDelta >ʲ 0 &&
        c.minDelta >ʲ c.expectedDelta) = false ∧
     (c.bg <ʲ c.threshold || c.minGuardBG <ʲ c.threshold) = true) := by
  unfold dbDosePatched
  split
  · left; rfl
  · rename_i h1
    split
    · rename_i h2
      right; exact ⟨by simpa using h1, h2⟩
    · left; rfl

end LeanAID.Fixed
