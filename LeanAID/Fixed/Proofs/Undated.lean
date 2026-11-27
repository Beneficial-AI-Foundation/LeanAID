import LeanAID.Fixed.Undated
import LeanAID.Proofs.ReviewFindings

/-!
# F-11: theorems about the fixed staleness check

* `determineBasalF11_eq` (**nothing else changed**): if the glucose status has a date that
  is a number (`¬ TriggerF11`), the fixed result is oref0's result. No other hypothesis.
* `f11_fixed` (**the fix works**): with an undated reading, the fixed version never gives a
  microbolus and never raises the rate above the scheduled basal: it replaces a running
  temp above `round_basal(current_basal)` by that rate, sets a zero temp, or issues
  nothing while the running temp is not above it.
* `f11_example`: on the input of `undated_glucose_max_rate`, where oref0 issues its maximum
  of 3.5 U/h, the fixed version issues nothing.
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Proofs JsNum

/-- With a finite age, the fixed test of line 187 is oref0's. -/
theorem cgmStaleF11_of_fin {g : GluVals} {a : Rat} (h : g.minAgo = .fin a) : cgmStaleF11 g = cgmStale g := by
  unfold cgmStaleF11 cgmStale
  rw [h]
  simp only [ofNat_eq, fin_neg, le_fin, ge_fin, gt_fin, lt_fin]
  by_cases h1 : a ≤ 12 <;> by_cases h2 : -5 ≤ a <;> simp [h1, h2] <;> grind

/-- The age of a reading with a numeric date is a number. -/
theorem minAgo_fin {now : Rat} {gs : GlucoseStatus} {b : Rat} (h : DateFmt.timeClip gs.date.js = .fin b) :
    ∃ a, (gluVals (.fin now) gs).minAgo = .fin a := by
  unfold gluVals
  simp only [h, fin_sub]
  rw [show (60 : JsNum) = .fin 60 from rfl, show (1000 : JsNum) = .fin 1000 from rfl,
    fin_div (by decide), fin_div (by decide), rnd, rnd_fin]
  exact ⟨_, rfl⟩

/-- Without the trigger, the fixed glucose stage is oref0's. -/
theorem stGlucoseF11_eq {inp : DBInputs} (h : ¬ TriggerF11 inp) (p : Profile) :
    stGlucoseF11 inp p = stGlucose inp p := by
  unfold stGlucoseF11 stGlucose
  cases hgs : inp.glucose_status with
  | none => rfl
  | some gs =>
    simp only
    have hd : ∃ b, DateFmt.timeClip gs.date.js = .fin b := by
      unfold TriggerF11 triggerF11 at h
      rw [hgs] at h
      simp only at h
      cases hc : DateFmt.timeClip gs.date.js with
      | nan => rw [hc] at h; exact absurd rfl h
      | fin b => exact ⟨b, rfl⟩
    obtain ⟨b, hb⟩ := hd
    obtain ⟨a, ha⟩ := minAgo_fin (now := inp.clock.now) hb
    have hs := cgmStaleF11_of_fin ha
    have he : cgmErrorF11 (gluVals (.fin inp.clock.now) gs) = cgmError (gluVals (.fin inp.clock.now) gs) := by
      unfold cgmErrorF11 cgmError; rw [hs]
    have hreason : ∀ c, cgmReasonF11 c (gluVals (.fin inp.clock.now) gs) = cgmReason c (gluVals (.fin inp.clock.now) gs) := by
      intro c; unfold cgmReasonF11 cgmReason; rw [hs]
    have hr : cgmResultF11 inp p (gluVals (.fin inp.clock.now) gs) = cgmResult inp p (gluVals (.fin inp.clock.now) gs) := by
      unfold cgmResultF11 cgmResult
      simp only [hreason]
      rfl
    rw [he, hr]

/-- Without the trigger, the fixed prelude is oref0's. -/
theorem dbPreludeF11_eq {inp : DBInputs} (h : ¬ TriggerF11 inp) : dbPreludeF11 inp = dbPrelude inp := by
  unfold dbPreludeF11 dbPrelude
  simp only [stGlucoseF11_eq h]

/-- **F-11, nothing else changed.** If the glucose status has a numeric date, the fixed
    result is oref0's result. -/
theorem determineBasalF11_eq (inp : DBInputs) (h : ¬ TriggerF11 inp) :
    determineBasalF11 inp = determineBasal inp := by
  unfold determineBasalF11 determineBasal
  rw [dbPreludeF11_eq h]
  rfl

/-- With the trigger, the fixed staleness test holds. -/
theorem cgmStaleF11_undated {now : Rat} {gs : GlucoseStatus} (h : DateFmt.timeClip gs.date.js = .nan) :
    cgmStaleF11 (gluVals (.fin now) gs) = true := by
  unfold cgmStaleF11 gluVals
  simp [h, rnd, JsNum.round]

/-- With the trigger, `determineBasalF11` returns the stale-data result. -/
theorem determineBasalF11_undated {inp : DBInputs} (ht : TriggerF11 inp) {p : Profile}
    (hp : inp.profile = some p) (hcb : p.current_basal.isSome) :
    ∃ gs, inp.glucose_status = some gs ∧
      determineBasalF11 inp = cgmResultF11 inp p (gluVals (.fin inp.clock.now) gs) := by
  unfold TriggerF11 triggerF11 at ht
  cases hgs : inp.glucose_status with
  | none => rw [hgs] at ht; cases ht
  | some gs =>
    rw [hgs] at ht
    simp only at ht
    have hnan : DateFmt.timeClip gs.date.js = .nan := by
      cases hc : DateFmt.timeClip gs.date.js with
      | nan => rfl
      | fin _ => rw [hc] at ht; cases ht
    refine ⟨gs, rfl, ?_⟩
    have hne : p.current_basal ≠ none := by intro h; simp [h] at hcb
    have h1 : stProfile inp = .ok p := by simp [stProfile, hp, hne]
    have herr : cgmErrorF11 (gluVals (.fin inp.clock.now) gs) = true := by
      unfold cgmErrorF11; rw [cgmStaleF11_undated hnan]; simp
    have h2 : stGlucoseF11 inp p = .error (cgmResultF11 inp p (gluVals (.fin inp.clock.now) gs)) := by
      simp [stGlucoseF11, hgs, herr]
    unfold determineBasalF11 dbPreludeF11
    simp [h1, h2, bind, Except.bind]

/-- **F-11, the fix works.** With an undated reading (the trigger) and a profile with
    `current_basal`, the fixed version gives no microbolus, and either replaces a running
    temp above the scheduled basal `round_basal(current_basal)` by that basal, or sets rate
    0, or issues no rate while the running temp is not above that basal. -/
theorem f11_fixed {inp : DBInputs} (ht : TriggerF11 inp) {p : Profile}
    (hp : inp.profile = some p) (hcb : p.current_basal.isSome) :
    let r := determineBasalF11 inp
    r.units = none ∧
    ((∃ ct, inp.currenttemp = some ct ∧ (ct.rate.js >ʲ profileCurrentBasal p) = true ∧
        r.rate = some (profileCurrentBasal p)) ∨
     r.rate = some 0 ∨
     (r.rate = none ∧ ∀ ct, inp.currenttemp = some ct → (ct.rate.js >ʲ profileCurrentBasal p) = false)) := by
  obtain ⟨gs, -, e⟩ := determineBasalF11_undated ht hp hcb
  simp only
  rw [e]
  unfold cgmResultF11
  cases hct : inp.currenttemp with
  | none => exact ⟨rfl, Or.inr (Or.inr ⟨rfl, by simp⟩)⟩
  | some ct =>
    simp only
    by_cases h1 : (ct.rate.js >ʲ profileCurrentBasal p) = true
    · rw [if_pos h1]; exact ⟨rfl, Or.inl ⟨ct, rfl, h1, rfl⟩⟩
    · rw [if_neg h1]
      split
      · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
      · refine ⟨rfl, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
        intro ct' hct'; cases hct'; simpa using h1

/-- On the F-11 input of `undated_glucose_max_rate` (BG 250 and rising, no date), oref0
    issues its maximum of 3.5 U/h; the trigger holds and the fixed version issues no rate
    (the running temp, rate 0, is not above the basal). -/
theorem f11_example :
    let base : DBInputs :=
      { glucose_status := some { glucose := some 250, delta := some 5, short_avgdelta := some 5, long_avgdelta := some 5 }
        currenttemp := some { duration := some 0, rate := some 0, temp := some "absolute" },
        iob_data := some (.single { iob := some 0, activity := some 0 }),
        profile := some reviewProfile, autosens_data := some { ratio := some 1 }, meal_data := some {},
        clock := { now := 1795003200000 } }
    TriggerF11 base ∧ (determineBasal base).rate = some 3.5 ∧ (determineBasalF11 base).rate = none ∧
      (determineBasalF11 base).units = none := by
  decide +kernel

end LeanAID.Fixed
