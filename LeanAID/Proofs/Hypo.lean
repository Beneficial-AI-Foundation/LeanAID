/-
  LeanAID.Proofs.Hypo — bad data (H5) and low glucose suspend (H3).
-/
import LeanAID.Proofs.Safety

namespace LeanAID.Proofs

open JsNum

/-! ### H5: unreliable or missing data -/

/-- When the CGM data is unusable, `determine_basal` returns the CGM-error result. -/
theorem determineBasal_cgmError {inp : DBInputs} {p : Profile} {gs : GlucoseStatus}
    (hp : inp.profile = some p) (hcb : p.current_basal.isSome) (hgs : inp.glucose_status = some gs)
    (herr : cgmError (gluVals (.fin inp.clock.now) gs) = true) :
    determineBasal inp = cgmResult inp p (gluVals (.fin inp.clock.now) gs) := by
  have hne : p.current_basal ≠ none := by intro h; simp [h] at hcb
  have h1 : stProfile inp = .ok p := by simp [stProfile, hp, hne]
  have h2 : stGlucose inp p = .error (cgmResult inp p (gluVals (.fin inp.clock.now) gs)) := by
    simp [stGlucose, hgs, herr]
  unfold determineBasal dbPrelude
  simp [h1, h2, bind, Except.bind]

/-- **H5a (R12).** If the glucose reading is an error code (≤ 10 or 38), noisy
    (noise ≥ 3), stale or from the future, or flat, then oref0 never issues a
    microbolus and never increases insulin: it replaces a running temp *above*
    the scheduled basal by the scheduled basal, or sets/keeps a zero temp, or
    issues nothing while the running temp is not above the scheduled basal. -/
theorem cgmError_no_increase {inp : DBInputs} {p : Profile} {gs : GlucoseStatus}
    (hp : inp.profile = some p) (hcb : p.current_basal.isSome) (hgs : inp.glucose_status = some gs)
    (herr : cgmError (gluVals (.fin inp.clock.now) gs) = true) :
    let r := determineBasal inp
    r.units = none ∧
    ((∃ ct, inp.currenttemp = some ct ∧ (ct.rate.js >ʲ profileCurrentBasal p) = true ∧
        r.rate = some (profileCurrentBasal p)) ∨
     r.rate = some 0 ∨
     (r.rate = none ∧ ∀ ct, inp.currenttemp = some ct → (ct.rate.js >ʲ profileCurrentBasal p) = false)) := by
  simp only
  rw [determineBasal_cgmError hp hcb hgs herr]
  unfold cgmResult
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

/-- **H5b (R13).** A missing profile or `current_basal` gives an error and no command. -/
theorem missing_current_basal {inp : DBInputs}
    (h : inp.profile = none ∨ ∃ p, inp.profile = some p ∧ p.current_basal = none) :
    (determineBasal inp).error = some "Error: could not get current basal rate" ∧
    (determineBasal inp).rate = none ∧ (determineBasal inp).units = none := by
  have : stProfile inp = .error (Result.err "Error: could not get current basal rate") := by
    rcases h with h | ⟨p, hp, hc⟩ <;> simp [stProfile, *]
  unfold determineBasal dbPrelude
  simp [this, bind, Except.bind, Result.err]

/-- **H5b (R13).** With usable CGM data, a missing `min_bg` or `max_bg` gives an
    error and no command. -/
theorem missing_targets {inp : DBInputs} {p : Profile} {g : GluVals}
    (hp : stProfile inp = .ok p) (hg : stGlucose inp p = .ok g) (h : p.min_bg = none ∨ p.max_bg = none) :
    (determineBasal inp).error = some "Error: could not determine target_bg. " ∧
    (determineBasal inp).rate = none ∧ (determineBasal inp).units = none := by
  have : stTargets p = .error (Result.err "Error: could not determine target_bg. ") := by
    unfold stTargets; rcases h with h | h <;> rw [h] <;> simp
  unfold determineBasal dbPrelude
  simp [hp, hg, this, bind, Except.bind, Result.err]

/-- **H5b (R13).** With usable CGM data and targets, missing IOB data gives an
    error and no command. -/
theorem missing_iob {inp : DBInputs} {p : Profile} {g : GluVals} {mm : JsNum × JsNum}
    (hp : stProfile inp = .ok p) (hg : stGlucose inp p = .ok g) (ht : stTargets p = .ok mm)
    (h : inp.iob_data = none) :
    (determineBasal inp).error = some "Error: iob_data undefined. " ∧
    (determineBasal inp).rate = none ∧ (determineBasal inp).units = none := by
  have : stIob inp = .error (Result.err "Error: iob_data undefined. ") := by simp [stIob, h]
  unfold determineBasal dbPrelude
  simp [hp, hg, ht, this, bind, Except.bind, Result.err]

/-! ### H3: low glucose suspend -/

theorem suggestedRate_zero {p : Profile} {M : Rat} (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) :
    suggestedRate 0 p = .fin 0 := by
  unfold suggestedRate; rw [hM]
  have : clampRate (0 : JsNum) (.fin M) = .fin 0 := by
    show clampRate (.fin 0) (.fin M) = .fin 0
    simp [clampRate]; grind
  rw [this, roundBasal_fin, rbR_zero]

/-- A running temp is "close enough" to a zero request only if its rate is zero,
    when that rate is a double (as every number read from JSON is): in double
    arithmetic `0 ≤ rate · 1.2` and `rate · 0.8 ≤ 0` hold exactly for the rates
    strictly between `-2^-1074` and `2^-1074`, and the only such double is 0. -/
theorem keepRunning_zero {dur : JsNum} {ct : Option CurrentTemp} {d r : JsNum}
    (h : keepRunning (.fin 0) dur ct = some (d, r)) :
    ∃ c x, ct = some c ∧ c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0) := by
  unfold keepRunning at h
  split at h
  · rename_i ctDur ctRate temp
    split at h
    · rename_i hc
      injection h with h; injection h with h1 h2; subst h2
      cases ctRate with
      | nan => simp at hc
      | fin x =>
        refine ⟨_, x, rfl, rfl, ?_⟩
        intro hdx
        simp only [Bool.and_eq_true, JsNum.ofSci_eq, JsNum.fin_mul, JsNum.le_fin, JsNum.ge_fin,
          decide_eq_true_eq] at hc
        obtain ⟨⟨⟨-, ha⟩, hb⟩, -⟩ := hc
        have e1 : (OfScientific.ofScientific 12 true 1 : Rat) = 6/5 := by decide +kernel
        have e2 : (OfScientific.ofScientific 8 true 1 : Rat) = 4/5 := by decide +kernel
        rw [e1] at ha; rw [e2] at hb
        have c1 : (1/2 : Rat) < Binary64.rd (4/5) := by decide +kernel
        have c2 : (1/2 : Rat) < Binary64.rd (6/5) := by decide +kernel
        have pp := Binary64.pow2_pos (-1075)
        have p2 : Binary64.pow2 (-1074) = Binary64.pow2 (-1075) * 2 := by
          rw [← Binary64.pow2_succ]; rfl
        apply Binary64.double_small hdx
        · -- x > -2^-1074, else rate · 1.2 rounds below 0
          by_cases hx : -Binary64.pow2 (-1074) < x
          · exact hx
          · exfalso
            have m := Rat.mul_le_mul_of_nonneg_right (show x ≤ -Binary64.pow2 (-1074) by grind)
              (Rat.le_of_lt (show (0 : Rat) < Binary64.rd (6/5) by grind))
            have m2 := Rat.mul_lt_mul_of_pos_left c2 (show 0 < Binary64.pow2 (-1074) by grind)
            have := Binary64.rd_pos_of_gt (y := -(x * Binary64.rd (6/5))) (by grind)
            rw [Binary64.rd_neg] at this; grind
        · by_cases hx : x < Binary64.pow2 (-1074)
          · exact hx
          · exfalso
            have m := Rat.mul_le_mul_of_nonneg_right (show Binary64.pow2 (-1074) ≤ x by grind)
              (Rat.le_of_lt (show (0 : Rat) < Binary64.rd (4/5) by grind))
            have m2 := Rat.mul_lt_mul_of_pos_left c1 (show 0 < Binary64.pow2 (-1074) by grind)
            have := Binary64.rd_pos_of_gt (y := x * Binary64.rd (4/5)) (by grind)
            grind
    · cases h
  · cases h

/-- `setTempBasal(0, ...)` sets a zero temp, or leaves a running zero temp alone
    (for a positive `current_basal`). -/
theorem setTempBasal_zero {dur : JsNum} {p : Profile} {rT : Result} {ct : Option CurrentTemp} {M cb : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) (hcb : p.current_basal = some (.fin cb)) (hcb0 : 0 < cb) :
    (setTempBasal 0 dur p rT ct).units = rT.units ∧
    ((setTempBasal 0 dur p rT ct).rate = some 0 ∨
     ((setTempBasal 0 dur p rT ct).rate = rT.rate ∧
       ∃ c x, ct = some c ∧ c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) := by
  have hs := suggestedRate_zero hM hM0
  unfold suggestedRate at hs
  refine ⟨setTempBasal_units _ _ _ _ _, ?_⟩
  simp only [setTempBasal]
  rw [hs]
  cases hk : keepRunning (.fin 0) dur ct with
  | some v => right; exact ⟨rfl, keepRunning_zero hk⟩
  | none =>
    simp only
    have : (JsNum.fin 0 =ʲ p.current_basal.js) = false := by
      rw [hcb]; simp; grind
    rw [this]; left; rfl

/-- The low-glucose-suspend branch of the dose phase (lines 912-920). -/
theorem dbDose_lgs {c : Ctx}
    (hexc : (c.bg <ʲ c.threshold && c.iobd.iob.js <ʲ -c.p.current_basal.js * 20 / 60 &&
      c.minDelta >ʲ 0 && c.minDelta >ʲ c.expectedDelta) = false)
    (hlow : (c.bg <ʲ c.threshold || c.minGuardBG <ʲ c.threshold) = true) :
    ∃ dur rT', rT'.rate = c.rT.rate ∧ rT'.units = c.rT.units ∧ dbDose c = setTempBasal 0 dur c.p rT' (some c.ct) := by
  unfold dbDose
  simp only
  rw [if_neg (by rw [hexc]; decide), if_pos hlow]
  refine ⟨_, _, ?_, ?_, rfl⟩ <;> rfl

/-- **H3 (R8, R9): low glucose suspend.** For valid input, once the prelude has
    succeeded (fresh, non-error CGM data, targets and IOB present): if BG or the
    predicted `minGuardBG` is below oref0's `threshold`, and BG is not both below
    `threshold` and rising (`minDelta > 0`), then oref0 issues no microbolus and
    either sets a zero temp or leaves a running zero temp in place (more precisely:
    a running temp whose rate is 0 if it is a double, as every rate read from JSON
    is; see `keepRunning_zero`). -/
theorem low_glucose_suspend {inp : DBInputs} (hv : ValidInput inp) {pre : Pre} (hpre : dbPrelude inp = .ok pre)
    (hlow : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true)
    (hnotrising : (pre.bg <ʲ pre.threshold) = false ∨ (pre.minDelta >ʲ 0) = false) :
    (determineBasal inp).units = none ∧
    ((determineBasal inp).rate = some 0 ∨
     ((determineBasal inp).rate = none ∧
       ∃ c x, inp.currenttemp = some c ∧ c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) := by
  obtain ⟨p, g, mm, io, ct, meal, h1, -, -, -, h5, -, hpp, hct, -, -, -, -, -, -, -⟩ := prelude_ok hpre
  have hp := stProfile_ok h1
  have vp := hv.validProfile hp
  obtain ⟨cb, hcb, hcb0⟩ := vp.current_basal
  obtain ⟨cb'', M, hcb'', -, hM, -, hMpos⟩ := maxSafeBasal_exists vp
  have hct' : inp.currenttemp = some ct := stPumpHistory_ok h5
  unfold determineBasal
  rw [hpre]
  simp only
  have hexc : ((dbPredict inp pre).bg <ʲ (dbPredict inp pre).threshold &&
      (dbPredict inp pre).iobd.iob.js <ʲ -(dbPredict inp pre).p.current_basal.js * 20 / 60 &&
      (dbPredict inp pre).minDelta >ʲ 0 && (dbPredict inp pre).minDelta >ʲ (dbPredict inp pre).expectedDelta) = false := by
    show (pre.bg <ʲ pre.threshold && pre.iobd.iob.js <ʲ -pre.p.current_basal.js * 20 / 60 &&
      pre.minDelta >ʲ 0 && pre.minDelta >ʲ pre.expectedDelta) = false
    rcases hnotrising with h | h <;> simp only [h, Bool.false_and, Bool.and_false]
  have hlow' : ((dbPredict inp pre).bg <ʲ (dbPredict inp pre).threshold ||
      (dbPredict inp pre).minGuardBG <ʲ (dbPredict inp pre).threshold) = true := by
    show (pre.bg <ʲ pre.threshold || (dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true
    rcases hlow with h | h <;> simp [h]
  obtain ⟨dur, rT', hr', hu', heq⟩ := dbDose_lgs hexc hlow'
  rw [heq]
  have hpc : (dbPredict inp pre).p = p := hpp
  rw [hpc]
  obtain ⟨hu, hr⟩ := setTempBasal_zero (dur := dur) (rT := rT') (ct := some (dbPredict inp pre).ct) hM
    (Rat.le_of_lt hMpos) hcb hcb0
  refine ⟨by rw [hu, hu']; rfl, ?_⟩
  rcases hr with hr | ⟨hr, c, x, hc, hcr⟩
  · left; exact hr
  · right; refine ⟨by rw [hr, hr']; rfl, c, x, ?_, hcr⟩
    injection hc with hc; rw [hct', ← hc, ← hct]; rfl

end LeanAID.Proofs
