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

/-- If `keepRunning s dur ct` keeps the running temp, then `ct` is a temp whose duration
    exceeds `dur − 10`, and `dur > 0`. -/
theorem keepRunning_dur {s dur : JsNum} {ct : Option CurrentTemp} {v : JsNum × JsNum}
    (h : keepRunning s dur ct = some v) :
    ∃ c ctDur, ct = some c ∧ c.duration = some ctDur ∧ (ctDur >ʲ dur - 10) = true ∧ (dur >ʲ 0) = true := by
  unfold keepRunning at h
  split at h
  · rename_i ctDur ctRate temp
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact ⟨_, ctDur, rfl, rfl, hc.1.1.1.1, hc.2⟩
    · cases h
  · cases h

/-- Let `p` have `getMaxSafeBasal p = M` finite with `M ≥ 0`, and `current_basal = cb > 0`.
    Then `setTempBasal(0, D, p, rT, ct)` keeps the units of `rT`, and either sets rate 0 with
    duration `D`, or keeps the rate and duration of `rT`. In the second case `D > 0` and `ct`
    is a temp with more than `D − 10` minutes left and a finite rate `x` that is 0 if `x` is
    a double. -/
theorem setTempBasal_zero_dur {D : JsNum} {p : Profile} {rT : Result} {ct : Option CurrentTemp} {M cb : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) (hcb : p.current_basal = some (.fin cb)) (hcb0 : 0 < cb) :
    (setTempBasal 0 D p rT ct).units = rT.units ∧
    (((setTempBasal 0 D p rT ct).rate = some 0 ∧ (setTempBasal 0 D p rT ct).duration = some D) ∨
     ((setTempBasal 0 D p rT ct).rate = rT.rate ∧ (setTempBasal 0 D p rT ct).duration = rT.duration ∧
       ∃ c ctDur x, ct = some c ∧ c.duration = some ctDur ∧ (ctDur >ʲ D - 10) = true ∧ (D >ʲ 0) = true ∧
         c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) := by
  have hs := suggestedRate_zero hM hM0
  unfold suggestedRate at hs
  refine ⟨setTempBasal_units _ _ _ _ _, ?_⟩
  simp only [setTempBasal]
  rw [hs]
  cases hk : keepRunning (.fin 0) D ct with
  | some v =>
    right
    obtain ⟨c, x, hc, hcr, hx⟩ := keepRunning_zero hk
    obtain ⟨c', ctDur, hc', hd, h1, h2⟩ := keepRunning_dur hk
    rw [hc] at hc'; cases hc'
    exact ⟨rfl, rfl, c, ctDur, x, hc, hd, h1, h2, hcr, hx⟩
  | none =>
    simp only
    have : (JsNum.fin 0 =ʲ p.current_basal.js) = false := by
      rw [hcb]; simp; grind
    rw [this]; left; exact ⟨rfl, rfl⟩

/-- Let `p` have `getMaxSafeBasal p = M` finite with `M ≥ 0`, and `current_basal = cb > 0`.
    Then `setTempBasal(0, dur, p, rT, ct)` keeps the units of `rT`, and either sets rate 0 or
    keeps the rate of `rT` while `ct` is a temp with a finite rate `x` that is 0 if `x` is a
    double. -/
theorem setTempBasal_zero {dur : JsNum} {p : Profile} {rT : Result} {ct : Option CurrentTemp} {M cb : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) (hcb : p.current_basal = some (.fin cb)) (hcb0 : 0 < cb) :
    (setTempBasal 0 dur p rT ct).units = rT.units ∧
    ((setTempBasal 0 dur p rT ct).rate = some 0 ∨
     ((setTempBasal 0 dur p rT ct).rate = rT.rate ∧
       ∃ c x, ct = some c ∧ c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) := by
  obtain ⟨hu, hr⟩ := setTempBasal_zero_dur (D := dur) (rT := rT) (ct := ct) hM hM0 hcb hcb0
  refine ⟨hu, ?_⟩
  rcases hr with ⟨hr, -⟩ | ⟨hr, -, c, -, x, hc, -, -, -, hcr, hx⟩
  · exact Or.inl hr
  · exact Or.inr ⟨hr, c, x, hc, hcr, hx⟩

/-- Let `p` have `getMaxSafeBasal p = M` finite with `M ≥ 0`, and `current_basal = cb > 0`,
    and let `D` be NaN or a whole number of minutes in `[30, 120]`. Then
    `setTempBasal(0, D, p, rT, ct)` keeps the units of `rT`, and either sets rate 0 with
    duration `D`, or keeps the rate and duration of `rT` while `ct` is a temp with more than
    20 minutes left and a finite rate `x` that is 0 if `x` is a double. -/
theorem setTempBasal_zero_lgs {D : JsNum} (hD : D = .nan ∨ ∃ q : Int, D = .fin q ∧ 30 ≤ q ∧ q ≤ 120)
    {p : Profile} {rT : Result} {ct : Option CurrentTemp} {M cb : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) (hcb : p.current_basal = some (.fin cb)) (hcb0 : 0 < cb) :
    (setTempBasal 0 D p rT ct).units = rT.units ∧
    (((setTempBasal 0 D p rT ct).rate = some 0 ∧ (setTempBasal 0 D p rT ct).duration = some D) ∨
     ((setTempBasal 0 D p rT ct).rate = rT.rate ∧ (setTempBasal 0 D p rT ct).duration = rT.duration ∧
       ∃ c ctDur x, ct = some c ∧ c.duration = some (.fin ctDur) ∧ 20 < ctDur ∧
         c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) := by
  obtain ⟨hu, hr⟩ := setTempBasal_zero_dur (D := D) (rT := rT) (ct := ct) hM hM0 hcb hcb0
  refine ⟨hu, ?_⟩
  rcases hr with h | ⟨hr, hd, c, ctDur, x, hc, hcd, hgt, hpos, hcr, hx⟩
  · exact Or.inl h
  · right
    refine ⟨hr, hd, c, ?_⟩
    rcases hD with hD | ⟨q, hq, hq30, -⟩
    · subst hD; simp at hpos
    · subst hq
      cases ctDur with
      | nan => simp at hgt
      | fin cd =>
        refine ⟨cd, x, hc, hcd, ?_, hcr, hx⟩
        have e : (JsNum.fin (q : Rat) - 10 : JsNum) = .fin (Binary64.rd ((q : Rat) - 10)) := rfl
        rw [e, gt_fin, decide_eq_true_eq] at hgt
        have m := LeanAID.Binary64.rd_mono (show ((20 : Int) : Rat) ≤ (q : Rat) - 10 by
          have : (30 : Rat) ≤ (q : Rat) := by exact_mod_cast hq30
          push_cast; grind)
        rw [LeanAID.Binary64.rd_intCast (by decide)] at m
        push_cast at m
        grind

/-- The duration that the low-glucose branch requests (`determine-basal.js:914-918`). -/
def lgsDur (c : Ctx) : JsNum :=
  JsNum.min 120 (JsNum.max 30 (rnd (rnd (60 * ((c.target_bg - c.minGuardBG) / c.sens) / c.p.current_basal.js) / 30) * 30))

/-- For every `y`, `min(120, max(30, rnd(y)·30))` is NaN or a whole number in `[30, 120]`. -/
theorem clamp30_120_int (y : JsNum) :
    JsNum.min 120 (JsNum.max 30 (rnd y * 30)) = .nan ∨
    ∃ q : Int, JsNum.min 120 (JsNum.max 30 (rnd y * 30)) = .fin q ∧ 30 ≤ q ∧ q ≤ 120 := by
  cases y with
  | nan => left; rfl
  | fin y =>
    right
    obtain ⟨N, hN⟩ := rnd0_int y
    have hN' : rnd (.fin y) = .fin (Binary64.rd (N : Rat)) := hN
    rw [hN']
    have e : (JsNum.fin (Binary64.rd (N : Rat)) * 30 : JsNum) = .fin (Binary64.rd (Binary64.rd (N : Rat) * 30)) := rfl
    rw [e]
    generalize hv : Binary64.rd (Binary64.rd (N : Rat) * 30) = v
    simp only [JsNum.max, JsNum.min, show (120 : JsNum) = .fin 120 from rfl]
    by_cases h30 : (30 : Rat) ≤ v
    · by_cases h120 : (120 : Rat) ≤ v
      · exact ⟨120, by simp [h30, h120], by decide, by decide⟩
      · have hN1 : 1 ≤ N := by
          by_cases h1 : 1 ≤ N
          · exact h1
          · exfalso
            have h1 : N ≤ 0 := by omega
            have a : Binary64.rd (N : Rat) ≤ 0 := Binary64.rd_nonpos (by exact_mod_cast h1)
            have b : Binary64.rd (Binary64.rd (N : Rat) * 30) ≤ 0 := Binary64.rd_nonpos (by grind)
            grind
        have hN4 : N ≤ 4 := by
          by_cases h4 : N ≤ 4
          · exact h4
          · exfalso
            have a := LeanAID.Binary64.rd_mono (show ((5 : Int) : Rat) ≤ (N : Rat) by exact_mod_cast (show (5 : Int) ≤ N by omega))
            rw [LeanAID.Binary64.rd_intCast (by decide)] at a
            have b := LeanAID.Binary64.rd_mono (show ((150 : Int) : Rat) ≤ Binary64.rd (N : Rat) * 30 by push_cast; grind)
            rw [LeanAID.Binary64.rd_intCast (by decide)] at b
            push_cast at b
            grind
        have hsmall : N.natAbs ≤ 2 ^ 53 := Nat.le_trans (show N.natAbs ≤ 4 by omega) (by decide)
        have hrdN : Binary64.rd (N : Rat) = N := LeanAID.Binary64.rd_intCast hsmall
        have hv' : v = ((N * 30 : Int) : Rat) := by
          rw [← hv, hrdN, show (N : Rat) * 30 = ((N * 30 : Int) : Rat) by push_cast; rfl]
          exact LeanAID.Binary64.rd_intCast (Nat.le_trans (show (N * 30).natAbs ≤ 120 by omega) (by decide))
        refine ⟨N * 30, ?_, by omega, by omega⟩
        rw [hv'] at h30 h120 ⊢
        simp only [h30, h120, ↓reduceIte]
    · refine ⟨30, ?_, by decide, by decide⟩
      simp only [h30, ↓reduceIte, show ¬ (120 : Rat) ≤ 30 by decide]; rfl

theorem lgsDur_cases (c : Ctx) : lgsDur c = .nan ∨ ∃ q : Int, lgsDur c = .fin q ∧ 30 ≤ q ∧ q ≤ 120 :=
  clamp30_120_int _

/-- The low-glucose branch of the dose phase (`determine-basal.js:912-920`). Suppose the
    branch before it does not fire: not all of `bg < threshold`,
    `iob < −current_basal·20/60`, `minDelta > 0` and `minDelta > expectedDelta` hold. If BG or
    `minGuardBG` is below `threshold`, then `dbDose c = setTempBasal(0, lgsDur c, c.p, rT', c.ct)`
    for some `rT'` with the rate, units and duration of `c.rT`. -/
theorem dbDose_lgs_dur {c : Ctx}
    (hexc : (c.bg <ʲ c.threshold && c.iobd.iob.js <ʲ -c.p.current_basal.js * 20 / 60 &&
      c.minDelta >ʲ 0 && c.minDelta >ʲ c.expectedDelta) = false)
    (hlow : (c.bg <ʲ c.threshold || c.minGuardBG <ʲ c.threshold) = true) :
    ∃ rT', rT'.rate = c.rT.rate ∧ rT'.units = c.rT.units ∧ rT'.duration = c.rT.duration ∧
      dbDose c = setTempBasal 0 (lgsDur c) c.p rT' (some c.ct) := by
  unfold dbDose
  simp only
  simp only [hexc, hlow, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, ?_, ?_, ?_, rfl⟩ <;> rfl

/-- The low-glucose-suspend branch of the dose phase (lines 912-920). -/
theorem dbDose_lgs {c : Ctx}
    (hexc : (c.bg <ʲ c.threshold && c.iobd.iob.js <ʲ -c.p.current_basal.js * 20 / 60 &&
      c.minDelta >ʲ 0 && c.minDelta >ʲ c.expectedDelta) = false)
    (hlow : (c.bg <ʲ c.threshold || c.minGuardBG <ʲ c.threshold) = true) :
    ∃ dur rT', rT'.rate = c.rT.rate ∧ rT'.units = c.rT.units ∧ dbDose c = setTempBasal 0 dur c.p rT' (some c.ct) := by
  obtain ⟨rT', hr, hu, -, h⟩ := dbDose_lgs_dur hexc hlow
  exact ⟨_, rT', hr, hu, h⟩

/-- The condition of the first branch of oref0's dose phase (`determine-basal.js:908-911`):
    `bg < threshold`, `iob < −current_basal·20/60`, `minDelta > 0` and
    `minDelta > expectedDelta`. If it holds, oref0 does not enter the low-glucose branch. -/
def doseFirstBranch (pre : Pre) : Bool :=
  pre.bg <ʲ pre.threshold && pre.iobd.iob.js <ʲ -pre.p.current_basal.js * 20 / 60 &&
    pre.minDelta >ʲ 0 && pre.minDelta >ʲ pre.expectedDelta

/-- Let BG not be both below `threshold` and rising: `bg < threshold` is false or
    `minDelta > 0` is false. Then `doseFirstBranch pre = false`. -/
theorem doseFirstBranch_of_not_rising {pre : Pre}
    (h : (pre.bg <ʲ pre.threshold) = false ∨ (pre.minDelta >ʲ 0) = false) : doseFirstBranch pre = false := by
  unfold doseFirstBranch
  rcases h with h | h <;> simp only [h, Bool.false_and, Bool.and_false]

/-- Let `inp` be a valid input whose prelude succeeds with `pre`, with BG or the predicted
    `minGuardBG` below `threshold`, and `doseFirstBranch pre = false`. Then the profile of
    `dbPredict inp pre` has a finite `getMaxSafeBasal` `M ≥ 0` and `current_basal = cb > 0`,
    `inp.currenttemp` is the context's `ct`, the condition of the dose phase's first branch
    is false, and its low-glucose condition is true. -/
theorem lgs_setup {inp : DBInputs} (hv : ValidInput inp) {pre : Pre} (hpre : dbPrelude inp = .ok pre)
    (hlow : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true)
    (hfirst : doseFirstBranch pre = false) :
    ∃ M cb, getMaxSafeBasal (dbPredict inp pre).p = .fin M ∧ 0 ≤ M ∧
      (dbPredict inp pre).p.current_basal = some (.fin cb) ∧ 0 < cb ∧
      inp.currenttemp = some (dbPredict inp pre).ct ∧
      ((dbPredict inp pre).bg <ʲ (dbPredict inp pre).threshold &&
        (dbPredict inp pre).iobd.iob.js <ʲ -(dbPredict inp pre).p.current_basal.js * 20 / 60 &&
        (dbPredict inp pre).minDelta >ʲ 0 && (dbPredict inp pre).minDelta >ʲ (dbPredict inp pre).expectedDelta) = false ∧
      ((dbPredict inp pre).bg <ʲ (dbPredict inp pre).threshold ||
        (dbPredict inp pre).minGuardBG <ʲ (dbPredict inp pre).threshold) = true := by
  obtain ⟨p, g, mm, io, ct, meal, h1, -, -, -, h5, -, hpp, hct, -, -, -, -, -, -, -⟩ := prelude_ok hpre
  have hp := stProfile_ok h1
  have vp := hv.validProfile hp
  obtain ⟨cb, hcb, hcb0⟩ := vp.current_basal
  obtain ⟨cb'', M, hcb'', -, hM, -, hMpos⟩ := maxSafeBasal_exists vp
  have hpc : (dbPredict inp pre).p = p := hpp
  refine ⟨M, cb, by rw [hpc]; exact hM, Rat.le_of_lt hMpos, by rw [hpc]; exact hcb, hcb0, ?_, ?_, ?_⟩
  · rw [stPumpHistory_ok h5, ← hct]; rfl
  · exact hfirst
  · show (pre.bg <ʲ pre.threshold || (dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true
    rcases hlow with h | h <;> simp [h]

/-- **Low glucose suspend, with durations.** Let `inp` be a valid input whose prelude
    succeeds with `pre`, with BG or the predicted `minGuardBG` below `threshold`, and
    `doseFirstBranch pre = false`. Then oref0 issues no microbolus, and either
    - sets rate 0 with a duration that is NaN or a whole number of minutes in `[30, 120]`, or
    - issues no rate and no duration, while `currenttemp` has more than 20 minutes left and
      a finite rate that is 0 if it is a double. -/
theorem lgs_detail {inp : DBInputs} (hv : ValidInput inp) {pre : Pre} (hpre : dbPrelude inp = .ok pre)
    (hlow : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true)
    (hfirst : doseFirstBranch pre = false) :
    (determineBasal inp).units = none ∧
    (((determineBasal inp).rate = some 0 ∧ ∃ D, (determineBasal inp).duration = some D ∧
        (D = .nan ∨ ∃ q : Int, D = .fin q ∧ 30 ≤ q ∧ q ≤ 120)) ∨
     ((determineBasal inp).rate = none ∧ (determineBasal inp).duration = none ∧
       ∃ c ctDur x, inp.currenttemp = some c ∧ c.duration = some (.fin ctDur) ∧ 20 < ctDur ∧
         c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) := by
  obtain ⟨M, cb, hM, hM0, hcb, hcb0, hct, hexc, hlow'⟩ := lgs_setup hv hpre hlow hfirst
  unfold determineBasal
  rw [hpre]
  simp only
  obtain ⟨rT', hr', hu', hd', heq⟩ := dbDose_lgs_dur hexc hlow'
  rw [heq]
  have hDc := lgsDur_cases (dbPredict inp pre)
  obtain ⟨hu, hr⟩ := setTempBasal_zero_lgs hDc (rT := rT') (ct := some (dbPredict inp pre).ct) hM hM0 hcb hcb0
  refine ⟨by rw [hu, hu']; rfl, ?_⟩
  rcases hr with ⟨hr, hd⟩ | ⟨hr, hd, c, rest⟩
  · exact Or.inl ⟨hr, _, hd, hDc⟩
  · right
    refine ⟨by rw [hr, hr']; rfl, by rw [hd, hd']; rfl, c, ?_⟩
    obtain ⟨ctDur, x, hc, rest⟩ := rest
    exact ⟨ctDur, x, by rw [hct, hc], rest⟩

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
  obtain ⟨hu, h⟩ := lgs_detail hv hpre hlow (doseFirstBranch_of_not_rising hnotrising)
  refine ⟨hu, ?_⟩
  rcases h with ⟨hr, -⟩ | ⟨hr, -, c, -, x, hc, -, -, hcr, hx⟩
  · exact Or.inl hr
  · exact Or.inr ⟨hr, c, x, hc, hcr, hx⟩

end LeanAID.Proofs
