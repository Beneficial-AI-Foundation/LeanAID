import LeanAID.Fixed.Proofs.Combined
import LeanAID.Fixed.Proofs.MaxBasalLgs
import LeanAID.Proofs.RateDouble

/-!
# The safety rules for the corrected version, without the exceptions

The headline theorems of `LeanAID/Proofs` (`scripts/headline.txt`), restated for
`determineBasalFixed`. Each states its exception of today as removed, or says why it keeps a
hypothesis. Table in `docs/FIXED.md`.

| oref0 (`LeanAID.Proofs`) | corrected (`LeanAID.Fixed`) |
|---|---|
| `rate_le_roundBasal_maxSafeBasal`: rate ≤ `round_basal(maxSafeBasal)` | `rate_le_maxSafeBasal_fixed`: rate ≤ `maxSafeBasal`, under `ValidInputFixed` |
| `cgm_unreliable_no_increase`: dated readings only | `cgm_unreliable_no_increase_fixed`: also undated readings |
| `missing_max_basal_no_clamp`: 5.9 U/h without `max_basal` | `missing_max_basal_fixed`: no rate above `current_basal`, no microbolus |
| `low_glucose_suspend`: duration may be NaN, needs `max_basal` | `low_glucose_suspend_fixed`: duration in [30, 120], `validate` accepts, under `ValidInputFixed` (also without `max_basal`) |
| `microbolus_limits` | `microbolus_limits_fixed`, under `ValidInputFixed` |
| `iob_at_max` | `iob_at_max_fixed` |
| `cgmError_no_increase` | `cgmError_no_increase_fixed` |
| `missing_current_basal`, `missing_targets`, `missing_iob` | `…_fixed` |
| `rate_double` | `rate_double_fixed` |
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Proofs LeanAID.Time JsNum
open LeanAID.Binary64 (rd)

/-! ### The shape of the result before the F-04 step -/

theorem cgmResultF11_shape (inp : DBInputs) (p : Profile) (g : GluVals) :
    (cgmResultF11 inp p g).units = none ∧
    ((cgmResultF11 inp p g).rate = none ∨ (cgmResultF11 inp p g).rate = some 0 ∨
      (cgmResultF11 inp p g).rate = some (profileCurrentBasal p)) := by
  unfold cgmResultF11
  split
  · exact ⟨rfl, Or.inl rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, Or.inr (Or.inr rfl)⟩
    · split
      · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨rfl, Or.inl rfl⟩

/-- `maxSafeOk` holds for a valid profile. -/
theorem maxSafeOk_of_valid {p : Profile} (vp : ValidProfile p) : maxSafeOk p = true := by
  obtain ⟨-, M, -, -, hM, -, hMpos⟩ := maxSafeBasal_exists vp
  simp [maxSafeOk, hM, hMpos]

/-- `maxSafeOk` gives a positive numeric `maxSafeBasal`. -/
theorem maxSafe_of_ok {p : Profile} (h : maxSafeOk p = true) : ∃ M, getMaxSafeBasal p = .fin M ∧ 0 < M := by
  unfold maxSafeOk at h
  cases hM : getMaxSafeBasal p with
  | nan => rw [hM] at h; cases h
  | fin M => rw [hM] at h; simp at h; exact ⟨M, rfl, h⟩

theorem uncapped_ok {inp : DBInputs} {p : Profile} {pre : Pre} (hs : stProfile inp = .ok p)
    (hpre : dbPreludeF11 inp = .ok pre) : determineBasalUncapped inp = dbDosePatched (dbPredict inp pre) := by
  rw [uncapped_of_st hs, hpre]

theorem determineBasal_ok {inp : DBInputs} {pre : Pre} (hpre : dbPrelude inp = .ok pre) :
    determineBasal inp = dbDose (dbPredict inp pre) := by
  unfold determineBasal; rw [hpre]

theorem determineBasalPatched_ok {inp : DBInputs} {pre : Pre} (hpre : dbPrelude inp = .ok pre) :
    determineBasalPatched inp = dbDosePatched (dbPredict inp pre) := by
  unfold determineBasalPatched; rw [hpre]

/-- With valid input, the result before the F-04 step is oref0's, or a result without a
    microbolus whose rate is none, 0 or `round_basal(current_basal)`. -/
theorem uncapped_valid_cases {inp : DBInputs} (hv : ValidInput inp) :
    determineBasalUncapped inp = determineBasal inp ∨
    ((determineBasalUncapped inp).units = none ∧
      ((determineBasalUncapped inp).rate = none ∨ (determineBasalUncapped inp).rate = some 0 ∨
        ∃ p, inp.profile = some p ∧ (determineBasalUncapped inp).rate = some (profileCurrentBasal p))) := by
  cases hs : stProfile inp with
  | error r =>
    left; unfold determineBasalUncapped; rw [hs]
    exact (determineBasal_of_stProfile_error hs).symm
  | ok p =>
    have hp := stProfile_ok hs
    cases hpre : dbPreludeF11 inp with
    | error r =>
      have e : determineBasalUncapped inp = r := by rw [uncapped_of_st hs, hpre]
      rw [e]
      rcases dbPreludeF11_error hpre with h | ⟨p', gs, hp', hgs, hr⟩
      · left; unfold determineBasal; rw [h]
      · right; subst hr
        rw [hp] at hp'; cases hp'
        obtain ⟨hu, hrate⟩ := cgmResultF11_shape inp p (gluVals (.fin inp.clock.now) gs)
        rcases hrate with h | h | h
        · exact ⟨hu, Or.inl h⟩
        · exact ⟨hu, Or.inr (Or.inl h)⟩
        · exact ⟨hu, Or.inr (Or.inr ⟨p, hp, h⟩)⟩
    | ok pre =>
      have hpre' := dbPreludeF11_ok hpre
      rw [uncapped_ok hs hpre]
      rcases dbDosePatched_cases (dbPredict inp pre) with h | ⟨h1, h2⟩
      · left; rw [h, determineBasal_ok hpre']
      · right
        have hlow : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true := by
          have : (pre.bg <ʲ pre.threshold || (dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true := h2
          simpa [Bool.or_eq_true] using this
        have hfirst : doseFirstBranch pre = false := h1
        obtain ⟨hu, hr⟩ := lgs_patched hv hpre' hlow hfirst
        rw [determineBasalPatched_ok hpre'] at hu hr
        rcases hr with ⟨hr, -⟩ | ⟨hr, -⟩
        · exact ⟨hu, Or.inr (Or.inl hr)⟩
        · exact ⟨hu, Or.inl hr⟩

/-! ### R1, R2: the rate ceiling without the rounding allowance -/

/-- **R1, R2 for the corrected version.** For valid input, where `max_basal` and
    `max_daily_basal` may be missing (`ValidInputFixed`), every finite rate the corrected
    version issues is between 0 and `maxSafeBasal` itself: no rounding allowance, no grid
    condition. (With `max_basal` or `max_daily_basal` missing, `maxSafeBasal` is NaN and
    `missing_max_basal_fixed` applies.) Compare `rate_le_roundBasal_maxSafeBasal`. -/
theorem rate_le_maxSafeBasal_fixed {inp : DBInputs} (hv : ValidInputFixed inp) {p : Profile}
    (hp : inp.profile = some p) {M r : Rat} (hM : getMaxSafeBasal p = .fin M)
    (hr : (determineBasalFixed inp).rate = some (.fin r)) : 0 ≤ r ∧ r ≤ M := by
  have hv' := validInput_of_fixed hv hp hM
  have vp := hv'.validProfile hp
  obtain ⟨cb, hcb, hcb0⟩ := vp.current_basal
  obtain ⟨-, hMpos⟩ := maxSafeBasal_ge vp hM hcb
  obtain ⟨hd, h30⟩ := maxSafeBasal_double vp hM
  rw [fixed_of_ok hp (maxSafeOk_of_valid vp)] at hr
  rcases capRate_rate hM hd (Rat.le_of_lt hMpos) h30 hr with ⟨hU, hle⟩ | ⟨h0, hle, -⟩
  · refine ⟨?_, hle⟩
    rcases uncapped_valid_cases hv' with e | ⟨-, hrate⟩
    · rw [e] at hU; exact (rate_le_roundBasal_maxSafeBasal hv' hp hM hU).1
    · rcases hrate with h | h | ⟨p', hp', h⟩
      · rw [h] at hU; cases hU
      · rw [h] at hU; cases hU; exact Rat.le_refl
      · rw [hp] at hp'; cases hp'
        rw [h] at hU
        simp [profileCurrentBasal, hcb, roundBasal_fin] at hU
        rw [← hU]; exact rbR_nonneg _ (Rat.le_of_lt hcb0)
  · exact ⟨h0, hle⟩

/-! ### R12: unreliable CGM data, now also undated -/

/-- The profile whose `maxSafeBasal` the corrected version uses: `p`, or, when `maxSafeBasal`
    is not a positive number (the F-12 trigger), the profile capped at `current_basal`. -/
def capOf (p : Profile) : Profile := if maxSafeOk p then p else capProfile p

/-- The CGM-error result after the F-04 step, for any profile `q`. -/
theorem cgm_capped (inp : DBInputs) (q : Profile) (g : GluVals) :
    (capRate q (cgmResultF11 inp q g)).units = none ∧
    ((∃ ct, inp.currenttemp = some ct ∧ (ct.rate.js >ʲ profileCurrentBasal q) = true ∧
        ((capRate q (cgmResultF11 inp q g)).rate = some (profileCurrentBasal q) ∨
         ((profileCurrentBasal q >ʲ getMaxSafeBasal q) = true ∧
           (capRate q (cgmResultF11 inp q g)).rate = some (roundBasalDown (getMaxSafeBasal q) q.model)))) ∨
     (capRate q (cgmResultF11 inp q g)).rate = some 0 ∨
     ((capRate q (cgmResultF11 inp q g)).rate = none ∧
       ∀ ct, inp.currenttemp = some ct → (ct.rate.js >ʲ profileCurrentBasal q) = false)) := by
  rw [capRate_units, capRate_rate_eq]
  unfold cgmResultF11
  cases hct : inp.currenttemp with
  | none => exact ⟨rfl, Or.inr (Or.inr ⟨rfl, fun ct h => by cases h⟩)⟩
  | some ct =>
    dsimp only
    by_cases h1 : (ct.rate.js >ʲ profileCurrentBasal q) = true
    · simp only [h1, ite_true]
      refine ⟨rfl, Or.inl ⟨ct, rfl, h1, ?_⟩⟩
      by_cases h3 : (profileCurrentBasal q >ʲ getMaxSafeBasal q && getMaxSafeBasal q ≥ʲ 0) = true
      · rw [if_pos h3]
        right; simp only [Bool.and_eq_true] at h3; exact ⟨h3.1, rfl⟩
      · rw [if_neg h3]; left; rfl
    · simp only [h1, Bool.false_eq_true, ite_false]
      split
      · refine ⟨rfl, Or.inr (Or.inl ?_)⟩
        have : ((0 : JsNum) >ʲ getMaxSafeBasal q && getMaxSafeBasal q ≥ʲ 0) = false := by
          cases getMaxSafeBasal q with
          | nan => rfl
          | fin m =>
            show (decide (m < 0) && decide (0 ≤ m)) = false
            by_cases hm : m < 0
            · have : ¬ (0 ≤ m) := by grind
              simp [hm, this]
            · simp [hm]
        dsimp only
        simp only [this, Bool.false_eq_true, ite_false]
      · refine ⟨rfl, Or.inr (Or.inr ⟨rfl, fun ct' hct' => ?_⟩)⟩
        cases hct'; simpa using h1

/-- **R12 for the corrected version.** If the corrected CGM check fires (an error code,
    noise, flat data, or a reading that is not known to be fresh, **including an undated
    one**), the corrected version gives no microbolus and never increases insulin: it
    replaces a running temp above the scheduled basal `round_basal(current_basal)` by that
    basal (or, if that basal is above the `maxSafeBasal` in use, `M = getMaxSafeBasal (capOf p)`,
    by `round_basal.down(M)`), or sets rate 0, or issues nothing while the running temp is
    not above `current_basal` or not above its rounding. Compare `cgmError_no_increase`.
    (With `maxSafeBasal` a positive number, `capOf p = p`.) -/
theorem cgmError_no_increase_fixed {inp : DBInputs} {p : Profile} {gs : GlucoseStatus}
    (hp : inp.profile = some p) (hcb : p.current_basal.isSome) (hgs : inp.glucose_status = some gs)
    (herr : cgmErrorF11 (gluVals (.fin inp.clock.now) gs) = true) :
    let r := determineBasalFixed inp
    r.units = none ∧
    ((∃ ct, inp.currenttemp = some ct ∧ (ct.rate.js >ʲ profileCurrentBasal p) = true ∧
        (r.rate = some (profileCurrentBasal p) ∨
         ((profileCurrentBasal p >ʲ getMaxSafeBasal (capOf p)) = true ∧
           r.rate = some (roundBasalDown (getMaxSafeBasal (capOf p)) p.model)))) ∨
     r.rate = some 0 ∨
     (r.rate = none ∧ ∀ ct, inp.currenttemp = some ct →
        (ct.rate.js >ʲ profileCurrentBasal p) = false ∨ (ct.rate.js >ʲ p.current_basal.js) = false)) := by
  have hne : p.current_basal ≠ none := by intro h; simp [h] at hcb
  have hs : stProfile inp = .ok p := by simp [stProfile, hp, hne]
  simp only
  cases hok : maxSafeOk p with
  | true =>
    have hcap : capOf p = p := by simp [capOf, hok]
    rw [hcap, fixed_of_ok hp hok]
    have h2 : stGlucoseF11 inp p = .error (cgmResultF11 inp p (gluVals (.fin inp.clock.now) gs)) := by
      simp [stGlucoseF11, hgs, herr]
    have hpre : dbPreludeF11 inp = .error (cgmResultF11 inp p (gluVals (.fin inp.clock.now) gs)) := by
      unfold dbPreludeF11; simp [hs, h2, bind, Except.bind]
    rw [uncapped_of_st hs, hpre]
    simp only
    obtain ⟨hu, h⟩ := cgm_capped inp p (gluVals (.fin inp.clock.now) gs)
    refine ⟨hu, ?_⟩
    rcases h with h | h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, fun ct hct => Or.inl (h' ct hct)⟩)
  | false =>
    have ht : TriggerF12 inp := by simp [TriggerF12, triggerF12, hp, hcb, hok]
    obtain ⟨p', hp', -, -, e⟩ := fixed_of_trigger ht
    rw [hp] at hp'; cases hp'
    have hcap : capOf p = capProfile p := by simp [capOf, hok]
    rw [hcap, e]
    have hs' := stProfile_inputF12 (inp := inp) hcb
    have h2 : stGlucoseF11 (inputF12 inp p) (capProfile p) =
        .error (cgmResultF11 (inputF12 inp p) (capProfile p) (gluVals (.fin inp.clock.now) gs)) := by
      simp [stGlucoseF11, inputF12, hgs, herr]
    have hpre : dbPreludeF11 (inputF12 inp p) =
        .error (cgmResultF11 (inputF12 inp p) (capProfile p) (gluVals (.fin inp.clock.now) gs)) := by
      unfold dbPreludeF11; simp [hs', h2, bind, Except.bind]
    rw [uncapped_of_st hs', hpre]
    simp only
    obtain ⟨hu, h⟩ := cgm_capped (inputF12 inp p) (capProfile p) (gluVals (.fin inp.clock.now) gs)
    have hpcb : profileCurrentBasal (capProfile p) = profileCurrentBasal p := rfl
    have hct : (inputF12 inp p).currenttemp = inp.currenttemp := rfl
    have hmodel : (capProfile p).model = p.model := rfl
    rw [hpcb, hct, hmodel] at h
    generalize capRate (capProfile p) (cgmResultF11 (inputF12 inp p) (capProfile p) (gluVals (.fin inp.clock.now) gs)) = U at h hu
    refine ⟨by rw [postF12_units]; exact hu, ?_⟩
    rcases h with ⟨ct, hct', h1, h3⟩ | h | ⟨h, h'⟩
    · rcases h3 with h3 | ⟨h4, h3⟩
      · exact Or.inl ⟨ct, hct', h1, Or.inl (postF12_some h3).1⟩
      · exact Or.inl ⟨ct, hct', h1, Or.inr ⟨h4, (postF12_some h3).1⟩⟩
    · exact Or.inr (Or.inl (postF12_some h).1)
    · rcases postF12_rate inp p U with ⟨hr, -⟩ | ⟨-, hr, -⟩
      · rw [hr]; exact Or.inr (Or.inr ⟨h, fun ct hct => Or.inl (h' ct hct)⟩)
      · rw [hr]; exact Or.inr (Or.inl rfl)

theorem cgmStaleF11_of_stale {g : GluVals} (h : cgmStale g = true) : cgmStaleF11 g = true := by
  cases ha : g.minAgo with
  | nan => unfold cgmStale at h; rw [ha] at h; simp [JsNum.gt, JsNum.lt] at h
  | fin a => rw [cgmStaleF11_of_fin ha]; exact h

/-- **R12 for the corrected version, with independent hypotheses.** As
    `cgm_unreliable_no_increase`, and **also for a reading with no `date`** (or one that is
    not a number): the corrected version gives no microbolus and never increases insulin. -/
theorem cgm_unreliable_no_increase_fixed {inp : DBInputs} {p : Profile} {gs : GlucoseStatus}
    (hp : inp.profile = some p) (hcb : p.current_basal.isSome) (hgs : inp.glucose_status = some gs)
    (hbad : (∃ b : Rat, gs.glucose = some (.fin b) ∧ (b ≤ 10 ∨ b = 38)) ∨
            (∃ n : Rat, gs.noise = some (.fin n) ∧ 3 ≤ n) ∨
            (∃ d : Int, gs.date = some (.fin (d : Rat)) ∧
              ((inp.clock.now - d : Rat) / 60000 ≥ 12 + 1/20 ∨ (inp.clock.now - d : Rat) / 60000 < -5 - 1/20)) ∨
            DateFmt.timeClip gs.date.js = .nan ∨
            cgmFlat (gluVals (.fin inp.clock.now) gs) = true) :
    let r := determineBasalFixed inp
    r.units = none ∧
    ((∃ ct, inp.currenttemp = some ct ∧ (ct.rate.js >ʲ profileCurrentBasal p) = true ∧
        (r.rate = some (profileCurrentBasal p) ∨
         ((profileCurrentBasal p >ʲ getMaxSafeBasal (capOf p)) = true ∧
           r.rate = some (roundBasalDown (getMaxSafeBasal (capOf p)) p.model)))) ∨
     r.rate = some 0 ∨
     (r.rate = none ∧ ∀ ct, inp.currenttemp = some ct →
        (ct.rate.js >ʲ profileCurrentBasal p) = false ∨ (ct.rate.js >ʲ p.current_basal.js) = false)) := by
  apply cgmError_no_increase_fixed hp hcb hgs
  unfold cgmErrorF11
  rcases hbad with ⟨b, hb, h⟩ | ⟨n, hn, h⟩ | ⟨d, hd, h⟩ | h | h
  · have : cgmBad (gluVals (.fin inp.clock.now) gs) = true := by
      unfold cgmBad gluVals; simp only [hb, Option.js_some, show (10 : JsNum) = .fin 10 from rfl, show (38 : JsNum) = .fin 38 from rfl, show (3 : JsNum) = .fin 3 from rfl, JsNum.le_fin, JsNum.seq_fin, decide_eq_true_eq, Bool.or_eq_true]
      rcases h with h | h
      · left; left; exact h
      · left; right; exact h
    simp [this]
  · have : cgmBad (gluVals (.fin inp.clock.now) gs) = true := by
      unfold cgmBad gluVals; simp only [hn, Option.js_some, show (10 : JsNum) = .fin 10 from rfl, show (38 : JsNum) = .fin 38 from rfl, show (3 : JsNum) = .fin 3 from rfl, JsNum.ge_fin, decide_eq_true_eq, Bool.or_eq_true]
      right; exact h
    simp [this]
  · have : cgmStale (gluVals (.fin inp.clock.now) gs) = true := by
      apply stale_of_clip (n := d) (by simp [hd, Option.js_some, timeClip_int])
      have hz : (inp.clock.now - d : Rat) = ((inp.clock.now - d : Int) : Rat) := by push_cast; rfl
      rwa [hz] at h
    rw [cgmStaleF11_of_stale this]; simp
  · rw [cgmStaleF11_undated h]; simp
  · simp [h]

/-! ### R13, R14: missing data -/

/-- **R14 for the corrected version (F-12).** With `max_basal` or `max_daily_basal` missing or
    not a number, and `current_basal` a double `cb` in `[0, 2^30]`, the corrected version
    issues no microbolus and no finite rate above `cb`. Compare `missing_max_basal_no_clamp`
    (oref0: 5.9 U/h for a scheduled 0.9 U/h). -/
theorem missing_max_basal_fixed {inp : DBInputs} {p : Profile} (hp : inp.profile = some p)
    {c : Rat} (hc : p.current_basal = some (.fin c)) (hd : rd c = c) (h0 : 0 ≤ c) (h1 : c ≤ 2 ^ 30)
    (h : p.max_basal.js = .nan ∨ p.max_daily_basal.js = .nan) :
    (determineBasalFixed inp).units = none ∧
    ∀ r, (determineBasalFixed inp).rate = some (.fin r) → r ≤ c := by
  have hcb : p.current_basal.isSome = true := by rw [hc]; rfl
  have ht := triggerF12_of_missing hp hcb h
  obtain ⟨p', hp', -, -, e⟩ := fixed_of_trigger ht
  rw [hp] at hp'; cases hp'
  have hM := maxSafe_capProfile hc hd
  rw [e]
  refine ⟨?_, fun r hr => ?_⟩
  · rw [postF12_units, capRate_units]
    apply uncapped_units_noSmb rfl
    intro q hq
    have : q = capProfile p := (Option.some.inj hq).symm
    subst this; exact ⟨c, hM, h0⟩
  · rcases postF12_rate inp p (capRate (capProfile p) (determineBasalUncapped (inputF12 inp p))) with
      ⟨h1', -⟩ | ⟨-, h1', -⟩
    · rw [h1'] at hr
      rcases capRate_rate hM hd h0 h1 hr with ⟨-, hle⟩ | ⟨-, hle, -⟩ <;> exact hle
    · rw [h1'] at hr
      have : (0 : JsNum) = .fin r := Option.some.inj hr
      cases this; exact h0

/-- **R13 for the corrected version.** A missing profile or `current_basal` gives oref0's
    error and no command. -/
theorem missing_current_basal_fixed {inp : DBInputs}
    (h : inp.profile = none ∨ ∃ p, inp.profile = some p ∧ p.current_basal = none) :
    (determineBasalFixed inp).error = some "Error: could not get current basal rate" ∧
    (determineBasalFixed inp).rate = none ∧ (determineBasalFixed inp).units = none := by
  have hs : stProfile inp = .error (Result.err "Error: could not get current basal rate") := by
    rcases h with h | ⟨p, hp, hc⟩ <;> simp [stProfile, *]
  have hu : determineBasalUncapped inp = Result.err "Error: could not get current basal rate" := by
    unfold determineBasalUncapped; rw [hs]
  have h12 : triggerF12 inp = false := by
    unfold triggerF12
    rcases h with h | ⟨p, hp, hc⟩
    · rw [h]
    · rw [hp]; simp [hc]
  have hfix : determineBasalFixed inp = Result.err "Error: could not get current basal rate" := by
    rw [fixed_of_not12 h12]
    unfold determineBasalCapped
    split
    · rw [hu, capRate_of_zero (Or.inr rfl)]
    · exact hu
  rw [hfix]; exact ⟨rfl, rfl, rfl⟩

/-- **R13 for the corrected version.** With usable CGM data (the corrected check), a missing
    `min_bg` or `max_bg` gives no microbolus and no rate other than 0; when `maxSafeBasal` is
    a positive number it gives oref0's error and no rate. (With the F-12 trigger it also
    gives oref0's error.) -/
theorem missing_targets_fixed {inp : DBInputs} {p : Profile} {g : GluVals}
    (hs : stProfile inp = .ok p) (hg : stGlucoseF11 inp p = .ok g) (h : p.min_bg = none ∨ p.max_bg = none) :
    (determineBasalFixed inp).units = none ∧
    ((determineBasalFixed inp).rate = none ∨ (determineBasalFixed inp).rate = some 0) ∧
    (maxSafeOk p = true → (determineBasalFixed inp).error = some "Error: could not determine target_bg. " ∧
      (determineBasalFixed inp).rate = none) := by
  have hp := stProfile_ok hs
  have ht : stTargets p = .error (Result.err "Error: could not determine target_bg. ") := by
    unfold stTargets; rcases h with h | h <;> rw [h] <;> simp
  cases hok : maxSafeOk p with
  | false =>
    have htr : TriggerF12 inp := by simp [TriggerF12, triggerF12, hp, stProfile_cb hs, hok]
    obtain ⟨p', hp', -, -, e⟩ := fixed_of_trigger htr
    rw [hp] at hp'; cases hp'
    have hs' := stProfile_inputF12 (inp := inp) (stProfile_cb hs)
    have hg' := stGlucoseF11_inputF12 (q := p) hg
    have ht' : stTargets (capProfile p) = .error (Result.err "Error: could not determine target_bg. ") := ht
    have hpre : dbPreludeF11 (inputF12 inp p) = .error (Result.err "Error: could not determine target_bg. ") := by
      unfold dbPreludeF11; simp [hs', hg', ht', bind, Except.bind]
    rw [e, uncapped_of_st hs', hpre]
    simp only
    rw [capRate_of_zero (Or.inr rfl), postF12_err rfl]
    exact ⟨rfl, Or.inl rfl, fun h => by cases h⟩
  | true =>
    have hpre : dbPreludeF11 inp = .error (Result.err "Error: could not determine target_bg. ") := by
      unfold dbPreludeF11; simp [hs, hg, ht, bind, Except.bind]
    rw [fixed_of_ok hp hok, uncapped_of_st hs, hpre]
    simp only
    rw [capRate_of_zero (Or.inr rfl)]
    exact ⟨rfl, Or.inl rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- **R13 for the corrected version.** With usable CGM data (the corrected check) and
    targets, missing IOB data gives no microbolus and no rate other than 0; when
    `maxSafeBasal` is a positive number it gives oref0's error and no rate. (With the F-12
    trigger it also gives oref0's error.) -/
theorem missing_iob_fixed {inp : DBInputs} {p : Profile} {g : GluVals} {mm : JsNum × JsNum}
    (hs : stProfile inp = .ok p) (hg : stGlucoseF11 inp p = .ok g) (htg : stTargets p = .ok mm)
    (h : inp.iob_data = none) :
    (determineBasalFixed inp).units = none ∧
    ((determineBasalFixed inp).rate = none ∨ (determineBasalFixed inp).rate = some 0) ∧
    (maxSafeOk p = true → (determineBasalFixed inp).error = some "Error: iob_data undefined. " ∧
      (determineBasalFixed inp).rate = none) := by
  have hp := stProfile_ok hs
  have hi : stIob inp = .error (Result.err "Error: iob_data undefined. ") := by simp [stIob, h]
  cases hok : maxSafeOk p with
  | false =>
    have htr : TriggerF12 inp := by simp [TriggerF12, triggerF12, hp, stProfile_cb hs, hok]
    obtain ⟨p', hp', -, -, e⟩ := fixed_of_trigger htr
    rw [hp] at hp'; cases hp'
    have hs' := stProfile_inputF12 (inp := inp) (stProfile_cb hs)
    have hg' := stGlucoseF11_inputF12 (q := p) hg
    have htg' : stTargets (capProfile p) = .ok mm := htg
    have hi' : stIob (inputF12 inp p) = .error (Result.err "Error: iob_data undefined. ") := hi
    have hpre : dbPreludeF11 (inputF12 inp p) = .error (Result.err "Error: iob_data undefined. ") := by
      unfold dbPreludeF11; simp [hs', hg', htg', hi', bind, Except.bind]
    rw [e, uncapped_of_st hs', hpre]
    simp only
    rw [capRate_of_zero (Or.inr rfl), postF12_err rfl]
    exact ⟨rfl, Or.inl rfl, fun h => by cases h⟩
  | true =>
    have hpre : dbPreludeF11 inp = .error (Result.err "Error: iob_data undefined. ") := by
      unfold dbPreludeF11; simp [hs, hg, htg, hi, bind, Except.bind]
    rw [fixed_of_ok hp hok, uncapped_of_st hs, hpre]
    simp only
    rw [capRate_of_zero (Or.inr rfl)]
    exact ⟨rfl, Or.inl rfl, fun _ => ⟨rfl, rfl⟩⟩

/-! ### R5, R6, R7: microbolus limits -/

/-- **R5, R6, R7 for the corrected version.** For valid input, where `max_basal` and
    `max_daily_basal` may be missing (`ValidInputFixed`), a microbolus of the corrected
    version is oref0's microbolus, with the limits of `microbolus_limits`. (Under the F-12
    trigger there is no microbolus.) -/
theorem microbolus_limits_fixed {inp : DBInputs} (hv : ValidInputFixed inp) {u : Rat}
    (hu : (determineBasalFixed inp).units = some (.fin u)) :
    ∃ pre, dbPrelude inp = .ok pre ∧
      let c := dbPredict inp pre
      0 < u ∧
      (∀ mb, smbMaxBolus c = .fin mb → u ≤ mb + mb / 2 ^ 50 + 1 / 2 ^ 90) ∧
      (∃ i mi : Rat, pre.iobd.iob = some (.fin i) ∧ pre.max_iob = .fin mi ∧
        i + u ≤ mi + (mi - i) / 2 ^ 44 + 1 / 2 ^ 79) ∧
      (lastBolusAge c >ʲ smbInterval pre.p) = true := by
  obtain ⟨p, hp, vp⟩ := hv.profile
  obtain ⟨cb, hcb, hcb0⟩ := vp.current_basal
  have hcbs : p.current_basal.isSome = true := by rw [hcb]; rfl
  cases hok : maxSafeOk p with
  | false =>
    exfalso
    have ht : TriggerF12 inp := by simp [TriggerF12, triggerF12, hp, hcbs, hok]
    obtain ⟨p', hp', -, -, e⟩ := fixed_of_trigger ht
    rw [hp] at hp'; cases hp'
    have hU : (determineBasalUncapped (inputF12 inp p)).units = none := by
      apply uncapped_units_noSmb rfl
      intro q hq
      have : q = capProfile p := (Option.some.inj hq).symm
      subst this
      exact ⟨cb, maxSafe_capProfile hcb (vp.current_basal_double cb hcb), Rat.le_of_lt hcb0⟩
    rw [e, postF12_units, capRate_units, hU] at hu
    cases hu
  | true =>
    rw [fixed_of_ok hp hok, capRate_units] at hu
    obtain ⟨M, hM, -⟩ := maxSafe_of_ok hok
    have hv' := validInput_of_fixed hv hp hM
    rcases uncapped_valid_cases hv' with e | ⟨hn, -⟩
    · rw [e] at hu; exact microbolus_limits hv' hu
    · rw [hn] at hu; cases hu

/-! ### R11: IOB at or above `max_iob` -/

/-- **R11 for the corrected version.** For valid input whose corrected prelude succeeds
    with `pre`, if IOB is at least `max_iob`, the corrected version issues no microbolus and
    every finite rate is between 0 and the (sensitivity-adjusted) basal `pre.basal`. -/
theorem iob_at_max_fixed {inp : DBInputs} (hv : ValidInput inp) {pre : Pre} (hpre : dbPreludeF11 inp = .ok pre)
    {i mi : Rat} (hi : pre.iobd.iob = some (.fin i)) (hmi : pre.max_iob = .fin mi) (hle : mi ≤ i) :
    (determineBasalFixed inp).units = none ∧
    ∃ b, pre.basal = .fin b ∧ ∀ r, (determineBasalFixed inp).rate = some (.fin r) → 0 ≤ r ∧ r ≤ b := by
  have hpre' := dbPreludeF11_ok hpre
  obtain ⟨hu0, b, hb, hrb⟩ := iob_at_max hv hpre' hi hmi hle
  obtain ⟨p, g, mm, io, ct, meal, h1, -, -, -, -, -, -, -, -, -, -, -, hbasal, -, -⟩ := prelude_ok hpre'
  have hp := stProfile_ok h1
  have vp := hv.validProfile hp
  obtain ⟨-, M, -, -, hM, -, hMpos⟩ := maxSafeBasal_exists vp
  obtain ⟨hd, h30⟩ := maxSafeBasal_double vp hM
  obtain ⟨b', hb', hb0, -⟩ := adjustedBasal_bound hv hp hM ((mm.1 + mm.2) / 2)
  have hbb : b' = b := by rw [hbasal, hb'] at hb; cases hb; rfl
  subst hbb
  have hfix : determineBasalFixed inp = capRate p (dbDosePatched (dbPredict inp pre)) := by
    rw [fixed_of_ok hp (maxSafeOk_of_valid vp), uncapped_ok h1 hpre]
  rw [hfix, capRate_units]
  rcases dbDosePatched_cases (dbPredict inp pre) with h | ⟨h1', h2⟩
  · rw [h, ← determineBasal_ok hpre']
    refine ⟨hu0, b', hb, fun r hr => ?_⟩
    rcases capRate_rate hM hd (Rat.le_of_lt hMpos) h30 hr with ⟨hU, -⟩ | ⟨h0, hle', x, hx, hMx⟩
    · exact hrb r hU
    · exact ⟨h0, by have := (hrb x hx).2; grind⟩
  · have hlow : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true := by
      have : (pre.bg <ʲ pre.threshold || (dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true := h2
      simpa [Bool.or_eq_true] using this
    have hfirst : doseFirstBranch pre = false := h1'
    obtain ⟨hu, hr⟩ := lgs_patched hv hpre' hlow hfirst
    rw [determineBasalPatched_ok hpre'] at hu hr
    have hz : (dbDosePatched (dbPredict inp pre)).rate = some 0 ∨ (dbDosePatched (dbPredict inp pre)).rate = none := by
      rcases hr with ⟨hr, -⟩ | ⟨hr, -⟩
      · exact Or.inl hr
      · exact Or.inr hr
    rw [capRate_of_zero hz]
    refine ⟨hu, b', hb, fun r hr' => ?_⟩
    rcases hz with h | h <;> rw [h] at hr' <;> cases hr'
    exact ⟨Rat.le_refl, hb0⟩

/-! ### R8, R9: low glucose suspend with a valid duration -/

/-- **R8, R9 for the corrected version.** For valid input, where `max_basal` and
    `max_daily_basal` may be missing (`ValidInputFixed`), let the corrected prelude of the
    input the corrected version evaluates (`inputFixed inp`: `inp`, or under the F-12 trigger
    the input with the capped profile and no microbolus) succeed with `pre` (so the reading
    is dated and fresh). If BG or `minGuardBG` is below `threshold` and BG is not both below
    `threshold` and rising, the corrected version issues no microbolus and either sets rate
    0 for a whole number of minutes in `[30, 120]`, or issues nothing while a temp with more
    than 20 minutes left and rate 0 (if it is a double) is running; and the pump model
    accepts the command (`validate`). Compare `low_glucose_suspend`, where the duration can be
    NaN (F-23) and `max_basal` must be given. -/
theorem low_glucose_suspend_fixed {inp : DBInputs} (hv : ValidInputFixed inp) {pre : Pre}
    (hpre : dbPreludeF11 (inputFixed inp) = .ok pre)
    (hlow : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict (inputFixed inp) pre).minGuardBG <ʲ pre.threshold) = true)
    (hnotrising : (pre.bg <ʲ pre.threshold) = false ∨ (pre.minDelta >ʲ 0) = false) :
    (determineBasalFixed inp).units = none ∧
    (((determineBasalFixed inp).rate = some 0 ∧
        ∃ q : Int, (determineBasalFixed inp).duration = some (.fin q) ∧ 30 ≤ q ∧ q ≤ 120) ∨
     ((determineBasalFixed inp).rate = none ∧ (determineBasalFixed inp).duration = none ∧
       ∃ c ctDur x, inp.currenttemp = some c ∧ c.duration = some (.fin ctDur) ∧ 20 < ctDur ∧
         c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) ∧
    validate (determineBasalFixed inp) ≠ none := by
  obtain ⟨p, hp, vp⟩ := hv.profile
  obtain ⟨cb, hcb, hcb0⟩ := vp.current_basal
  have hdb := vp.current_basal_double cb hcb
  have hcbs : p.current_basal.isSome = true := by rw [hcb]; rfl
  have hfirst := doseFirstBranch_of_not_rising hnotrising
  cases hok : maxSafeOk p with
  | true =>
    have h12 : triggerF12 inp = false := by simp [triggerF12, hp, hok]
    rw [inputFixed_of_not12 h12] at hpre hlow
    obtain ⟨M, hM, -⟩ := maxSafe_of_ok hok
    have hv' := validInput_of_fixed hv hp hM
    have hpre' := dbPreludeF11_ok hpre
    obtain ⟨p', g, mm, io, ct, meal, h1, -⟩ := prelude_ok hpre'
    obtain ⟨hu, hr⟩ := lgs_patched hv' hpre' hlow hfirst
    have hz : (determineBasalPatched inp).rate = some 0 ∨ (determineBasalPatched inp).rate = none := by
      rcases hr with ⟨hr, -⟩ | ⟨hr, -⟩
      · exact Or.inl hr
      · exact Or.inr hr
    have hfix : determineBasalFixed inp = determineBasalPatched inp := by
      rw [fixed_of_ok hp hok, uncapped_ok h1 hpre, ← determineBasalPatched_ok hpre', capRate_of_zero hz]
    rw [hfix]
    exact ⟨hu, hr, lgs_patched_valid hv' hpre' hlow hfirst⟩
  | false =>
    have ht : TriggerF12 inp := by simp [TriggerF12, triggerF12, hp, hcbs, hok]
    rw [inputFixed_of_trigger hp ht] at hpre hlow
    obtain ⟨p', hp', -, -, e⟩ := fixed_of_trigger ht
    rw [hp] at hp'; cases hp'
    have hM := maxSafe_capProfile hcb hdb
    have hs' := stProfile_inputF12 (inp := inp) hcbs
    have hpre' := dbPreludeF11_ok hpre
    obtain ⟨hM', hcb', hct, hexc, hlow'⟩ :=
      lgs_setup_of hpre' (q := capProfile p) rfl hM (show (capProfile p).current_basal = some (.fin cb) from hcb) hlow hfirst
    have hrT : (dbPredict (inputF12 inp p) pre).rT.rate = none := rfl
    obtain ⟨hu, hr⟩ := dbDosePatched_lgs hM' (Rat.le_of_lt hcb0) hcb' hcb0 hexc hlow' hrT
    rw [dbPredict_rT_units] at hu
    rw [e, uncapped_ok hs' hpre]
    have hz : (dbDosePatched (dbPredict (inputF12 inp p) pre)).rate = some 0 ∨
        (dbDosePatched (dbPredict (inputF12 inp p) pre)).rate = none := by
      rcases hr with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    rw [capRate_of_zero hz]
    rcases hr with ⟨hr, q, hd, hq30, hq120⟩ | ⟨hr, hd, cc, ctDur, x, hc', hcd, h20, hcr, hx, hsmall⟩
    · obtain ⟨hr', hd'⟩ := postF12_some (inp := inp) (p := p) hr
      have hu' := postF12_units inp p (dbDosePatched (dbPredict (inputF12 inp p) pre))
      rw [hu] at hu'
      refine ⟨hu', Or.inl ⟨hr', q, by rw [hd', hd], hq30, hq120⟩, ?_⟩
      have hd'' : (postF12 inp p (dbDosePatched (dbPredict (inputF12 inp p) pre))).duration = some (.fin q) := by
        rw [hd', hd]
      simp [validate, validateTemp, validateBolus, validDuration, hr', hd'', hu',
        show (30 : Rat) ≤ q by exact_mod_cast hq30, show (q : Rat) ≤ 120 by exact_mod_cast hq120]
    · have hctin : inp.currenttemp = some cc := by
        have : inp.currenttemp = (inputF12 inp p).currenttemp := rfl
        rw [this, hct]; exact hc'
      have hkeep : ∀ ct, inp.currenttemp = some ct → (ct.rate.js >ʲ p.current_basal.js) = false := by
        intro ct hct'
        rw [hctin] at hct'; cases hct'
        rw [hcr, hcb]
        have := LeanAID.Fixed.pow2_le_of_double hdb hcb0
        show (JsNum.fin x >ʲ JsNum.fin cb) = false
        rw [gt_fin]; simp only [decide_eq_false_iff_not]; grind
      obtain ⟨hr', hd'⟩ := postF12_keep hr hkeep
      have hu' := postF12_units inp p (dbDosePatched (dbPredict (inputF12 inp p) pre))
      rw [hu] at hu'
      have hd'' : (postF12 inp p (dbDosePatched (dbPredict (inputF12 inp p) pre))).duration = none := by
        rw [hd', hd]; rfl
      refine ⟨hu', Or.inr ⟨hr', hd'', cc, ctDur, x, hctin, hcd, h20, hcr, hx⟩, ?_⟩
      simp [validate, validateTemp, validateBolus, hr', hd'', hu']

/-! ### Every finite rate is a double -/

/-- The fixes of F-11 and F-23 issue only doubles. -/
theorem uncapped_rateDbl (inp : DBInputs) : RateDouble.RateDbl (determineBasalUncapped inp) := by
  open RateDouble in
  intro q hq
  cases hs : stProfile inp with
  | error r =>
    have : determineBasalUncapped inp = determineBasal inp := by
      unfold determineBasalUncapped; rw [hs]; exact (determineBasal_of_stProfile_error hs).symm
    rw [this] at hq; exact rate_double hq
  | ok p =>
    rw [uncapped_of_st hs] at hq
    cases hpre : dbPreludeF11 inp with
    | error r =>
      rw [hpre] at hq; simp only at hq
      rcases dbPreludeF11_error hpre with h' | ⟨p', gs, -, -, hr⟩
      · exact prelude_error_rateDbl h' q hq
      · rw [hr] at hq
        obtain ⟨-, hrate⟩ := cgmResultF11_shape inp p' (gluVals (.fin inp.clock.now) gs)
        rcases hrate with h'' | h'' | h''
        · rw [h''] at hq; cases hq
        · rw [h''] at hq; cases hq; exact dbl_zero _ rfl
        · rw [h''] at hq; exact dbl_roundBasal _ _ q (Option.some.inj hq)
    | ok pre =>
      rw [hpre] at hq; simp only at hq
      rcases dbDosePatched_cases (dbPredict inp pre) with h' | ⟨h1, h2⟩
      · rw [h', ← determineBasal_ok (dbPreludeF11_ok hpre)] at hq; exact rate_double hq
      · unfold dbDosePatched at hq
        simp only [h1, h2, Bool.false_eq_true, ite_false, ite_true] at hq
        exact rateOk_trans (stb_rateOk _ _ _ _ _) rfl q hq

/-- The F-04 step issues only doubles if its input does. -/
theorem capRate_rateDbl (q : Profile) {U : Result} (hU : RateDouble.RateDbl U) : RateDouble.RateDbl (capRate q U) := by
  open RateDouble in
  have hdown : ∀ y m, Dbl (roundBasalDown y m) := by
    intro y m; unfold roundBasalDown; dsimp only; split <;> exact dbl_div _ _
  intro x hx
  rw [capRate_rate_eq] at hx
  cases hr : U.rate with
  | none => rw [hr] at hx; cases hx
  | some y =>
    rw [hr] at hx
    dsimp only at hx; split at hx
    · exact hdown _ _ x (Option.some.inj hx)
    · cases hx; exact hU x hr

open RateDouble in
/-- Every finite rate the corrected version issues is fixed by the model's binary64
    rounding (compare `rate_double`). No hypothesis. -/
theorem rate_double_fixed {inp : DBInputs} {x : Rat} (h : (determineBasalFixed inp).rate = some (.fin x)) :
    Binary64.rd x = x := by
  by_cases ht : TriggerF12 inp
  · obtain ⟨p, -, -, -, e⟩ := fixed_of_trigger ht
    rw [e] at h
    rcases postF12_rate inp p (capRate (capProfile p) (determineBasalUncapped (inputF12 inp p))) with ⟨hr, -⟩ | ⟨-, hr, -⟩
    · rw [hr] at h; exact capRate_rateDbl _ (uncapped_rateDbl _) x h
    · rw [hr] at h
      have : (0 : JsNum) = .fin x := Option.some.inj h
      cases this; exact dbl_zero _ rfl
  · have h12 : triggerF12 inp = false := by simpa [TriggerF12] using ht
    rw [fixed_of_not12 h12] at h
    unfold determineBasalCapped at h
    split at h
    · exact capRate_rateDbl _ (uncapped_rateDbl _) x h
    · exact uncapped_rateDbl _ x h

end LeanAID.Fixed
