/-
  LeanAID.Proofs.Safety — headline safety theorems about `determineBasal`, the
  transcription of oref0's `determine_basal`.
-/
import LeanAID.Spec.Valid
import LeanAID.Proofs.Dose

namespace LeanAID.Proofs

open JsNum
open Binary64 (rd rd_mono rd_nonneg rd_rd)

/-! ### Facts from valid input -/

theorem _root_.LeanAID.ValidInput.validProfile {inp : DBInputs} (hv : ValidInput inp) {p : Profile} (hp : inp.profile = some p) :
    ValidProfile p := by
  obtain ⟨p', hp', hv'⟩ := hv.profile
  rw [hp] at hp'; cases hp'; exact hv'

theorem multiplierOr_ge {m : Option JsNum} {d : Rat} (hd : 1 ≤ d) (h : ∀ x : Rat, m = some (.fin x) → 1 ≤ x) :
    ∃ x, multiplierOr m d = .fin x ∧ 1 ≤ x := by
  unfold multiplierOr
  cases m with
  | none => exact ⟨d, rfl, hd⟩
  | some v =>
    cases v with
    | nan => exact ⟨d, rfl, hd⟩
    | fin x => exact ⟨x, rfl, h x rfl⟩

/-- `maxSafeBasal ≥ current_basal` for a valid profile. -/
theorem maxSafeBasal_ge {p : Profile} (vp : ValidProfile p) {M cb : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hcb : p.current_basal = some (.fin cb)) : cb ≤ M ∧ 0 < M := by
  obtain ⟨cb0, hcb0, hpos⟩ := vp.current_basal
  rw [hcb] at hcb0; cases hcb0
  obtain ⟨mb, cb1, hmb, hcb1, hle1⟩ := vp.max_basal
  rw [hcb] at hcb1; cases hcb1
  obtain ⟨mdb, cb2, hmdb, hcb2, hle2⟩ := vp.max_daily_basal
  rw [hcb] at hcb2; cases hcb2
  obtain ⟨m3, hm3, h3⟩ := multiplierOr_ge (d := 3) (by decide) vp.max_daily_safety_multiplier
  obtain ⟨m4, hm4, h4⟩ := multiplierOr_ge (d := 4) (by decide) vp.current_basal_safety_multiplier
  unfold getMaxSafeBasal at hM
  rw [hmb, hmdb, hcb, hm3, hm4] at hM
  simp only [Option.js_some, JsNum.fin_mul, JsNum.min3_fin, JsNum.min_fin] at hM
  injection hM with hM
  have hd := vp.current_basal_double cb hcb
  have a1 : cb ≤ rd (m3 * mdb) := by
    have : 1 * mdb ≤ m3 * mdb := Rat.mul_le_mul_of_nonneg_right h3 (by grind)
    have := rd_mono (show cb ≤ m3 * mdb by grind); rwa [hd] at this
  have a2 : cb ≤ rd (m4 * cb) := by
    have : 1 * cb ≤ m4 * cb := Rat.mul_le_mul_of_nonneg_right h4 (by grind)
    have := rd_mono (show cb ≤ m4 * cb by grind); rwa [hd] at this
  subst hM
  constructor <;> split <;> (try split) <;> grind

/-- `maxSafeBasal` of a valid profile is a double, at most `2^30`. -/
theorem maxSafeBasal_double {p : Profile} (vp : ValidProfile p) {M : Rat} (hM : getMaxSafeBasal p = .fin M) :
    rd M = M ∧ M ≤ 2 ^ 30 := by
  obtain ⟨mb, cb1, hmb, hcb1, -⟩ := vp.max_basal
  obtain ⟨mdb, cb2, hmdb, hcb2, -⟩ := vp.max_daily_basal
  obtain ⟨m3, hm3, -⟩ := multiplierOr_ge (d := 3) (by decide) vp.max_daily_safety_multiplier
  obtain ⟨m4, hm4, -⟩ := multiplierOr_ge (d := 4) (by decide) vp.current_basal_safety_multiplier
  obtain ⟨hmbd, hmb30⟩ := vp.max_basal_double mb hmb
  unfold getMaxSafeBasal at hM
  rw [hmb, hmdb, hcb1, hm3, hm4] at hM
  simp only [Option.js_some, JsNum.fin_mul, JsNum.min3_fin, JsNum.min_fin] at hM
  injection hM with hM
  subst hM
  constructor
  · split <;> (try split) <;> simp [rd_rd, hmbd]
  · split <;> (try split) <;> grind

theorem div_pos_of_neg_neg {a b : Rat} (ha : a < 0) (hb : b < 0) : 0 < a / b := by
  have hq : a / b * b = a := Rat.div_mul_cancel (by grind)
  by_cases hq0 : 0 < a / b
  · exact hq0
  · exfalso
    have h1 : 0 ≤ (-(a / b)) * (-b) := Rat.mul_nonneg (by grind) (by grind)
    have h2 : (-(a / b)) * (-b) = a / b * b := by grind
    grind

theorem div_nonneg_of_mul_pos {a b : Rat} (h : 0 < a * b) : 0 ≤ a / b := by
  by_cases hb : 0 < b
  · have ha : 0 < a := by
      by_cases ha : 0 < a
      · exact ha
      · exfalso
        have : a * b ≤ 0 * b := Rat.mul_le_mul_of_nonneg_right (by grind) (by grind)
        grind
    exact Rat.le_of_lt ((Rat.lt_div_iff hb).mpr (by grind))
  · have hb' : b < 0 := by
      have : b ≠ 0 := by intro h0; subst h0; simp at h
      grind
    have ha : a < 0 := by
      by_cases ha : a < 0
      · exact ha
      · exfalso
        have : b * a ≤ 0 * a := Rat.mul_le_mul_of_nonneg_right (by grind) (by grind)
        grind
    exact Rat.le_of_lt (div_pos_of_neg_neg ha hb')

/-- The temp-target ratio is NaN or non-negative (given a positive `autosens_max`). -/
theorem tempTargetRatio_pos {p : Profile} {amax : Rat} (hamax : p.autosens_max = some (.fin amax)) (hpos : 0 < amax)
    (p' : Profile) (t : JsNum) (hp' : p' = p := by rfl) :
    tempTargetRatio p t = .nan ∨ ∃ y, tempTargetRatio p t = .fin y ∧ 0 ≤ y := by
  unfold tempTargetRatio
  simp only
  generalize halfBasalTargetOf p = hbt
  cases hbt with
  | nan => simp
  | fin h =>
    cases t with
    | nan => simp
    | fin t =>
      simp only [JsNum.ofNat_eq, JsNum.fin_sub, JsNum.fin_add, JsNum.fin_mul, JsNum.le_fin, decide_eq_true_eq]
      generalize rd (h - 100) = a
      generalize rd (rd (a + t) - 100) = b
      split
      · right; exact ⟨amax, by simp [hamax], Rat.le_of_lt hpos⟩
      · rename_i hc
        have hab : 0 < a * b := by
          by_cases h0 : 0 < a * b
          · exact h0
          · exfalso; apply hc; exact Binary64.rd_nonpos (by grind)
        have hb : b ≠ 0 := by intro h0; subst h0; simp at hab
        rw [JsNum.fin_div hb]
        right
        exact ⟨_, rfl, rd_nonneg (div_nonneg_of_mul_pos hab)⟩

/-- The sensitivity ratio oref0 uses (lines 250-281) is missing, NaN, or a number
    `x ≥ 0` with `current_basal · x ≤ maxSafeBasal`, for valid input. -/
theorem sensitivityRatio_range {inp : DBInputs} (hv : ValidInput inp) {p : Profile} (hp : inp.profile = some p)
    {cb M : Rat} (hcb : p.current_basal = some (.fin cb)) (hcb0 : 0 < cb) (hM : getMaxSafeBasal p = .fin M)
    (t : JsNum) :
    sensitivityRatioOf p inp.autosens_data t = none ∨ sensitivityRatioOf p inp.autosens_data t = some .nan ∨
    ∃ x, sensitivityRatioOf p inp.autosens_data t = some (.fin x) ∧ 0 ≤ x ∧ cb * x ≤ M := by
  have vp := hv.validProfile hp
  unfold sensitivityRatioOf
  simp only
  split
  · -- temp-target branch
    right
    cases hamax : p.autosens_max with
    | none => left; simp [rnd, JsNum.round]
    | some av =>
      cases av with
      | nan => left; simp [rnd, JsNum.round]
      | fin amax =>
        obtain ⟨hpos, ⟨n, hn0, hnB, hn⟩, hle⟩ := vp.autosens_max amax hamax
        have hle := hle cb M hcb hM
        have hsr' := tempTargetRatio_pos hamax hpos p t
        generalize tempTargetRatio p t = sr at hsr' ⊢
        rcases hsr' with h0 | ⟨y, hy, hy0⟩
        · subst h0; left; simp [rnd, JsNum.round]
        · subst hy
          right
          simp only [Option.js_some, JsNum.min_fin, rnd, rnd_fin, pow10_two]
          refine ⟨_, rfl, ?_, ?_⟩
          · apply rts_nonneg (by decide); split <;> grind
          · have hm : (if y ≤ amax then y else amax) ≤ amax := by split <;> grind
            have := rts_mono (s := 100) (by decide) hm
            have hn41 : (n : Rat) ≤ 2 ^ 41 := by
              have : (n : Rat) ≤ ((2 ^ 41 : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
              rw [show ((2 ^ 41 : Int) : Rat) = 2 ^ 41 by decide +kernel] at this; exact this
            have hfix := rts_grid_fix (s := 100) (by decide) (by decide) hn0 hn41
            rw [← hn] at hfix
            rw [hfix] at this
            have := Rat.mul_le_mul_of_nonneg_left this (Rat.le_of_lt hcb0)
            grind
  · -- autosens branch
    split
    · rename_i a ha
      obtain ⟨r, hr, hr0, hra⟩ := hv.autosens p a hp ha
      right; right; exact ⟨r, hr, Rat.le_of_lt hr0, hra cb M hcb hM⟩
    · left; rfl

/-- The adjusted basal (lines 142-143, 282-290) is an output of `round_basal` (the
    double nearest to `n/s`, `s ∈ {10, 20, 40}`) between 0 and
    `round_basal(maxSafeBasal)`, which `round_basal` leaves unchanged, for valid input. -/
theorem adjustedBasal_bound {inp : DBInputs} (hv : ValidInput inp) {p : Profile} (hp : inp.profile = some p)
    {M : Rat} (hM : getMaxSafeBasal p = .fin M) (t : JsNum) :
    ∃ b, adjustedBasal p (sensitivityRatioOf p inp.autosens_data t) = .fin b ∧ 0 ≤ b ∧
      (∃ n : Int, ∃ s : Rat, 0 ≤ n ∧ (s = 10 ∨ s = 20 ∨ s = 40) ∧ b = rd ((n : Rat) / s)) ∧
      b ≤ rbR M p.model ∧ rbR b p.model = b := by
  have vp := hv.validProfile hp
  obtain ⟨cb, hcb, hcb0⟩ := vp.current_basal
  obtain ⟨hcbM, -⟩ := maxSafeBasal_ge vp hM hcb
  obtain ⟨hMd, hM30⟩ := maxSafeBasal_double vp hM
  have base : ∀ y : Rat, 0 ≤ y → y ≤ M → ∃ b, JsNum.fin (rbR y p.model) = .fin b ∧ 0 ≤ b ∧
      (∃ n : Int, ∃ s : Rat, 0 ≤ n ∧ (s = 10 ∨ s = 20 ∨ s = 40) ∧ b = rd ((n : Rat) / s)) ∧
      b ≤ rbR M p.model ∧ rbR b p.model = b := by
    intro y hy0 hyM
    obtain ⟨n, s, hn, hs, he⟩ := rbR_form p.model hy0
    exact ⟨rbR y p.model, rfl, rbR_nonneg _ hy0, ⟨n, s, hn, hs, he⟩, rbR_mono _ hyM,
      rbR_idem _ hy0 (by grind)⟩
  have hcbase : ∃ b, profileCurrentBasal p = .fin b ∧ 0 ≤ b ∧
      (∃ n : Int, ∃ s : Rat, 0 ≤ n ∧ (s = 10 ∨ s = 20 ∨ s = 40) ∧ b = rd ((n : Rat) / s)) ∧
      b ≤ rbR M p.model ∧ rbR b p.model = b := by
    have e : profileCurrentBasal p = .fin (rbR cb p.model) := by
      simp [profileCurrentBasal, hcb, roundBasal_fin]
    rw [e]; exact base cb (by grind) hcbM
  unfold adjustedBasal
  rcases sensitivityRatio_range hv hp hcb hcb0 hM t with h | h | ⟨x, h, hx0, hcx⟩
  · rw [h]; simp only [Option.truthyN]; exact hcbase
  · rw [h]; simp only [Option.truthyN, JsNum.truthy]; exact hcbase
  · rw [h]
    by_cases hx : x = 0
    · subst hx
      rw [ite_cond_eq_false _ _ (by simp [Option.truthyN, JsNum.truthy])]; exact hcbase
    · have ht : (some (JsNum.fin x)).truthyN = true := by simp [Option.truthyN, JsNum.truthy, hx]
      rw [ite_eq_left_iff.mpr (fun h => absurd ht h)]
      have hcx0 : 0 ≤ cb * x := Rat.mul_nonneg (by grind) hx0
      have e : roundBasal ((some (JsNum.fin cb)).js * (some (JsNum.fin x)).js) p.model
          = .fin (rbR (rd (cb * x)) p.model) := by
        simp [roundBasal_fin]
      simp only [hcb, e]
      have h1 : rd (cb * x) ≤ M := by have := rd_mono hcx; rwa [hMd] at this
      exact base _ (rd_nonneg hcx0) h1

/-- A valid profile has a finite, positive `maxSafeBasal` at least `current_basal`. -/
theorem maxSafeBasal_exists {p : Profile} (vp : ValidProfile p) :
    ∃ cb M : Rat, p.current_basal = some (.fin cb) ∧ 0 < cb ∧ getMaxSafeBasal p = .fin M ∧ cb ≤ M ∧ 0 < M := by
  obtain ⟨cb, hcb, hpos⟩ := vp.current_basal
  obtain ⟨mb, cb1, hmb, hcb1, -⟩ := vp.max_basal
  obtain ⟨mdb, cb2, hmdb, hcb2, -⟩ := vp.max_daily_basal
  obtain ⟨m3, hm3, -⟩ := multiplierOr_ge (d := 3) (by decide) vp.max_daily_safety_multiplier
  obtain ⟨m4, hm4, -⟩ := multiplierOr_ge (d := 4) (by decide) vp.current_basal_safety_multiplier
  have hfin : ∃ M, getMaxSafeBasal p = .fin M := by
    unfold getMaxSafeBasal
    rw [hmb, hmdb, hcb, hm3, hm4]
    simp only [Option.js_some, JsNum.fin_mul, JsNum.min3_fin, JsNum.min_fin]
    exact ⟨_, rfl⟩
  obtain ⟨M, hM⟩ := hfin
  obtain ⟨h1, h2⟩ := maxSafeBasal_ge vp hM hcb
  exact ⟨cb, M, hcb, hpos, hM, h1, h2⟩

/-! ### H1: the temp basal ceiling -/

/-- **H1 (R1, R2).** For valid input, every finite temp basal rate that
    `determine_basal` issues is between 0 and `round_basal(maxSafeBasal)`, where
    `maxSafeBasal = min(max_basal, max_daily_safety_multiplier × max_daily_basal,
    current_basal_safety_multiplier × current_basal)`.
    (`round_basal(maxSafeBasal)` can exceed `maxSafeBasal` by up to half a pump
    increment: see `rate_can_exceed_maxSafeBasal` and FINDINGS F-04. When
    `maxSafeBasal` is itself on the pump's increment grid, the bound is
    `maxSafeBasal`: see `rate_le_maxSafeBasal_of_grid`.) -/
theorem rate_le_roundBasal_maxSafeBasal {inp : DBInputs} (hv : ValidInput inp) {p : Profile}
    (hp : inp.profile = some p) {M r : Rat} (hM : getMaxSafeBasal p = .fin M)
    (hr : (determineBasal inp).rate = some (.fin r)) :
    0 ≤ r ∧ r ≤ rbR M p.model := by
  have vp := hv.validProfile hp
  obtain ⟨cb, hcb, hcb0⟩ := vp.current_basal
  obtain ⟨hcbM, hMpos⟩ := maxSafeBasal_ge vp hM hcb
  have hM0 : 0 ≤ M := Rat.le_of_lt hMpos
  unfold determineBasal at hr
  cases hpre : dbPrelude inp with
  | error e =>
    rw [hpre] at hr
    have hMall : ∀ p', inp.profile = some p' → ∃ M', getMaxSafeBasal p' = .fin M' ∧ 0 ≤ M' := by
      intro p' hp'; rw [hp] at hp'; cases hp'; exact ⟨M, hM, hM0⟩
    obtain ⟨-, he⟩ := prelude_error hpre hMall
    rcases he with he | he | ⟨p', hp', he⟩
    · simp [he] at hr
    · rw [he] at hr; injection hr with hr; injection hr with hr; subst hr
      exact ⟨Rat.le_refl, rbR_nonneg _ hM0⟩
    · rw [hp] at hp'; cases hp'
      rw [he] at hr; injection hr with hr
      simp [profileCurrentBasal, hcb, Option.js, JsNum.ofOpt, roundBasal_fin] at hr
      subst hr
      exact ⟨rbR_nonneg _ (by grind), rbR_mono _ hcbM⟩
  | ok pre =>
    rw [hpre] at hr
    obtain ⟨p', g, mm, io, ct, meal, h1, -, -, -, -, -, hpp, -, -, -, -, -, hbasal, -, -⟩ := prelude_ok hpre
    have := stProfile_ok h1; rw [hp] at this; cases this
    obtain ⟨b, hb, hb0, hbg, hbM, -⟩ := adjustedBasal_bound hv hp hM ((mm.1 + mm.2) / 2)
    have H : DoseHyp (dbPredict inp pre) M b :=
      { hM := by simp [hpp, hM], hM0, hb := by simp [hbasal, hb], hb0, hbgrid := hbg, hbM := by simp [hpp, hbM] }
    rcases dbDose_rateOk H r hr with h | h
    · simp at h
    · simpa [hpp] using h

/-- When `maxSafeBasal` is on the pump's increment grid (`round_basal` leaves it
    unchanged), every finite issued rate is at most `maxSafeBasal` (R1 as stated). -/
theorem rate_le_maxSafeBasal_of_grid {inp : DBInputs} (hv : ValidInput inp) {p : Profile}
    (hp : inp.profile = some p) {M r : Rat} (hM : getMaxSafeBasal p = .fin M) (hgrid : rbR M p.model = M)
    (hr : (determineBasal inp).rate = some (.fin r)) : 0 ≤ r ∧ r ≤ M := by
  have := rate_le_roundBasal_maxSafeBasal hv hp hM hr
  rw [hgrid] at this; exact this

end LeanAID.Proofs
