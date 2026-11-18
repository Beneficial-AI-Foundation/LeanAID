/-
  LeanAID.Proofs.Safety — headline safety theorems about `determineBasal`, the
  transcription of oref0's `determine_basal`.
-/
import LeanAID.Spec.Valid
import LeanAID.Proofs.Dose

namespace LeanAID.Proofs

open JsNum

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
  have a1 : cb ≤ m3 * mdb := by
    have : 1 * mdb ≤ m3 * mdb := Rat.mul_le_mul_of_nonneg_right h3 (by grind)
    grind
  have a2 : cb ≤ m4 * cb := by
    have : 1 * cb ≤ m4 * cb := Rat.mul_le_mul_of_nonneg_right h4 (by grind)
    grind
  subst hM
  constructor <;> split <;> (try split) <;> grind

/-- `rnd(x, 2)` of a value on the 0.01 grid is itself. -/
theorem rts100_grid {n : Int} : rts ((n : Rat) / 100) 100 = (n : Rat) / 100 := by
  unfold rts
  rw [Rat.div_mul_cancel (by decide), roundInt_intCast]

theorem div_pos_of_neg_neg {a b : Rat} (ha : a < 0) (hb : b < 0) : 0 < a / b := by
  have hq : a / b * b = a := Rat.div_mul_cancel (by grind)
  by_cases hq0 : 0 < a / b
  · exact hq0
  · exfalso
    have h1 : 0 ≤ (-(a / b)) * (-b) := Rat.mul_nonneg (by grind) (by grind)
    have h2 : (-(a / b)) * (-b) = a / b * b := by grind
    grind

/-- The temp-target ratio is NaN or positive (given a positive `autosens_max`). -/
theorem tempTargetRatio_pos {p : Profile} {amax : Rat} (hamax : p.autosens_max = some (.fin amax)) (hpos : 0 < amax)
    (p' : Profile) (t : JsNum) (hp' : p' = p := by rfl) :
    tempTargetRatio p t = .nan ∨ ∃ y, tempTargetRatio p t = .fin y ∧ 0 < y := by
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
      split
      · right; exact ⟨amax, by simp [hamax], hpos⟩
      · rename_i hc
        have hne : (h - 100 + t - 100) ≠ 0 := by
          intro h0
          apply hc
          have : (h - 100) * (h - 100 + t - 100) = 0 := by rw [h0]; grind
          grind
        rw [JsNum.fin_div hne]
        right
        refine ⟨(h - 100) / (h - 100 + t - 100), rfl, ?_⟩
        have hprod : 0 < (h - 100) * (h - 100 + t - 100) := by grind
        by_cases hpos2 : 0 < h - 100 + t - 100
        · have h1 : 0 < h - 100 := by
            by_cases hh : 0 < h - 100
            · exact hh
            · exfalso
              have : (h - 100) * (h - 100 + t - 100) ≤ 0 * (h - 100 + t - 100) :=
                Rat.mul_le_mul_of_nonneg_right (by grind) (by grind)
              grind
          exact (Rat.lt_div_iff hpos2).mpr (by grind)
        · have hneg2 : h - 100 + t - 100 < 0 := by
            have : h - 100 + t - 100 ≠ 0 := hne
            grind
          have hneg1 : h - 100 < 0 := by
            by_cases hh : h - 100 < 0
            · exact hh
            · exfalso
              have : (h - 100 + t - 100) * (h - 100) ≤ 0 * (h - 100) :=
                Rat.mul_le_mul_of_nonneg_right (by grind) (by grind)
              grind
          exact div_pos_of_neg_neg hneg1 hneg2

/-- The sensitivity ratio oref0 uses (lines 250-281) is missing, NaN, or a number
    in `[0, autosens_max]`, for valid input. -/
theorem sensitivityRatio_range {inp : DBInputs} (hv : ValidInput inp) {p : Profile} (hp : inp.profile = some p)
    {amax : Rat} (hamax : p.autosens_max = some (.fin amax)) (t : JsNum) :
    sensitivityRatioOf p inp.autosens_data t = none ∨ sensitivityRatioOf p inp.autosens_data t = some .nan ∨
    ∃ x, sensitivityRatioOf p inp.autosens_data t = some (.fin x) ∧ 0 ≤ x ∧ x ≤ amax := by
  have vp := hv.validProfile hp
  obtain ⟨amax', cb, M, hamax', hpos, ⟨n, hn⟩, -, -, -⟩ := vp.autosens_max
  rw [hamax] at hamax'; cases hamax'
  unfold sensitivityRatioOf
  simp only
  split
  · -- temp-target branch
    right
    have hsr' := tempTargetRatio_pos hamax hpos p t
    generalize tempTargetRatio p t = sr at hsr' ⊢
    rcases hsr' with h0 | ⟨y, hy, hy0⟩
    · subst h0; left; simp [rnd, JsNum.round, JsNum.min, hamax, Option.js, JsNum.ofOpt]
    · subst hy
      right
      simp only [hamax, Option.js, JsNum.ofOpt, JsNum.min, rnd, JsNum.round, pow10_two]
      refine ⟨_, rfl, ?_, ?_⟩
      · apply rts_nonneg (by decide); split <;> grind
      · have hm : (if y ≤ amax then y else amax) ≤ amax := by split <;> grind
        have := rts_mono (s := 100) (by decide) hm
        rw [hn] at this ⊢; rw [rts100_grid] at this; exact this
  · -- autosens branch
    split
    · rename_i a ha
      obtain ⟨r, amax', hr, hamax', hr0, hra⟩ := hv.autosens p a hp ha
      rw [hamax] at hamax'; cases hamax'
      right; right; exact ⟨r, hr, Rat.le_of_lt hr0, hra⟩
    · left; rfl

/-- The adjusted basal (lines 142-143, 282-290) is a multiple of 0.025 between 0
    and `round_basal(maxSafeBasal)`, for valid input. -/
theorem adjustedBasal_bound {inp : DBInputs} (hv : ValidInput inp) {p : Profile} (hp : inp.profile = some p)
    {M : Rat} (hM : getMaxSafeBasal p = .fin M) (t : JsNum) :
    ∃ b, adjustedBasal p (sensitivityRatioOf p inp.autosens_data t) = .fin b ∧ 0 ≤ b ∧
      (∃ k : Int, 0 ≤ k ∧ b = (k : Rat) / 40) ∧ b ≤ rbR M p.model ∧ rbR b p.model = b := by
  have vp := hv.validProfile hp
  obtain ⟨cb, hcb, hcb0⟩ := vp.current_basal
  obtain ⟨amax, cb', M', hamax, -, -, hcb', hM', hle⟩ := vp.autosens_max
  rw [hcb] at hcb'; cases hcb'
  rw [hM] at hM'; cases hM'
  obtain ⟨hcbM, -⟩ := maxSafeBasal_ge vp hM hcb
  have base : ∃ b, profileCurrentBasal p = .fin b ∧ 0 ≤ b ∧
      (∃ k : Int, 0 ≤ k ∧ b = (k : Rat) / 40) ∧ b ≤ rbR M p.model ∧ rbR b p.model = b := by
    refine ⟨rbR cb p.model, ?_, rbR_nonneg _ (by grind), rbR_grid _ (by grind), rbR_mono _ hcbM,
      rbR_idem _ (by grind)⟩
    simp [profileCurrentBasal, hcb, Option.js, JsNum.ofOpt, roundBasal_fin]
  unfold adjustedBasal
  rcases sensitivityRatio_range hv hp hamax t with h | h | ⟨x, h, hx0, hxa⟩
  · rw [h]; simp only [Option.truthyN]; exact base
  · rw [h]; simp only [Option.truthyN, JsNum.truthy]; exact base
  · rw [h]
    by_cases hx : x = 0
    · subst hx; simp only [Option.truthyN, JsNum.truthy]; simp; exact base
    · have ht : (some (JsNum.fin x)).truthyN = true := by simp [Option.truthyN, JsNum.truthy, hx]
      rw [ite_eq_left_iff.mpr (fun h => absurd ht h)]
      have hcx0 : 0 ≤ cb * x := Rat.mul_nonneg (by grind) hx0
      have hcx : cb * x ≤ M := by
        have : cb * x ≤ cb * amax := Rat.mul_le_mul_of_nonneg_left hxa (by grind)
        grind
      refine ⟨rbR (cb * x) p.model, ?_, rbR_nonneg _ hcx0, rbR_grid _ hcx0, rbR_mono _ hcx, rbR_idem _ hcx0⟩
      simp [hcb, Option.js, JsNum.ofOpt, HMul.hMul, Mul.mul, JsNum.mul, roundBasal_fin]

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
