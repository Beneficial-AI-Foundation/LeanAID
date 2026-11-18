/-
  LeanAID.Proofs.Headline — headline theorems H2 (microbolus limits), H4 (IOB at
  or above max_iob) and H6 (rounding), stated on `determineBasal`.
  H1 is in `Proofs/Safety.lean`, H3 and H5 in `Proofs/Hypo.lean`.
-/
import LeanAID.Proofs.Smb

namespace LeanAID.Proofs

open JsNum

/-- A microbolus is only issued after a successful prelude. -/
theorem units_needs_prelude {inp : DBInputs} (hv : ValidInput inp) {u : JsNum}
    (hu : (determineBasal inp).units = some u) : ∃ pre, dbPrelude inp = .ok pre := by
  unfold determineBasal at hu
  cases hpre : dbPrelude inp with
  | ok pre => exact ⟨pre, rfl⟩
  | error e =>
    rw [hpre] at hu
    have hM : ∀ p, inp.profile = some p → ∃ M, getMaxSafeBasal p = .fin M ∧ 0 ≤ M := by
      intro p hp
      have vp := hv.validProfile hp
      obtain ⟨-, M, -, -, hM, -, hMpos⟩ := maxSafeBasal_exists vp
      exact ⟨M, hM, Rat.le_of_lt hMpos⟩
    obtain ⟨hn, -⟩ := prelude_error hpre hM
    rw [hn] at hu; cases hu

/-- **H2 (R5, R6, R7): microbolus limits.** For valid input, if `determine_basal`
    issues a microbolus of `u` units (a finite number), then `u > 0`; the
    microbolus is the one the SMB block computed, so it is at most `maxBolus`
    (lines 1078-1095); IOB plus `u` does not exceed `max_iob`; and the last bolus
    was more than `SMBInterval` minutes ago. The two bounds hold up to double
    rounding: relative 2^-50 (resp. 2^-44) plus at most 2^-90 (resp. 2^-79) units
    (FINDINGS F-16). -/
theorem microbolus_limits {inp : DBInputs} (hv : ValidInput inp) {u : Rat}
    (hu : (determineBasal inp).units = some (.fin u)) :
    ∃ pre, dbPrelude inp = .ok pre ∧
      let c := dbPredict inp pre
      0 < u ∧
      (∀ mb, smbMaxBolus c = .fin mb → u ≤ mb + mb / 2 ^ 50 + 1 / 2 ^ 90) ∧
      (∃ i mi : Rat, pre.iobd.iob = some (.fin i) ∧ pre.max_iob = .fin mi ∧
        i + u ≤ mi + (mi - i) / 2 ^ 44 + 1 / 2 ^ 79) ∧
      (lastBolusAge c >ʲ smbInterval pre.p) = true := by
  obtain ⟨pre, hpre⟩ := units_needs_prelude hv hu
  refine ⟨pre, hpre, ?_⟩
  simp only
  unfold determineBasal at hu; rw [hpre] at hu; simp only at hu
  rcases dbDose_units (dbPredict inp pre) _ hu with h | hsmb
  · simp at h
  have hsmb' := hsmb
  obtain ⟨hg, hueq⟩ := hsmb
  -- positivity and the interval come from `smbGivesBolus`
  unfold smbGivesBolus at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨hage, hpos⟩ := hg
  rw [← hueq] at hpos
  simp at hpos
  obtain ⟨p, g, mm, io, ct, meal, h1, -, -, -, -, -, hpp, -, -, -, -, -, -, hmi, -⟩ := prelude_ok hpre
  have hp := stProfile_ok h1
  have vp := hv.validProfile hp
  obtain ⟨mi, hmi', hmi0⟩ := vp.max_iob
  obtain ⟨i, hi⟩ := prelude_iob_fin hpre
  have hmiv : pre.max_iob = .fin mi := by rw [hmi, hmi']; rfl
  have hinc : ∀ x : Rat, (dbPredict inp pre).p.bolus_increment = some (.fin x) → 0 < x := by
    show ∀ x : Rat, pre.p.bolus_increment = some (.fin x) → 0 < x
    rw [hpp]; exact vp.bolus_increment
  have hroom : (dbPredict inp pre).max_iob - (dbPredict inp pre).iobd.iob.js = .fin (Binary64.rd (mi - i)) := by
    show pre.max_iob - pre.iobd.iob.js = _
    rw [hmiv, hi]; rfl
  refine ⟨hpos, ?_, ⟨i, mi, hi, hmiv, ?_⟩, ?_⟩
  · intro mb hmb
    have := hueq
    cases hir : smbInsulinReq (dbPredict inp pre) with
    | nan =>
      exfalso; rw [hir] at this
      unfold smbMicroBolus at this
      obtain ⟨x, hx, -⟩ := smbBolusIncrement_pos hinc
      simp [hx] at this
    | fin ir =>
      rw [hir] at this
      exact ((smbMicroBolus_le hinc this.symm hpos).2.2 mb hmb).2
  · obtain ⟨h0, hle⟩ := microbolus_le_room hinc hroom hsmb' hpos
    have hmi_i : 0 < mi - i := by
      by_cases hc : 0 < mi - i
      · exact hc
      · have := Binary64.rd_nonpos (show mi - i ≤ 0 by grind); grind
    obtain ⟨-, r2⟩ := rd_close (Rat.le_of_lt hmi_i)
    have := tiny_pos; have := tiny_le
    grind
  · exact hage

/-- **H4 (R11): insulin on board at or above max_iob.** For valid input, if the
    prelude succeeds and IOB is at least `max_iob`, then every finite issued rate
    is at most the (sensitivity-adjusted) basal `pre.basal` and no microbolus is
    issued. -/
theorem iob_at_max {inp : DBInputs} (hv : ValidInput inp) {pre : Pre} (hpre : dbPrelude inp = .ok pre)
    {i mi : Rat} (hi : pre.iobd.iob = some (.fin i)) (hmi : pre.max_iob = .fin mi) (hle : mi ≤ i) :
    (determineBasal inp).units = none ∧
    ∃ b, pre.basal = .fin b ∧ ∀ r, (determineBasal inp).rate = some (.fin r) → 0 ≤ r ∧ r ≤ b := by
  obtain ⟨p, g, mm, io, ct, meal, h1, -, -, -, -, -, hpp, -, -, -, -, -, hbasal, -, -⟩ := prelude_ok hpre
  have hp := stProfile_ok h1
  have vp := hv.validProfile hp
  obtain ⟨cb, M, hcb, -, hM, -, hMpos⟩ := maxSafeBasal_exists vp
  obtain ⟨b, hb, hb0, hbg, hbM, hbid⟩ := adjustedBasal_bound hv hp hM ((mm.1 + mm.2) / 2)
  have hinc : ∀ x : Rat, (dbPredict inp pre).p.bolus_increment = some (.fin x) → 0 < x := by
    show ∀ x : Rat, pre.p.bolus_increment = some (.fin x) → 0 < x
    rw [hpp]; exact vp.bolus_increment
  have H : IobHyp (dbPredict inp pre) M b :=
    { hM := by simp [hpp, hM], hM0 := Rat.le_of_lt hMpos, hb := by simp [hbasal, hb], hb0, hbgrid := hbg,
      hbM := by simp [hpp, hbM], hbid := by simp [hpp, hbid], hiob := ⟨i, mi, hi, hmi, hle⟩, hinc }
  unfold determineBasal; rw [hpre]; simp only
  refine ⟨?_, b, by rw [hbasal, hb], ?_⟩
  · cases hu : (dbDose (dbPredict inp pre)).units with
    | none => rfl
    | some u =>
      exfalso
      rcases dbDose_units (dbPredict inp pre) u hu with h | hsmb
      · simp at h
      · have hsmb' := hsmb
        obtain ⟨hg, hueq⟩ := hsmb
        unfold smbGivesBolus at hg
        simp only [Bool.and_eq_true] at hg
        obtain ⟨-, hpos⟩ := hg
        rw [← hueq] at hpos
        cases u with
        | nan => simp at hpos
        | fin uv =>
          simp at hpos
          have hroom : (dbPredict inp pre).max_iob - (dbPredict inp pre).iobd.iob.js =
              .fin (Binary64.rd (mi - i)) := by
            show pre.max_iob - pre.iobd.iob.js = _
            rw [hmi, hi]; rfl
          obtain ⟨h0, -⟩ := microbolus_le_room hinc hroom hsmb' hpos
          have := Binary64.rd_nonpos (show mi - i ≤ 0 by grind)
          grind
  · intro r hr
    rcases dbDose_le H r hr with h | h
    · simp at h
    · exact h

/-! ### H6: rounding -/

/-- **H6 (R3), finding F-04.** `round_basal` can push a rate above a limit that is
    not on the pump's increment grid: `maxSafeBasal = 0.83` U/h is issued as
    0.85 U/h. Concretely, `setTempBasal` with a request of 2 U/h and
    `max_basal = 0.83` issues 0.85 U/h (as doubles: the doubles nearest 0.83 and 0.85). -/
theorem rate_can_exceed_maxSafeBasal :
    let p : Profile := { current_basal := some 0.5, max_basal := some 0.83, max_daily_basal := some 1 }
    getMaxSafeBasal p = .fin (Binary64.rd (83/100)) ∧
    (setTempBasal 2 30 p {} none).rate = some (.fin (Binary64.rd (85/100))) := by
  decide +kernel

/-- **H6 (R3), strongest true version.** Rounding never moves a rate up by more
    than half a pump increment, so an issued rate exceeds `maxSafeBasal` by at most
    0.025 U/h (rates below 10 U/h) or 0.05 U/h, plus double rounding of relative
    size 2^-50. -/
theorem roundBasal_overshoot {M : Rat} (m : Option String) (h0 : 0 ≤ M) :
    rbR M m ≤ M + 1/40 + (M + 1) / 2 ^ 50 ∨ (10 ≤ M ∧ rbR M m ≤ M + 1/20 + (M + 1) / 2 ^ 50) := rbR_le m h0

/-- **H6 (R3).** Rounding is monotone: it never reorders two rates. -/
theorem roundBasal_monotone {x y : Rat} (m : Option String) (h : x ≤ y) : rbR x m ≤ rbR y m := rbR_mono m h

end LeanAID.Proofs
