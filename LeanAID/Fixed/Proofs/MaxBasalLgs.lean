import LeanAID.Fixed.Proofs.Combined
import LeanAID.Fixed.Proofs.MaxBasal

/-!
# F-12: lemmas for low-glucose suspend under the trigger

oref0's low-glucose theorems (`LeanAID.Proofs.lgs_setup`, `lgs_detail`) take `ValidInput`.
Under the F-12 trigger the corrected version runs oref0 on `inputF12 inp p`, whose profile
has `maxSafeBasal = current_basal`; that input need not satisfy `ValidInput` (V5 and V9 ask
`current_basal · autosens ≤ maxSafeBasal`, false for an autosens ratio above 1). The proofs
use only that `current_basal` is positive and `maxSafeBasal` a number `≥ 0`, so this file
restates them with those hypotheses (`lgs_setup_of`), and adds:

* `keepRunning_small`, `setTempBasal_zero_small`: when oref0 keeps a running temp instead of
  a requested zero temp, the running rate is below `2^-1074`, so below every positive double
  (`postF12` then does not cancel it);
* `stGlucoseF11_inputF12`, `postF12_err`, `postF12_keep`: the steps of the corrected version
  on the capped input.
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Proofs LeanAID.Time JsNum
open LeanAID.Binary64 (rd pow2)

/-- `LeanAID.Proofs.lgs_setup` with the profile facts as hypotheses instead of `ValidInput`. -/
theorem lgs_setup_of {inp : DBInputs} {pre : Pre} (hpre : dbPrelude inp = .ok pre)
    {q : Profile} (hq : inp.profile = some q) {M cb : Rat} (hM : getMaxSafeBasal q = .fin M)
    (hcb : q.current_basal = some (.fin cb))
    (hlow : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true)
    (hfirst : doseFirstBranch pre = false) :
    getMaxSafeBasal (dbPredict inp pre).p = .fin M ∧
      (dbPredict inp pre).p.current_basal = some (.fin cb) ∧
      inp.currenttemp = some (dbPredict inp pre).ct ∧
      ((dbPredict inp pre).bg <ʲ (dbPredict inp pre).threshold &&
        (dbPredict inp pre).iobd.iob.js <ʲ -(dbPredict inp pre).p.current_basal.js * 20 / 60 &&
        (dbPredict inp pre).minDelta >ʲ 0 && (dbPredict inp pre).minDelta >ʲ (dbPredict inp pre).expectedDelta) = false ∧
      ((dbPredict inp pre).bg <ʲ (dbPredict inp pre).threshold ||
        (dbPredict inp pre).minGuardBG <ʲ (dbPredict inp pre).threshold) = true := by
  obtain ⟨p, g, mm, io, ct, meal, h1, -, -, -, h5, -, hpp, hct, -, -, -, -, -, -, -⟩ := prelude_ok hpre
  have hp := stProfile_ok h1
  rw [hq] at hp; cases hp
  have hpc : (dbPredict inp pre).p = q := hpp
  refine ⟨by rw [hpc]; exact hM, by rw [hpc]; exact hcb, ?_, ?_, ?_⟩
  · rw [stPumpHistory_ok h5, ← hct]; rfl
  · exact hfirst
  · show (pre.bg <ʲ pre.threshold || (dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true
    rcases hlow with h | h <;> simp [h]

/-- When `keepRunning` keeps a running temp for a zero request, its rate is a number below
    `2^-1074` (in double arithmetic, `rate · 0.8` rounds to at most 0). -/
theorem keepRunning_small {dur : JsNum} {ct : Option CurrentTemp} {d r : JsNum}
    (h : keepRunning (.fin 0) dur ct = some (d, r)) :
    ∃ c x, ct = some c ∧ c.rate = some (.fin x) ∧ x < pow2 (-1074) := by
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
        simp only [Bool.and_eq_true, JsNum.ofSci_eq, JsNum.fin_mul, JsNum.le_fin, JsNum.ge_fin,
          decide_eq_true_eq] at hc
        obtain ⟨⟨-, hb⟩, -⟩ := hc
        have e2 : (OfScientific.ofScientific 8 true 1 : Rat) = 4/5 := by decide +kernel
        rw [e2] at hb
        have c1 : (1/2 : Rat) < Binary64.rd (4/5) := by decide +kernel
        have pp := Binary64.pow2_pos (-1075)
        have p2 : Binary64.pow2 (-1074) = Binary64.pow2 (-1075) * 2 := by
          rw [← Binary64.pow2_succ]; rfl
        by_cases hx : x < Binary64.pow2 (-1074)
        · exact hx
        · exfalso
          have m := Rat.mul_le_mul_of_nonneg_right (show Binary64.pow2 (-1074) ≤ x by grind)
            (Rat.le_of_lt (show (0 : Rat) < Binary64.rd (4/5) by grind))
          have m2 := Rat.mul_lt_mul_of_pos_left c1 (show 0 < Binary64.pow2 (-1074) by grind)
          have := Binary64.rd_pos_of_gt (y := x * Binary64.rd (4/5)) (by grind)
          grind
    · cases h
  · cases h

/-- If `setTempBasal(0, …)` issues no rate (with `rT` issuing none), it kept a running temp
    whose rate is below `2^-1074`. -/
theorem setTempBasal_zero_small {D : JsNum} {p : Profile} {rT : Result} {ct : Option CurrentTemp} {M cb : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) (hcb : p.current_basal = some (.fin cb)) (hcb0 : 0 < cb)
    (h : (setTempBasal 0 D p rT ct).rate = none) :
    ∃ c x, ct = some c ∧ c.rate = some (.fin x) ∧ x < pow2 (-1074) := by
  have hs := suggestedRate_zero hM hM0
  unfold suggestedRate at hs
  simp only [setTempBasal] at h
  rw [hs] at h
  cases hk : keepRunning (.fin 0) D ct with
  | some v =>
    obtain ⟨d, r⟩ := v
    exact keepRunning_small hk
  | none =>
    rw [hk] at h
    simp only at h
    have : (JsNum.fin 0 =ʲ p.current_basal.js) = false := by
      rw [hcb]; simp; grind
    rw [this] at h
    simp at h

/-- A positive double is at least `2^-1074`. -/
theorem pow2_le_of_double {c : Rat} (hd : rd c = c) (h0 : 0 < c) : pow2 (-1074) ≤ c := by
  by_cases h : c < pow2 (-1074)
  · exfalso
    have := Binary64.double_small hd (by have := Binary64.pow2_pos (-1074); grind) h
    grind
  · grind

/-- `stGlucoseF11` does not read the profile when it succeeds. -/
theorem stGlucoseF11_inputF12 {inp : DBInputs} {p q : Profile} {g : GluVals} (hg : stGlucoseF11 inp p = .ok g) :
    stGlucoseF11 (inputF12 inp q) (capProfile q) = .ok g := by
  unfold stGlucoseF11 at hg ⊢
  simp only [inputF12]
  cases hgs : inp.glucose_status with
  | none => rw [hgs] at hg; cases hg
  | some gs =>
    rw [hgs] at hg
    simp only at hg ⊢
    split at hg
    · cases hg
    · rename_i hc; simp only [hc, Bool.false_eq_true, ite_false]; exact hg

theorem stProfile_inputF12 {inp : DBInputs} {p : Profile} (hcb : p.current_basal.isSome = true) :
    stProfile (inputF12 inp p) = .ok (capProfile p) := by
  have hne : (capProfile p).current_basal.isNone = false := by
    simp only [capProfile]; cases h : p.current_basal <;> simp_all
  simp [stProfile, inputF12, hne]

/-- `postF12` returns an error result unchanged. -/
theorem postF12_err {inp : DBInputs} {p : Profile} {U : Result} (h : U.shape = .error) : postF12 inp p U = U := by
  unfold postF12; simp [h]

/-- `postF12` keeps "no rate" when the running temp is not above `current_basal`. -/
theorem postF12_keep {inp : DBInputs} {p : Profile} {U : Result} (hr : U.rate = none)
    (hct : ∀ ct, inp.currenttemp = some ct → (ct.rate.js >ʲ p.current_basal.js) = false) :
    (postF12 inp p U).rate = none ∧ (postF12 inp p U).duration = U.duration := by
  unfold postF12
  split
  · exact ⟨hr, rfl⟩
  · dsimp only
    cases hR : U.reason <;> cases hc : inp.currenttemp <;> simp_all

/-- The units of the fixes of F-11 and F-23 without `microBolusAllowed`. -/
theorem uncapped_units_noSmb {inp : DBInputs} (h : inp.microBolusAllowed = false)
    (hM : ∀ p, inp.profile = some p → ∃ M, getMaxSafeBasal p = .fin M ∧ 0 ≤ M) :
    (determineBasalUncapped inp).units = none := by
  cases hs : stProfile inp with
  | error r =>
    have : determineBasalUncapped inp = determineBasal inp := by
      unfold determineBasalUncapped; rw [hs]; exact (determineBasal_of_stProfile_error hs).symm
    rw [this]; exact determineBasal_units_noSmb h hM
  | ok p =>
    rw [uncapped_of_st hs]
    cases hpre : dbPreludeF11 inp with
    | error r =>
      simp only
      rcases dbPreludeF11_error hpre with h' | ⟨p', gs, -, -, hr⟩
      · exact (prelude_error h' hM).1
      · rw [hr]
        unfold cgmResultF11
        split
        · rfl
        · dsimp only; split
          · rfl
          · split <;> rfl
    | ok pre =>
      simp only
      rcases dbDosePatched_cases (dbPredict inp pre) with h' | ⟨h1, h2⟩
      · rw [h', dbDose_units_noSmb _ (by rw [dbPredict_mba]; exact h)]; exact dbPredict_rT_units _ _
      · unfold dbDosePatched
        simp only [h1, h2, Bool.false_eq_true, ite_false, ite_true]
        rw [setTempBasal_units]
        simp [Result.addReason]

/-- The low-glucose branch of the corrected dose phase, for any context whose profile has
    `maxSafeBasal = M ≥ 0` and `current_basal = cb > 0`: no new microbolus, and rate 0 for a
    whole number of minutes in `[30, 120]`, or no rate while a temp with more than 20
    minutes left and a rate below `2^-1074` (0, if it is a double) keeps running. -/
theorem dbDosePatched_lgs {C : Ctx} {M cb : Rat} (hM : getMaxSafeBasal C.p = .fin M) (hM0 : 0 ≤ M)
    (hcb : C.p.current_basal = some (.fin cb)) (hcb0 : 0 < cb)
    (hexc : (C.bg <ʲ C.threshold && C.iobd.iob.js <ʲ -C.p.current_basal.js * 20 / 60 &&
      C.minDelta >ʲ 0 && C.minDelta >ʲ C.expectedDelta) = false)
    (hlow : (C.bg <ʲ C.threshold || C.minGuardBG <ʲ C.threshold) = true) (hrT : C.rT.rate = none) :
    (dbDosePatched C).units = C.rT.units ∧
    (((dbDosePatched C).rate = some 0 ∧
        ∃ q : Int, (dbDosePatched C).duration = some (.fin q) ∧ 30 ≤ q ∧ q ≤ 120) ∨
     ((dbDosePatched C).rate = none ∧ (dbDosePatched C).duration = C.rT.duration ∧
       ∃ c ctDur x, some C.ct = some c ∧ c.duration = some (.fin ctDur) ∧ 20 < ctDur ∧
         c.rate = some (.fin x) ∧ (rd x = x → x = 0) ∧ x < pow2 (-1074))) := by
  unfold dbDosePatched
  simp only [hexc, hlow, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨q, hq, hq30, hq120⟩ := patchDur_lgsDur C
  rw [hq]
  obtain ⟨hu, hr⟩ := setTempBasal_zero_lgs (Or.inr ⟨q, rfl, hq30, hq120⟩)
    (rT := C.rT.addReason ("minGuardBG " ++ convertBgS C.minGuardBG C.p ++ "<" ++ convertBgS C.threshold C.p))
    (ct := some C.ct) hM hM0 hcb hcb0
  refine ⟨by rw [hu]; rfl, ?_⟩
  rcases hr with ⟨hr, hd⟩ | ⟨hr, hd, c, ctDur, x, hc, hcd, h20, hcr, hx⟩
  · exact Or.inl ⟨hr, q, hd, hq30, hq120⟩
  · right
    have hnone : (setTempBasal 0 (.fin q) C.p (C.rT.addReason ("minGuardBG " ++ convertBgS C.minGuardBG C.p ++ "<" ++
        convertBgS C.threshold C.p)) (some C.ct)).rate = none := by rw [hr]; exact hrT
    obtain ⟨c', x', hc', hcr', hx'⟩ := setTempBasal_zero_small hM hM0 hcb hcb0 hnone
    rw [hc] at hc'
    have hcc : c = c' := Option.some.inj hc'
    subst hcc
    rw [hcr] at hcr'
    have hxx : x = x' := by injection hcr' with h; injection h
    subst hxx
    exact ⟨by rw [hr]; exact hrT, by rw [hd]; rfl, c, ctDur, x, hc, hcd, h20, hcr, hx, hx'⟩

end LeanAID.Fixed
