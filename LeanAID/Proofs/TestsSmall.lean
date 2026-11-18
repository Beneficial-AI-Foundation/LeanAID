/-
  LeanAID.Proofs.TestsSmall — class A tests of round_basal (DB-01..05),
  set-temp-basal.test.js, basal.test.js and iob.test.js as theorems (M6).
  Test values are proved by kernel evaluation (no `native_decide`).
-/
import LeanAID.Proofs.Lifted
import LeanAID.Conformance.Data.SmallData

namespace LeanAID.Proofs.TestsSmall

open LeanAID LeanAID.Proofs LeanAID.Conformance JsNum

/-- **DB-01..05.** All 10 `round_basal` test calls give oref0's expected values. -/
theorem roundBasal_tests : SmallData.roundBasal.all RBCase.ok = true := by decide +kernel

/-- DB-01 as an instance of `roundBasal_nearest`: 0.025 without a pump model is
    rounded on the 0.05 grid (scale 20). -/
theorem DB_01_general : basalScale (1/40) none = 20 ∧
    roundBasal (.fin (1/40)) none = .fin (rts (1/40) 20) := by
  refine ⟨by decide +kernel, ?_⟩
  have := (roundBasal_nearest (x := 1/40) none (by decide +kernel)).1
  rw [this, show basalScale (1/40) none = 20 by decide +kernel]

/-- DB-03 as an instance: model "554" uses the 0.025 grid (scale 40). -/
theorem DB_03_general : lowestRateScale (some "554") = 40 :=
  lowestRateScale_x23 "554" (Or.inr (by decide +kernel))

/-- **STB-01..12.** All 13 `setTempBasal` test calls give oref0's rate, duration
    and reason. -/
theorem setTempBasal_tests : SmallData.setTempBasal.all STBCase.ok = true := by decide +kernel

/-- STB-05..10 as instances of `setTempBasal_rate_bound` (rates within
    `[0, round_basal(maxSafeBasal)]`) and STB-01..03 of `setTempBasal_no_temp`. -/
theorem STB_general (rate dur : JsNum) (p : Profile) (rT : Result) (hskip : p.skip_neutral_temps ≠ some true) :
    (setTempBasal rate dur p rT none).rate = some (suggestedRate rate p) :=
  (setTempBasal_no_temp rate dur p rT hskip).1

/-- **BAS-01.** (BAS-02 uses `basalLookup`, whose sort the kernel cannot evaluate;
    it is checked in `LeanAID/Conformance/Checks.lean`.) -/
theorem maxDailyBasal_tests : SmallData.maxDailyBasal.all MaxDailyCase.ok = true := by decide +kernel

/-- **IOB-01 (general).** A 2 U bolus (bilinear curve, DIA 3 h) is fully on board
    when given and contributes nothing after DIA. -/
theorem IOB_01_general :
    (Iob.iobCalcBilinear (.fin 2) 0 (.fin 3)).iobContrib = .fin 2 ∧
    (Iob.iobCalcBilinear (.fin 2) (.fin 180) (.fin 3)).iobContrib = .fin 0 :=
  ⟨by rw [bilinear_at_zero 2 3 (by decide)]; decide +kernel,
   bilinear_after_dia' 2 180 3 (by decide) (by decide +kernel)⟩

/-- **IOB-08 (general).** The test's profile (rapid-acting curve, DIA 3 h) gets a DIA
    of 5 h, as every exponential curve does. -/
theorem IOB_08_general :
    (Iob.curveSetup { dia := some 3, curve := some "rapid-acting" }).2.1 = .fin 5 := by decide +kernel

end LeanAID.Proofs.TestsSmall
