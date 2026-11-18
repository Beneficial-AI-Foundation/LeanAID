/-
  LeanAID.Conformance.Checks — the transcription agrees with oref0 on every call
  that oref0's own test suite makes to the in-scope functions.

  Each case holds the exact inputs a test passed and oref0's output (captured by
  `scripts/capture/run.sh` under Node, `TZ=UTC`, clock frozen at
  2026-11-18T12:00:00Z). The checks are evaluated by `native_decide`, which the
  project rules allow in this directory only: these theorems trust the Lean
  compiler (axiom `Lean.ofReduceBool`), unlike the proofs in `LeanAID/Proofs`.

  Agreement is exact (same JSON output, same numbers) except for the two IOB
  calls listed in `iob_ties`, where oref0's double arithmetic and our exact
  arithmetic round an exact tie in opposite directions.
-/
import LeanAID.Conformance.Data.DetermineBasalData
import LeanAID.Conformance.Data.IobData
import LeanAID.Conformance.Data.SmallData

namespace LeanAID.Conformance

/-- All 42 `determine_basal` calls of `determine-basal.test.js`: identical JSON output. -/
theorem determineBasal_conforms : DetermineBasalData.all.all DBCase.ok = true := by native_decide

/-- The 23 disabled determine-basal tests, run on their inputs: identical output. -/
theorem determineBasal_disabled_conforms : DetermineBasalData.disabled.all DBCase.ok = true := by native_decide

/-- The 10 `round_basal` calls of `determine-basal.test.js`. -/
theorem roundBasal_conforms : SmallData.roundBasal.all RBCase.ok = true := by native_decide

/-- The 13 `setTempBasal` calls of `set-temp-basal.test.js`: same rate, duration and reason. -/
theorem setTempBasal_conforms : SmallData.setTempBasal.all STBCase.ok = true := by native_decide

/-- `basal.test.js`: `basalLookup` and `maxDailyBasal`. -/
theorem basal_conforms :
    SmallData.basalLookup.all BasalLookupCase.ok = true ∧ SmallData.maxDailyBasal.all MaxDailyCase.ok = true := by
  native_decide

/-- The 5 `getLastGlucose` calls of `get-last-glucose.test.js`: identical JSON. -/
theorem getLastGlucose_conforms : SmallData.getLastGlucose.all GLGCase.ok = true := by native_decide

/-- `cobhistory.test.js`. -/
theorem cobHistory_conforms : SmallData.cobHistory.all COBHCase.ok = true := by native_decide

/-- All 51 `lib/iob` calls of `iob.test.js` agree exactly on every element of the
    48-element IOB array (and on lastBolusTime and lastTemp). (With exact rational
    arithmetic, before the binary64 model, 2 differed at a rounding tie: F-09.) -/
theorem iob_exact : (IobData.all.filter IobCase.ok).length = 51 := by native_decide

/-- All 51 agree up to rounding ties (implied by `iob_exact`; kept as a check of the
    weaker comparison). -/
theorem iob_ties : IobData.all.all IobCase.okUpToTies = true := by native_decide

end LeanAID.Conformance

/-! `Exp.taylor` (integer form) against `Exp.taylorHorner` (rational Horner form) on the
    arguments the exponential insulin curves use: x = -m/τ for every whole minute
    m ≤ 600 and the peak times 55 and 75 min with DIA 5 h, halved as `expNonpos` does. -/
open LeanAID in
theorem taylor_eq_horner_samples :
    ((List.range 601).all fun m => [55, 75].all fun peak =>
      let end_ : Rat := 300
      let tau : Rat := Binary64.rd (peak * (1 - peak / end_) / (1 - 2 * peak / end_))
      let x : Rat := Binary64.rd (-(m : Rat) / tau)
      let y := x / (2 : Rat) ^ Exp.halvings x
      Exp.taylor y 30 == Exp.taylorHorner y 30) = true := by native_decide
