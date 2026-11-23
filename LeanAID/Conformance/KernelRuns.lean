import LeanAID.Conformance.TimeRuns

/-!
# Concrete runs checked by the kernel

The checks here use `decide +kernel`, so they trust no compiled code, unlike the
`native_decide` checks of `LeanAID.Conformance.TimeRuns`, which trust `Lean.ofReduceBool`.
`TimeRuns` also has three `decide +kernel` checks, `zeroRun_pump`, `zeroRun_temp` and
`keepRun_low`. They stay next to their runs, and `zeroRun_zero` there builds on
`zeroRun_temp`.
The kernel can evaluate `Iob.generate` because `calcTempTreatments` is split into stages
(`docs/DESIGN.md`).

- `zeroRun_cycle_kernel`: the one cycle of `zeroRun`, `LeanAID.step` on inputs built by
  `Iob.generate`, issues a zero temp of 120 minutes and no bolus, and the pump accepts it.
- `same_timestamp_both_kept_kernel`: `calcTempTreatments` keeps both boluses of
  `twoBoluses`, which have the same timestamp.
- `twoBoluses_lastBolusTime`: the `lastBolusTime` of `iobOut` on `twoBoluses` is the time
  of the two boluses, `t0 − 10 min`.

The three `i2Run` checks of `TimeRuns`, over 32 cycles, fail under `decide +kernel` and use
`native_decide`.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time.Runs

open LeanAID LeanAID.Time LeanAID.Iob

theorem zeroRun_cycle_kernel :
    (results env zeroRun).map (fun (t, r, o) => (t, r.rate, r.duration, r.units, o)) =
      [(t0 + 10 * mn, some 0, some 120, none, .accepted)] := by
  decide +kernel

theorem same_timestamp_both_kept_kernel :
    ((calcTempTreatments { history := history env twoBoluses, profile := prof, clockMs := t0 } none).treatments.filter
      (fun t => t.insulin.isSome)).map (fun t => (t.insulin, t.startedAt)) =
      [(some (.fin (1/2)), some (t0 - 10 * mn)), (some 1, some (t0 - 10 * mn))] := by
  decide +kernel

theorem twoBoluses_lastBolusTime : (iobOut env twoBoluses t0 none).lastBolusTime = .fin (t0 - 10 * mn) := by
  decide +kernel

end LeanAID.Time.Runs
