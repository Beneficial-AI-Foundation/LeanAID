# Results over runs

This file ranks the theorems about runs of the loop (`LeanAID/Time/`). A run is a
sequence of time steps. Each step holds CGM readings, user boluses and at most one loop
cycle, and a pump model executes the commands of the cycles. Every theorem below assumes
three things:

- the run is legal (`Legal env r`): each cycle gets its inputs from the run and its result
  is `LeanAID.step` of them,
- the profile is valid at every time (`ValidEnv env`). `validEnv_of_schedule` derives this
  from `ValidSchedule env`, a check on the schedule entries that `decide` can run,
- the autosens data of every cycle is valid (`AutosensOk env r`). `autosensOk_of_clamped`
  derives this from a ratio clamped to `autosens_max`.

Here a cycle increases insulin if it issues a microbolus or a rate above the controller basal
rounded to the pump grid (`Increases`). A command that only shortens a running zero temp
does not count.

Nothing here is fit for dosing insulin.

## Main results

| rank | theorem | statement | other hypotheses |
|---|---|---|---|
| 1 | `p6_delivered_sched` | Let B be the schedule cap and U the microbolus cap that the profile gives, and let k be the number of accepted microboluses in a window of n ms. Then the basal insulin plus the microbolus insulin of the window is at most B · n / 1 h + k · (U + U · 2⁻⁵⁰ + 2⁻⁹⁰). `p6_bolus` bounds k: k = 0 or (k − 1)(60000 · I − 3000 − 2⁻³⁰) < n(1 + 2⁻⁵⁰), with I the SMB interval. This is R20. | `ValidSchedule env`, `SmbMinutesOk env`, initial temp at most B, `smbInterval env.profile = I` |
| 2 | `p4b_fail_safe` | If no command replaces a temp, the pump runs the scheduled basal again at most 30 minutes after a positive temp started and at most 120 minutes after a zero temp started. For the initial temp both bounds count from max(start, t0), where t0 is the first step. A stopped loop is the main case (F-20). | `InitRemaining env t0` |
| 3 | `low_glucose_pump` | Let c be an accepted cycle with `LowCycle`: BG or `minGuardBG` is below the threshold, and oref0's first dose branch is not taken. BG may be low and rising. Then the pump delivers 0 U/h from c until the next temp command or the end of the zero temp, or oref0 requests a zero temp with a NaN duration, the pump rejects it, and the old temp keeps running (F-23). | `InitDouble env` |
| 4 | `p5_gap` | A cycle issues a microbolus only if every earlier nonzero bolus in the run's action log is more than I − 0.05 minutes older, up to double rounding, with I the SMB interval. Boluses in the initial pump history (`env.initHistory`) are not covered. | `smbInterval env.profile = I` |
| 5 | `p1_true_age_head` | A cycle that increases insulin used a reading whose true age is between −5.05 min − 1 ms − δ and 12.05 min + δ. | `DatedReadings`, `RecordedNear δ`, `HeadSpaced` |

## Per-call results added by this branch

These are about one call of `determine_basal`. The run theorems use them.

- `issued_temp_ok` (R4): every finite duration is 0 or between 30 and 120 minutes. If the
  duration is finite and nonzero and the rate is positive, the duration is 30 minutes.
- `rate_double`: every finite rate that `determineBasal` issues is fixed by the model's binary64
  rounding (`rd x = x`).

## Supporting results

- `p6_basal`, `rate_envelope`: let B satisfy `RateCap env B`, bound the schedule
  (`env.sched k ≤ B` for all k) and bound the initial temp (`InvRate B env.init`). Then the
  pump rate is at most B at every time, so the basal insulin of a window of n ms is at most
  B · n / 1 h.
- `p6_delivered`: the R20 bound for such a B, a microbolus cap U with `SmbCap env r U`, and a
  finite SMB interval.
- `p6_bolus`: the number and the total of the accepted microboluses in a window.
- `p4a_expiry`, `temp_bound`: a temp ends at its deadline unless a command replaces it,
  and every stored temp ends at most 120 minutes, or 30 minutes with a positive rate,
  after max(start, t0).
- `low_glucose_no_smb`: a cycle with `LowCycle` adds no bolus to the pump log. It applies
  `low_glucose_suspend` at one cycle.
- `p5_strict`: two accepted microboluses never have the same time.
- `p1_dated`: let every reading have a positive finite recorded date (`DatedReadings r`).
  Then every cycle that increases insulin, at time t, uses a status with a finite date
  d ≥ 0, and −5.05 min ≤ t − ⌊d⌋ < 12.05 min.
- `p1_true_age`: let every recorded date be a double of the model (`DoubleDates r`) and lie
  within δ ms of the true time (`RecordedNear δ r`). Then every cycle that increases insulin
  saw a reading with true age below 12.05 min + δ and a reading with true age above
  −5.05 min − 1 ms − δ. They need not be the same reading.
- `lgs_patched_valid` (`LeanAID/Fixed/LowGlucose.lean`): one call of oref0 with the F-23 fix. The pump accepts its
  low-glucose command.
- `iobTotal_insert_bolus_num`: let the insulin curve be bilinear with finite DIA, and let a
  bolus of u units dated t (`rd u ≠ 0`, |t − 1| ≤ 2⁵³) be inserted before every treatment
  dated after t. If the raw IOB sum x at t before the insertion is finite and |x|, |u| ≤ 2²⁰,
  then the reported IOB at t rises by u up to 1/1000 + 2⁻²⁸ U. This is a step toward R21.

## Model and input facts

`Legal.cycle`, `build_legal`, `validRun_of`, `validEnv_of_schedule`, `rateCap_of_schedule`,
`sched_le_of_schedule`, `autosensOk_of_clamped`, `sortByKey_eq_merge`,
`calcTempTreatments_bolus`, `Legal.logOk`, `Legal.bolusSeen`, `smbTraced_run`,
`getLastGlucose_dated`, `getLastGlucose_date_between`, `getLastGlucose_date_first`,
`round3_accounting`, `determineBasalPatched_eq`, `zeroRun_cycle_kernel`. The results above
use these. They are not safety statements.

## Findings checked on runs

`docs/FINDINGS.md` has the details.

- F-20: `zeroRun_pump`. A stopped loop leaves a zero temp running for 120 minutes.
- F-21: `i2_fails`. The IOB of microboluses alone can exceed `max_iob`.
- F-22: `basalLookup_last_zero`. A schedule whose last entry is 0 U/h gives no basal.
- F-23: `f23Run_covered`, `f23Run_second`. `low_glucose_pump` applies to a legal run in which
  BG is low and rising, the NaN-duration zero temp is rejected, and a 2 U/h temp keeps
  running. With carbs the same run gets a zero temp (`f23RunC_checks`).
