# The corrected version

**Research artifact. Not a medical device. Nothing here may be used to dose insulin.**

`LeanAID/Core` is the faithful translation of oref0 0.7.1, identical to oref0 on the
differential tests, and it is not changed (`git diff 43fcc38 -- LeanAID/Core` is empty).
Next to it, `LeanAID/Fixed` is a corrected version that fixes five findings: F-04, F-11,
F-12, F-23 and F-24 (`docs/FINDINGS.md`). Each fix is the smallest change that removes the
defect, in its own file, and calls the `Core` functions for everything it does not fix.
`scripts/fixes/` has the same fixes as patches to oref0's JavaScript.

For each fix Lean proves:

1. **a trigger**: a decidable predicate saying when the fix changes anything, stated on the
   input or, where that is not possible, with oref0's (`Core`) functions;
2. **nothing else changed**: without the trigger, the corrected result is oref0's, for every
   input, with no other hypothesis;
3. **the fix works**: with the trigger, the corrected result is safe.

For the combined version (`determineBasalFixed`, `generateFixed`) Lean proves that without
any trigger it is oref0, and restates the safety theorems of `LeanAID/Proofs` without the
exceptions they have today. All theorems below are checked by `lake build` with no `sorry`
and use only the axioms `propext`, `Classical.choice`, `Quot.sound` (`scripts/check.sh`
prints them; they are listed in `scripts/headline.txt`). `LeanAID/Fixed` follows the rules of
`LeanAID/Core`: no `sorry`, `partial`, `unsafe`, `@[extern]`, `implemented_by`, `Float`,
`native_decide`, axioms or Mathlib (`scripts/check.sh` checks it).

Section [What is not proved as intended](#what-is-not-proved-as-intended) lists the gaps.

## Using it

```bash
.lake/build/bin/aid-lean determine-basal … --fixed     # determineBasalFixed
.lake/build/bin/aid-lean batch cases.jsonl --fixed      # the difftest batch, corrected
.lake/build/bin/aid-lean batch cases.jsonl --fixed-triggers   # {"triggers":[…],"result":…}
.lake/build/bin/aid-lean iob-batch cases.jsonl --fixed  # generateFixed; adds "f24": <trigger>
.lake/build/bin/aid-lean serve --fixed                  # the virtual-patient controller
bash scripts/fixes/apply.sh          # scripts/fixes/out/oref0-fixed: a patched copy of oref0
```

Without `--fixed`, nothing changes.

## F-04: a rate rounded above `maxSafeBasal`

**oref0** (`lib/basal-set-temp.js:21-30`): `setTempBasal` caps the rate at `maxSafeBasal`
and then rounds it to the nearest pump step, so with `maxSafeBasal` 0.83 it issues 0.85 U/h.
The CGM-error branch of `determine_basal` (lines 198-206) issues `round_basal(current_basal)`
without a cap, which is 0.85 U/h when `current_basal = max_basal = 0.83`.

**Fix** (`LeanAID/Fixed/Rounding.lean`, `scripts/fixes/F-04.patch`). At the exit of
`determine_basal`: if the issued rate is above `maxSafeBasal` (and `maxSafeBasal ≥ 0`), issue
`round_basal.down(maxSafeBasal)` instead, the largest rate on the pump's grid that is at most
`maxSafeBasal`, and append to the reason "…U/hr is above maxSafeBasal …: setting …U/hr".
`round_basal.down` (`roundBasalDown`) uses `round_basal`'s scale and corrects
`Math.floor(m·s)` when the double product was rounded up to an integer. Every other result
is unchanged. The fix acts on the result, not inside `setTempBasal`, so that it changes
exactly the results that issue a rate above `maxSafeBasal`, wherever the rate comes from; a
fix inside `setTempBasal` (as in `private/docs/upstream/oref0/F-04.patch`) would miss the
CGM-error branch and would also change the "~ req" comparison with a running temp, which
issues nothing. The upstream draft's `Math.floor(x + 1e-9)` can also round up; it was not
reused.

**Trigger** (`TriggerF04`, with oref0's functions): oref0's `determine_basal` issues a rate
above oref0's `getMaxSafeBasal` of the profile (`triggerF04_iff`).

**Theorems** (`LeanAID/Fixed/Proofs/Rounding.lean`)
- `determineBasalF04_eq`: without the trigger, the corrected result is oref0's.
- `f04_fixed`: with the trigger, if `maxSafeBasal = M` is a double with `0 ≤ M ≤ 2^30`, the
  corrected rate `r` satisfies `0 ≤ r ≤ M`, and duration and microbolus are oref0's.
- `roundBasalDown_le`: `round_basal.down(M)` is between 0 and `M` (same conditions on `M`).
- `f04_example`: `current_basal` 0.5, `max_basal` 0.83, BG 300 rising: oref0 issues 0.85,
  the corrected version 0.8 U/h.

## F-11: an undated glucose reading

**oref0** (`lib/determine-basal/determine-basal.js:149-150, 187, 198`): a reading without a
date has `minAgo = NaN`; `minAgo > 12 || minAgo < -5` is false, so it is never stale, and
oref0 issues its maximum rate on a reading of any age.

**Fix** (`LeanAID/Fixed/Undated.lean`, `scripts/fixes/F-11.patch`). Lines 187 and 198 test
`!(minAgo <= 12 && minAgo >= -5)`. For a numeric age this is the same condition; a NaN age
takes oref0's own stale-data path (replace a high temp by the scheduled basal, shorten a
long zero temp, or do nothing), with oref0's reason "…BG data is too old…".

**Trigger** (`TriggerF11`, on the input): the glucose status has no date or a date that is
not a number. In `aid-lean`, whose glucose status comes from the newest CGM entry
(`getLastGlucose`), this is an entry without `date`, `display_time` or `dateString`.

**Theorems** (`LeanAID/Fixed/Proofs/Undated.lean`)
- `determineBasalF11_eq`: with a numeric date, the corrected result is oref0's.
- `f11_fixed`: with the trigger (and a profile with `current_basal`), no microbolus, and the
  rate is `round_basal(current_basal)` replacing a running temp above it, or 0, or none while
  the running temp is not above it.
- `f11_example`: the F-11 input of FINDINGS (BG 250 rising, no date): oref0 3.5 U/h, the
  corrected version no rate.

## F-12: a missing maximum basal

**oref0** (`lib/basal-set-temp.js:11-17`): `maxSafeBasal = min(max_basal, 3·max_daily_basal,
4·current_basal)` is NaN when `max_basal` or `max_daily_basal` is missing or not a number,
and no cap applies (5.9 U/h for a scheduled 0.9 U/h). `determine_basal` checks only
`current_basal` (lines 138-143).

**Fix, second version** (`LeanAID/Fixed/MaxBasal.lean`, `scripts/fixes/F-12.patch`, commit
"Fixed: F-12 caps at the scheduled basal instead of refusing"). When the trigger holds,
oref0's normal decision runs with these changes and no others:

1. **The cap is the scheduled basal.** oref0 runs on `capProfile p`, a copy of the profile
   whose `max_basal` and `max_daily_basal` are `current_basal` and whose two safety
   multipliers are 1, so `getMaxSafeBasal` returns `min(cb, 1·cb, 1·cb) = cb`
   (`maxSafe_capProfile`). `getMaxSafeBasal` is the only reader of these four fields in
   `determine_basal` and `setTempBasal` (checked in the JavaScript and in `LeanAID/Core`), so
   oref0 uses `current_basal` everywhere it used `maxSafeBasal`: the clamp in `setTempBasal`
   and the cap of the high-temp branch (line 1162). The F-04 step with the same profile then
   replaces a rate rounded above `current_basal` (0.83 → 0.85) by `round_basal.down`; so the
   F-12 fix relies on the F-04 fix for "no rate above `current_basal`", and Lean's
   `determineBasalF12` includes that step. `F-12.patch` alone (without `F-04.patch`) can
   issue `round_basal(current_basal)`, up to half a pump step above.
2. **No microbolus**: oref0 runs with `microBolusAllowed = false`, its own path when the pump
   loop does not allow SMB (lines 60-62, `enable_smb`). This also skips the check of lines
   380-383, which runs only with `microBolusAllowed`.
3. **A running temp above `current_basal` is not left running.** Where oref0 issues no rate
   and keeps the running temp (the "~ req", "~< req" and ">~ req" comparisons, the 20 %
   window of `setTempBasal`, and the CGM-error branch for a temp between `current_basal`
   and its rounding), and that temp's rate is above `current_basal`, the result cancels it
   (rate 0, duration 0, so the pump runs its schedule), as oref0 cancels at lines 380-392.
   This is a step after oref0 (`postF12`), not a change inside it: whether oref0 issued no
   rate and the running temp is above `current_basal` is visible on the result. A
   replacement by the requested rate was not chosen: the request is not part of the result,
   and recomputing it would mean a second change inside the dose phase.
4. **The reason** ends with "; maxSafeBasal NaN is not a positive number (max_basal or
   max_daily_basal missing or not a number): rate capped at current basal 0.9U/hr, no SMB",
   and, for 3, "; canceling temp basal of 2 above current basal 0.9".

Everything else is oref0's: the predictions, the low-glucose suspend, the CGM-error and
stale-data paths, the error results (returned unchanged), and the JSON shape (a cancel adds
`deliverAt` and `temp` only where they are missing, then `duration` and `rate`, in oref0's
key order). In JavaScript the fix is a wrapper appended after `module.exports` that calls
the previous `determine_basal` with the capped copy of the profile; it wraps the F-04 wrapper
when both patches are applied.

**Fix, first version, replaced** (commit `eccda9f`, still in git history). Right after the
`current_basal` check, it returned without a dosing decision: no microbolus, a running temp
above `current_basal` cancelled, a long zero temp shortened, otherwise nothing. It removed
the rates above the limit (with the F-12 fault: R1 1,064 → 0 violations, time below 54 mg/dL 4.80 % →
2.48 %), but it never set a zero temp at low glucose: 962 R8 violations against oref0's 1,
and 3 of 30 virtual patients spent more time below 54 mg/dL than with oref0 (see "Virtual
patients" below). A fix that removes one hazard and adds another was replaced.

**Trigger** (`TriggerF12`, on the input, unchanged): the profile has `current_basal` and its
`maxSafeBasal` is not a positive number. `triggerF12_of_missing`: a missing or non-numeric
`max_basal` or `max_daily_basal` triggers it. It also holds when one of the three limits is
zero or negative; then the cap is also `current_basal`.

**Theorems** (`LeanAID/Fixed/Proofs/MaxBasal.lean`, `LeanAID/Fixed/Proofs/MaxBasalLgs.lean`)
- `determineBasalF12_eq` (statement unchanged): with a positive `maxSafeBasal` (or without a
  profile or `current_basal`), the corrected result is oref0's.
- `f12_fixed` (restated): with the trigger and `current_basal` a double `cb` in `[0, 2^30]`:
  no microbolus; no finite rate above `cb`; when no rate is issued and the result is not an
  error, the running temp is not above `current_basal`. (First version: "no rate other than
  0", with no hypothesis; error results were impossible there, because the refusal came
  first.)
- `maxSafe_capProfile`: the capped profile's `maxSafeBasal` is `current_basal`.
- `determineBasal_units_noSmb`, `dbDose_units_noSmb`: with `microBolusAllowed = false`, oref0
  sets no microbolus.
- `postF12_rate`, `postF12_none`, `postF12_keep`: the last step only turns "no rate" into a
  cancel, and only when the running temp is above `current_basal`.
- `f12_example`: the input of `missing_max_basal_no_clamp` (BG 300, rising): oref0 5.9 U/h,
  the corrected version 0.9 U/h for 30 minutes (reason checked); with a 2 U/h temp running,
  a cancel (oref0, capped, would keep it: "temp 2 >~ req 0.9U/hr").
- `f12_lgs_example`: the same profile at BG 60, falling: oref0 and the corrected version set
  a zero temp for 30 minutes (the first version issued nothing).
- `low_glucose_suspend_fixed` now covers the trigger (see the combined version).
- `f12_rate_le` (first version: "every rate is 0") was removed; its content is in `f12_fixed`.

## F-23: low-glucose suspend with a NaN duration

**oref0** (`determine-basal.js:912-920`): with `minGuardBG` NaN the low-glucose zero temp has
a NaN duration, which a pump rejects, so a running temp continues at low glucose.

**Fix** (`LeanAID/Fixed/LowGlucose.lean`, moved from `LeanAID/Patched`, and
`scripts/fixes/F-23.patch`): after line 919, a NaN `durationReq` becomes 30 minutes. The root
cause (`fractionCarbsLeft`, line 709) is not changed, so the predictions stay oref0's.

**Trigger** (`TriggerF23`, with oref0's functions): the prelude succeeds, oref0 takes the
low-glucose branch of lines 912-920, and its duration `lgsDur` is NaN.

**Theorems** (`LeanAID/Fixed/LowGlucose.lean`, `LeanAID/Fixed/Proofs/LowGlucose.lean`)
- `determineBasalF23_eq`: without the trigger, the corrected result is oref0's.
  (`determineBasalPatched_eq`, kept: the result is oref0's unless `lgsDur` is NaN.)
- `f23_fixed`: for valid input with the trigger, the pump model accepts the command
  (`validate`), no microbolus, and rate 0 for a whole number of minutes in [30, 120] or a
  running zero temp left in place. (`lgs_patched`, `lgs_patched_valid`, kept.)
- `f23_trigger_example`: the trigger holds on `f23Input`.

## F-24: `splitTimespan` drops pieces of a temp

**oref0** (`lib/iob/history.js:50-80`): the flag `splitFound` is shared by all pieces of one
pass, so once a piece splits, every later piece of the pass that does not split is dropped
with its insulin.

**Fix** (`LeanAID/Fixed/SplitTimespan.lean`, `scripts/fixes/F-24.patch`): each piece has its
own flag (`thisSplit`); `splitFound` still decides whether another pass is needed. This is
the fix of `sim/q6fix.js` (`splitPassF24_eq_splitPassFixed`, `splitTimespanF24_eq`).
`generateF24` is `LeanAID.Iob.generate` with the fixed split; the IOB pipeline is written
once with the split as a parameter, and with oref0's split it is the transcription
(`generateW_splitTimespan`).

**Trigger** (`TriggerF24`, with oref0's functions): in one of the two calls of
`calcTempTreatments` by `generate`, oref0's `splitTimespan` drops a piece of a temp it
splits (`q6Event`: some pass has a piece that does not split after one that does).

**Theorems** (`LeanAID/Fixed/Proofs/SplitTimespan.lean`)
- `generateF24_eq`: without the trigger, the corrected IOB is oref0's.
- `splitTimespanF24_tiles`: the pieces of the fixed split tile the temp: every piece of
  every pass is kept or replaced by the two parts of its split. `splitOne_parts`: the
  first part starts where the piece starts and lasts `d₁`, the second starts `d₁` minutes
  later and lasts `d − d₁`; both keep the rate.
- `q6Event_ev60`: on the 60-minute zero temp of FINDINGS F-24 the trigger holds, and the fix
  keeps all three pieces (oref0 keeps 30 of the 60 minutes, `q6_drops_zero_temp`).

## The combined version

`determineBasalFixed` (`LeanAID/Fixed/Combined.lean`) runs, in source order: oref0's profile
check, oref0's prelude with the F-11 check, oref0's predictions, oref0's dose phase with the
F-23 duration, and the F-04 step at the exit. Under the F-12 trigger these steps run on
`inputF12 inp p` (the capped profile, no microbolus; `inputFixed inp` is the input actually
evaluated), followed by `postF12`. `generateFixed` is
`generateF24`. `ValidInputFixed` is `ValidInput` without the conditions that the F-12 fix
makes unnecessary: `max_basal` and `max_daily_basal` may be missing or not numbers (V2, V3,
V10 apply only when they are numbers). `validInputFixed_of_valid`: it is weaker than
`ValidInput`; `validInput_of_fixed`: with a numeric `maxSafeBasal` the two agree.

**Nothing else changed** (`LeanAID/Fixed/Proofs/Combined.lean`)
- `determineBasalFixed_eq`: if none of the triggers of F-04, F-11, F-12, F-23 holds,
  `determineBasalFixed inp = determineBasal inp`. No other hypothesis.
- `generateFixed_eq`: if the F-24 trigger does not hold, `generateFixed inp = generate inp`.
- `triggers_nil`: `aid-lean --fixed-triggers` prints no trigger exactly when none holds.

**The safety rules without exceptions** (`LeanAID/Fixed/Proofs/Safety.lean`)

| rule | faithful version (`LeanAID.Proofs`) | corrected version (`LeanAID.Fixed`) |
|---|---|---|
| R1, R2 rate ceiling | `rate_le_roundBasal_maxSafeBasal`: valid input, rate ≤ `round_basal(maxSafeBasal)`, up to half a pump step above `maxSafeBasal` (`rate_can_exceed_maxSafeBasal`); exactly `maxSafeBasal` only on the grid (`rate_le_maxSafeBasal_of_grid`) | `rate_le_maxSafeBasal_fixed`: `ValidInputFixed`, `0 ≤ rate ≤ maxSafeBasal`, no rounding allowance, no grid condition |
| R12 unreliable CGM data | `cgm_unreliable_no_increase`: error code, noise, flat, or a **dated** reading too old or in the future; not for undated readings (`undated_glucose_max_rate`) | `cgm_unreliable_no_increase_fixed`: the same, **and undated readings**, also with `max_basal` missing; no microbolus, no increase |
| R12 (implementation condition) | `cgmError_no_increase` | `cgmError_no_increase_fixed` (the corrected check) |
| R14 missing maximum | `missing_max_basal_no_clamp`: 5.9 U/h for a scheduled 0.9 U/h | `missing_max_basal_fixed`: `current_basal` a double in `[0, 2^30]`; no microbolus, no rate above `current_basal` |
| R8, R9 low-glucose suspend | `low_glucose_suspend`: valid input (`max_basal` given); zero temp, but its duration can be NaN (F-23) and the pump rejects it (`low_glucose_pump`) | `low_glucose_suspend_fixed`: `ValidInputFixed`, so **also with `max_basal` or `max_daily_basal` missing (F-12)**; zero temp for 30-120 whole minutes or a running zero temp, and `validate` accepts the command |
| R5, R6, R7 microbolus | `microbolus_limits` (valid input) | `microbolus_limits_fixed` (`ValidInputFixed`): the same limits |
| R11 IOB at `max_iob` | `iob_at_max` | `iob_at_max_fixed`: the same |
| R13 missing data | `missing_current_basal`, `missing_targets`, `missing_iob` | `missing_current_basal_fixed`; `missing_targets_fixed`, `missing_iob_fixed` (oref0's error and no rate; the statements still say "no rate other than 0" for the F-12 case, which was the first version's result) |
| rates are doubles | `rate_double` | `rate_double_fixed` |

**Statements changed by the second F-12 version** (every other statement of this section and
of the per-finding sections is unchanged):
- `f12_fixed`: see F-12 above. `f12_rate_le` removed.
- `missing_max_basal_fixed`: was "no microbolus, and every finite rate is 0 (so at most
  `current_basal ≥ 0`)" for any profile with `current_basal`; now "no microbolus, and every
  finite rate is at most `current_basal`", for `current_basal` a double in `[0, 2^30]` (the
  condition of the F-04 step, which provides the cap).
- `cgmError_no_increase_fixed`, `cgm_unreliable_no_increase_fixed`: a replaced high temp can
  be `round_basal.down(M)` for `M = getMaxSafeBasal (capOf p)`, the `maxSafeBasal` in use
  (`capOf p` is `p`, or the capped profile under the F-12 trigger); was `getMaxSafeBasal p`.
- `low_glucose_suspend_fixed`: `ValidInput inp` became `ValidInputFixed inp`, and its `pre`
  is the corrected prelude of `inputFixed inp` (the input actually evaluated) instead of
  `inp`. Without the F-12 trigger `inputFixed inp = inp`, so for those inputs it is the old
  statement.
- Lemmas removed or renamed (not headline theorems): `determineBasalF12_refuse`,
  `refuseF12_units`, `uncapped_refuse`, `determineBasalFixed_units`; `uncapped_of_ok` became
  `uncapped_of_st` (no `maxSafeOk` hypothesis), `uncapped_ok` lost its `maxSafeOk`
  hypothesis. New: `fixed_of_ok`, `fixed_of_not12`, `fixed_of_trigger`, `inputFixed_of_*`,
  `capOf`, `cgm_capped`, `uncapped_rateDbl`, `capRate_rateDbl`, and the lemmas of
  `LeanAID/Fixed/Proofs/MaxBasalLgs.lean`.

`roundBasal_overshoot`, `roundBasal_monotone` and `setTempBasal_rate_bound` are about
`round_basal` and `setTempBasal`, which the corrected version still uses unchanged; they are
not restated. The theorems about runs (`LeanAID/Time`) are about the faithful version and
are not restated.

## What is not proved as intended

- **oref0's own tests on the patched copy** (`scripts/fixes/test.js`). The prompt asks for
  the same passes and failures as unpatched oref0. This holds for F-04, F-12, F-23 and F-24
  alone (234 pass, 10 fail, as unpatched). It does not hold for F-11: with all five patches
  196 pass and 48 fail. The 38 newly failing tests (37 titles; two tests share one) all fail
  with the F-11 patch alone. Every one is a test whose `determine_basal` input triggers the
  patch (the script checks this with a hook on `determine_basal`): oref0's tests pass glucose
  statuses without a `date` (DESIGN, "Why an explicit NaN"), which the F-11 fix treats as
  stale. No test fails on an input that does not trigger a patch. (The first F-12 version
  also broke 2 error-message tests; the second does not.)
- **F-04, the fix works** needs `maxSafeBasal` to be a double in `[0, 2^30]`
  (`f04_fixed`). Every number read from JSON is a double, and `maxSafeBasal ≤ max_basal`;
  `ValidInput` gives both (V10). A negative `maxSafeBasal` has no grid rate below it; the
  F-04 step then leaves the result alone (the F-12 trigger holds for such profiles, and the
  cap becomes `current_basal`).
- **Low-glucose suspend with the F-12 trigger is proved** (`low_glucose_suspend_fixed`, under
  `ValidInputFixed`), but in terms of the prelude and predictions of the input actually
  evaluated, `inputF12 inp p`, whose profile differs from `inp`'s in `max_basal`,
  `max_daily_basal` and the two multipliers, and whose `microBolusAllowed` is false. No theorem
  shows that `bg`, `threshold` and `minGuardBG` are the same as for `inp` (no code that
  computes them reads these fields, but that is checked by reading, not proved). Core's
  `lgs_setup` needs `ValidInput`, which the capped input does not satisfy when the autosens
  ratio or `autosens_max` is above 1 (V5, V9 ask `current_basal · ratio ≤ maxSafeBasal`);
  `lgs_setup_of` restates it with only the facts its proof uses (`current_basal > 0`, a
  numeric `maxSafeBasal ≥ 0`).
- **IOB at `max_iob`** (`iob_at_max_fixed`) keeps `ValidInput`, with `max_basal` present: it is
  not proved for the F-12 trigger. Core's proof needs the adjusted basal to be at most
  `round_basal(maxSafeBasal)` (`IobHyp.hbM`), which fails for the capped profile when the
  autosens ratio is above 1. What is proved for the trigger is `f12_fixed` and
  `missing_max_basal_fixed`: no microbolus and no rate above `current_basal`, not "no rate
  above the sensitivity-adjusted basal".
- **Low-glucose suspend with an undated reading** (F-11) is still not covered: an undated
  reading at low glucose takes the stale-data path, which leaves a running temp not above
  the scheduled basal in place instead of setting a zero temp; `low_glucose_suspend_fixed`
  assumes that the corrected prelude succeeds (a dated, fresh reading).
- **F-12 alone in JavaScript.** `F-12.patch` without `F-04.patch` can issue
  `round_basal(current_basal)`, up to half a pump step above `current_basal`; Lean's
  `determineBasalF12` includes the F-04 step on the capped profile. The patched copy that is
  tested (`oref0-fixed`) has both.
- **R12 for the corrected version** (`cgm_unreliable_no_increase_fixed`) has a slightly
  different conclusion from oref0's: a replaced high temp can be
  `round_basal.down(M)` instead of `round_basal(current_basal)` (F-04), where `M` is the
  `maxSafeBasal` in use (`capOf p`), and when no rate is issued, the running temp is not above
  `round_basal(current_basal)` or not above `current_basal`.
- **F-24, "the pieces cover the temp's whole time span"** is proved as a tiling
  (`splitTimespanF24_tiles`, `splitOne_parts`): every piece is kept or replaced by two
  contiguous parts whose durations are `d₁` and `d − d₁` in JavaScript arithmetic. No theorem
  sums the durations in exact arithmetic, and, as in `Core`, the loop has a fuel bound of
  10 000 passes that no theorem shows is never reached.
- **Triggers that are wider than the change.** `TriggerF12` also holds for a zero or
  negative limit; `TriggerF04` holds when `maxSafeBasal` is negative, where the F-04 step
  changes nothing. The "nothing else changed" theorems are unaffected; the counts below are
  counts of the triggers.
- **F-11 through `aid-lean`.** `getLastGlucose` gives an undated entry the deltas 0, so the
  F-11 input that matters (undated, non-zero deltas) can reach `determine_basal` only as a
  glucose status from another source; through CGM entries the trigger holds but the flat-data
  check already catches it (FINDINGS, "F-11 in the run model").

## Test results

All numbers below come from the scripts named; the JSON files are committed.

**Random decisions** (`TZ=UTC node scripts/difftest/run.js 100000 7 --fixed`,
`docs/difftest-fixed.json`). Each case runs through oref0, the patched copy of oref0 and
`aid-lean batch --fixed-triggers`.

| | cases |
|---|--:|
| identical to oref0 | 98,143 |
| differ from oref0, with a trigger | 1,857 (all F-04) |
| differ from oref0, without a trigger | **0** |
| identical to the patched oref0 | **100,000** |
| F-04 / F-11 / F-12 / F-23 trigger | 1,857 / 0 / 0 / 0 |
| fixed rate above `maxSafeBasal` (89,695 rates checked) | 0 |

On the 1,857 F-04 cases, oref0's rate is above its `maxSafeBasal` by up to 0.05 U/h
(`maxSafeBasal` 0.85, oref0 0.9, corrected 0.85); the corrected rate is never above it and at
most 0.1 U/h below it (the 0.1 U/h pump step above 10 U/h). The random generator makes
no F-11, F-12 or F-23 input, so those fixes are tested by the cases below and by the virtual
patients. The same command without `--fixed` gives 100,000 / 100,000 identical
(`docs/difftest.json`, unchanged). Both were rerun after the second F-12 version, with the
same counts.

**Random IOB cases** (`TZ=UTC IOB_JOBS=5 node scripts/difftest/iob.js 100000 1 --fixed`,
`docs/iobtest-fixed.json`).

| | cases |
|---|--:|
| identical to oref0 | 88,854 |
| differ from oref0, with the F-24 trigger | 11,146 |
| differ from oref0, without it | **0** |
| identical to the patched oref0 | **100,000** |
| F-24 trigger | 23,731 (12,585 of them give the same output) |

On the differing cases the IOB at some time differs by up to 1.883 U (zero-temp IOB: up to
3.11 U); 212,775 IOB ticks differ; at the first tick the corrected IOB is higher in 1,222
cases and lower in 4,188 (a dropped piece of a temp below the scheduled basal makes oref0's
IOB too high, a dropped piece above it makes it too low).

**Finding cases** (`scripts/fixes/findings.jsonl`, 12 cases, through
`node scripts/difftest/targeted.js --fixed`; table by `node scripts/fixes/show-findings.js`):
4 identical to oref0 (the controls and the undated readings through CGM entries), 8 differ
with a trigger, 12 / 12 identical to the patched oref0. The F-12 low-glucose case is new with
the second version; it differs from oref0 only in the reason.

| case | input | trigger | oref0 | corrected |
|---|---|---|---|---|
| F-04 trigger | max_basal 0.83 off the pump grid, BG 300 rising | F-04 | 0.85 U/h 30 min | 0.8 U/h 30 min |
| F-04 control | max_basal 0.85 on the grid | – | 0.85 U/h 30 min | 0.85 U/h 30 min |
| F-04 trigger (CGM-error branch) | current_basal = max_basal = 0.83, stale reading, temp 2 U/h running | F-04 | 0.85 U/h 30 min | 0.8 U/h 30 min |
| F-11 trigger | readings without dates, BG 250 rising | F-11 | 0.9 U/h 30 min | 0.9 U/h 30 min |
| F-11 control | the same readings dated now | – | 3.5 U/h 30 min | 3.5 U/h 30 min |
| F-12 trigger | no max_basal, no max_daily_basal, BG 300 rising | F-12 | 5.9 U/h 30 min | 0.9 U/h 30 min |
| F-12 trigger (running high temp) | no max_basal, temp 2 U/h running | F-12 | 5.9 U/h 30 min | 0 U/h 0 min (cancel) |
| F-12 trigger (long zero temp) | no max_basal, zero temp with 90 min left | F-12 | 5.9 U/h 30 min | 0.9 U/h 30 min |
| F-12 trigger (low glucose) | no max_basal, no max_daily_basal, BG 60 falling | F-12 | 0 U/h 30 min | 0 U/h 30 min |
| F-12 control | the test profile, max_basal 3.5 | – | 3.5 U/h 30 min | 3.5 U/h 30 min |
| F-23 trigger | mealCOB 20 without carbs, UAM, BG 60 rising | F-23 | 0 U/h NaN min | 0 U/h 30 min |
| F-23 control | the same with carbs 30 | – | 0 U/h 30 min | 0 U/h 30 min |

The F-11 trigger case gives the same rate through a different path (stale data instead of
"CGM data is unchanged"); see "F-11 through `aid-lean`" above. `scripts/check.sh` runs
`targeted.js --fixed` on `targeted.jsonl` and on this file.

**The JavaScript patches** (`bash scripts/fixes/apply.sh && TZ=UTC node
scripts/fixes/test.js`, `scripts/fixes/test-results.json`; the copies are in
`scripts/fixes/out/`, gitignored):

| oref0's own tests (244) | pass | fail | newly failing | of them on inputs that trigger the patch |
|---|--:|--:|--:|--:|
| unpatched | 234 | 10 | | |
| F-04 alone | 234 | 10 | 0 | |
| F-11 alone | 196 | 48 | 38 | 38 |
| F-12 alone | 234 | 10 | 0 | |
| F-23 alone | 234 | 10 | 0 | |
| F-24 alone | 234 | 10 | 0 | |
| all five | 196 | 48 | 38 | 38 |

With the first F-12 version, F-12 alone gave 232 pass and 12 fail: two error-message tests
pass the profile `{"current_basal": 0.0}` without `max_basal`, and the refusal came before
oref0's error. The second version returns oref0's errors unchanged. (`test.js` must run
outside the sandbox of the coding agent: inside it, oref0's Python and shell syntax checks
and its profile tests fail in every copy, unpatched included, giving 228 / 16.)

The finding reproductions with `--fixed` on the patched copy (`scripts/findings/run.js
--fixed`): F-04, F-11 and F-12 all ABSENT. The F-23 probe on the patched copy sends
durations 30, 30, 30, 60 and 30 (no `null`). The F-24 probe: the patched copy's treatments are
identical to the fix in memory (`sim/q6fix.js`) in 8 of 8 cases.

**Virtual patients** (`sim/run_fixed.py`, then `sim/fixed_report.py`,
`sim/out/fixed-report.json`). 30 patients, 2 days, meal seed 1, as items 1 and 3 of
`docs/SIM.md`; 576 decisions per run. The oref0 runs were re-run and agree with the SIM.md
runs in every metric for all 90 patients and faults.

| fault | controller | TIR 70-180 | < 70 | < 54 | > 180 | mean BG | U/day | lowest BG | runs with any < 54 | decisions identical to oref0 | monitor violations |
|---|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| none | oref0 (SIM.md) | 88.8 % | 3.20 % | 1.59 % | 8.0 % | 127.3 | 40.5 | 12 | 9 | | 0 |
| none | aid-lean --fixed | 88.8 % | 3.15 % | 1.57 % | 8.0 % | 127.4 | 40.5 | 14 | 9 | 16,733 / 17,280 | 0 |
| f11 | oref0 (SIM.md) | 88.9 % | 3.06 % | 1.61 % | 8.1 % | 127.9 | 40.3 | 11 | 9 | | 5 (R8) |
| f11 | aid-lean --fixed | 88.9 % | 3.04 % | 1.60 % | 8.1 % | 128.0 | 40.3 | 13 | 9 | 15,665 / 17,280 | 6 (R8) |
| f12 | oref0 (SIM.md) | 86.0 % | 8.29 % | 4.80 % | 5.7 % | 117.1 | 42.4 | 0 | 10 | | 1,065 (R1 1,064, R8 1) |
| f12 | aid-lean --fixed, F-12 first version | 83.8 % | 5.94 % | 2.48 % | 10.2 % | 131.6 | 39.2 | 18 | 6 | 0 / 17,280 | 962 (R8) |
| f12 | aid-lean --fixed, F-12 second version | 84.2 % | 0.38 % | 0.09 % | 15.4 % | 149.3 | 36.1 | 42 | 1 | 0 / 17,280 | 0 |

What this shows, and where it differs from what the prompt expected:

- **Without a fault the corrected version is not identical to oref0.** 547 of 17,280
  decisions differ: 525 are the F-04 cap and 22 are F-24 (a different IOB). The F-04 cases
  come from 7 patients, and in every one `maxSafeBasal` is a grid value minus floating-point
  error, for example `3 × 0.35 = 1.0499999999999998`: oref0 issues 1.05, above it by about
  2·10⁻¹⁶, and the corrected version issues 1.0, a full 0.05 U/h step lower. The fix does
  what the theorem states (no rate above `maxSafeBasal`, no rounding allowance), but in the
  simulator it fires only on this rounding noise. 23 of 30 patients have identical glucose
  metrics; time below 54 mg/dL is higher for 1 patient, lower for 2. The prompt expected
  identical results; both fixes fire on ordinary profiles and pump histories, so they are not.
- **F-11 fault:** 1,080 more decisions differ (the undated reading takes the stale-data path
  instead of "CGM data is unchanged"). Of the 1,099 differing decisions that are not the
  F-04 cap, 1,054 have oref0's rate, duration and microbolus, 45 a different rate or duration
  (none a different microbolus). The metrics are within 0.05 pp of oref0. One more R8 than oref0: the stale-data path leaves a zero temp
  expire at low glucose ("Temp 0 <= current basal; doing nothing"), as oref0's flat-data
  branch does in its 5 (F-18).
- **F-12 fault, first version:** every decision is the refusal. No rate above `maxSafeBasal`
  any more (R1: 1,064 → 0), less insulin (42.4 → 39.2 U/day), time below 54 mg/dL 4.80 % →
  2.48 %, time below 70 8.29 % → 5.94 %, lowest glucose 0 → 18 mg/dL; 9 patients have less
  time below 54, 3 have more. In exchange, time above 180 rises 5.7 % → 10.2 % and the
  monitor reports 962 R8 violations: the refusal never sets a zero temp, so at low glucose,
  once a zero temp has run out, the scheduled basal runs ("Temp 0 <= current basal; doing
  nothing"). This is why the first version was replaced.
- **F-12 fault, second version** (`sim/run_fixed.py --out sim/out/runs-fixed-f12v2
  --controllers aid-lean-fixed --faults f12`, then `sim/f12v2_report.py`,
  `sim/out/f12v2-report.json`; the oref0 and first-version runs are reused). The targets of
  the task were R1 0, R8 not above oref0's, and no patient with more time below 54 than
  oref0. All three are met: R1 0, R8 0 (oref0 1), and per patient the time below 54 is lower
  than oref0's for 10 patients and the same for 20 (all 20 at 0 %, for oref0 too). Time below
  54 is 0.09 % (one run with any time below 54, child#008: 2.60 % against oref0's 69.44 %),
  time below 70 0.38 %, lowest glucose 42 mg/dL. Every decision differs from oref0's (the
  reason ends with the F-12 note) and none is an error. The cost is high glucose: time
  above 180 is 15.4 % (oref0 with the fault 5.7 %, the intact profile 8.0 %), mean glucose
  149 mg/dL, 36.1 U/day: with the cap at the scheduled basal the loop cannot raise the rate
  to correct a high glucose. This is the cost of the cap the task asked for, not a defect of
  the fix; it is also the reason oref0 has a `max_basal` above the scheduled basal.
  The runs without a fault and with the F-11 fault were not rerun: the F-12 trigger needs a
  missing or non-positive maximum, which they do not have, so their decisions are those of
  the first version.

## Run times

On the maintainer's Mac (arm64), `aid-lean` built with `lake build`, copied to a
fixed path for the long runs (`AID_LEAN`) so that later builds did not change them.

| run | wall time |
|---|--:|
| `run.js 100000 7 --fixed` (oref0, patched oref0, aid-lean) | 2,936 s (48 min 56 s); aid-lean 2,893 s, node 42 s; second F-12 version: 2,548 s (42 min 29 s), aid-lean 2,505 s |
| `run.js 100000 7` (no `--fixed`, after all changes) | 17 min 15 s; aid-lean 1,010 s; second F-12 version: 19 min 42 s, aid-lean 1,143 s (run at the same time as the `--fixed` run) |
| `iob.js 100000 1 --fixed`, 5 processes | 24,547 s (6 h 49 min); aid-lean 116,558 CPU s, node 581 s |
| `scripts/fixes/test.js` (seven mocha runs, findings, probes) | about 38 s; 16 s for the second F-12 version |
| virtual patients, 180 runs, 3–4 in parallel | 14,578 s (4 h 3 min) |
| one 2-day run, oref0 | 14–22 s |
| one 2-day run, aid-lean --fixed, no fault / f11 | 768 s / 815 s on average (385–1,447 s) |
| one 2-day run, aid-lean --fixed, f12, first version (the refusal stops early) | 148 s on average |
| one 2-day run, aid-lean --fixed, f12, second version (3 in parallel) | 273 s on average (116–559 s); 30 runs in 2,770 s (46 min) |
| `lake build` of the changed `LeanAID/Fixed` files | each file 1.5–4 s to check |
| checking one `LeanAID/Fixed` file | 0.4–3.2 s |
