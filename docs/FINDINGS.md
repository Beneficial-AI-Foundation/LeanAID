# Findings

Facts about oref0 0.7.1 (commit 88cf032) found while transcribing, testing and proving.
Each was reproduced under Node (commands below, run from `vendor/oref0`) unless stated.
None of these is a claim that oref0 is unsafe in practice: most need inputs that the
rest of OpenAPS normally prevents. They are what a formal model makes visible.

## Safety-relevant

### F-04 — Rounding can push the temp basal above `maxSafeBasal` (R3)
`setTempBasal` clamps the request to `maxSafeBasal` and *then* rounds with
`round_basal`, which can round up. With `max_basal = 0.83` (any `maxSafeBasal` not on
the pump's 0.05/0.025 grid) a request of 2 U/h is issued as **0.85 U/h**.
```
node -e 'var t=require("./lib/basal-set-temp");console.log(t.setTempBasal(2,30,{current_basal:0.5,max_basal:0.83,max_daily_basal:1},{}))'
→ { duration: 30, rate: 0.85 }
```
Proved in Lean: `rate_can_exceed_maxSafeBasal`. It also occurs on random valid inputs:
difftest case 28557 (seed 7) has `maxSafeBasal` 4.44 and issues 4.45 U/h. Strongest true statements proved:
every issued rate is ≤ `round_basal(maxSafeBasal)` (`rate_le_roundBasal_maxSafeBasal`),
which exceeds `maxSafeBasal` by at most 0.025 U/h below 10 U/h (`roundBasal_overshoot`);
and when `maxSafeBasal` is on the grid the bound is `maxSafeBasal` itself
(`rate_le_maxSafeBasal_of_grid`). R1 is therefore met only up to half a pump increment.

### F-05 — The SMB low temp is not clamped to `maxSafeBasal`
The SMB branch returns `rate = round(basal × durationReq/30, 2)` directly (line 1155),
without `setTempBasal`. If the sensitivity-adjusted basal exceeds `maxSafeBasal`
(autosens ratio × `current_basal` > `max_basal`), this rate can exceed it. Our H1
excludes this by validity condition V5/V9 (adjusted basal within `maxSafeBasal`); with
V5 the low temp is proved ≤ the adjusted basal (`smbLowTemp_bound`, using the 0.025
grid). Without V5 the bound fails; an input with autosens ratio 2 and `max_basal` 1.5
reached the SMB microbolus path in Node but not the low-temp path, so no concrete
over-limit low temp was observed yet (M10 will search for one).

### F-06 — NaN temp basal rate when carbs are present without `lastCarbTime`
With `meal_data.carbs > 0` and `mealCOB > 0` but no `lastCarbTime`, `remainingCATime`
becomes NaN, the COB predictions become NaN, `minPredBG` and `insulinReq` become NaN, and
oref0 issues `{"rate": null, "duration": 30}` with reason "no temp, setting NaNU/hr".
```
(see scripts in docs/LOG.md, M5) → {"rate":null,"duration":30,"eventualBG":null}
```
A pump driver receiving `rate: null` may reject or misinterpret the command. This is the
kind of out-of-bounds input CFR862 (b)(3)(iv) is about (R14). Our theorems are stated for
finite issued rates. `aid-lean determine-basal --safe` refuses such inputs (exit code 2); without `--safe` it reproduces oref0's output, NaN included.

### F-01 — oref0's tests never reach the prediction, COB, UAM or SMB code
All 42 determine-basal test calls pass a single IOB object, on which the prediction
loop's `forEach` throws; the `catch` swallows it. So `minPredBG`/`minGuardBG` are 999 in
every test, and no test passes `microBolusAllowed`. The most complex half of
`determine_basal` (lines 439–903 and 1076–1160), including all microbolus logic, is
untested by oref0's suite. Our proofs cover it; conformance on it comes from
differential testing (M10).

## Test-suite findings

- **F-02** 23 of 70 determine-basal test blocks are disabled (12 `//it`, 11 in
  `/* */`); 10 use an obsolete input format (`avgdelta`) and would now hit
  "could not calculate eventualBG".
- **F-03** DB-51 is vacuous: its profile key is `"max_bg "` (trailing space), so the
  call returns an error and the "no rate" assertion holds for that reason.
- **F-07** `profile.test.js` fails entirely (7/7): it calls `generate(inputs)` but the
  function now takes `(final_result, inputs, opts)`.
- **F-08** Tests share and mutate one `profile` object; DB-65 to DB-70 depend on test
  order.

## Transcription quirks (reproduced on purpose)

| id | where | behaviour |
|---|---|---|
| Q1 | determine-basal.js 573–644 | `iobArray.forEach` on a single object throws; caught; predictions empty |
| Q2 | 149–150 | missing glucose `date` → `minAgo` NaN → staleness check skipped (every oref0 test). Safety consequence: F-11 |
| Q3 | 596, 610 | `COBpredBG`, `UAMpredBG` are implicit globals |
| Q4 | 636 | `maxCOBPredBG` is updated when COBpredBG exceeds `maxIOBPredBG` (not `maxCOBPredBG`) |
| Q5 | 500 | missing `lastCarbTime` → NaN `remainingCATime` (see F-06) |
| Q6 | iob/history.js 58–77 | `splitTimespan` shares `splitFound` across elements of a pass: once one element is split, later unsplit elements of the same pass are dropped |
| Q7 | iob/history.js 106–112 | `lastSuspendTime` is a timestamp string compared with numbers (always false for ISO strings): the "currently suspended" adjustment is dead code |
| Q8 | iob/history.js 85–157 | `splitAroundSuspends` mutates temp-basal objects in place; unsplit events alias the returned `tempHistory`, so `lastTemp` can show a mutated date and a **negative duration** (−15 min in test IOB-17) |
| Q9 | determine-basal.js 949 + basal-set-temp.js 5 | reason strings contain ". . " (neutral temp: "as temp. . Setting neutral …") |
| Q10 | lib/meal/total.js, cob.js | COB uses an IOB clock left over from the previous call; the first call uses the wall clock (not transcribed yet, see LOG) |

## Arithmetic

- **F-09** Exact arithmetic and doubles disagree at rounding ties (DESIGN D2): 2 of 51
  IOB test calls differ in `activity` by 0.0001 because the exact value is a tie. The
  effect of a tie can be much larger than one unit when it feeds a later decision: F-13.
  **Resolved** (second review, step 3): the core now rounds every operation to the
  nearest double; all 51 IOB calls agree exactly.

## Found during M6

### F-10 — The bilinear insulin curve gives negative IOB for a positive dose
The post-peak IOB polynomial `0.001323·x² − 0.054233·x + 0.55556` (iob/calculate.js
line 81) has its minimum at x ≈ 20.5, where it is about −0.00023. With DIA 3 h a dose
given 177 minutes ago contributes −0.00021 × dose: −0.0021 U for 10 U, visible after
oref0's 3-decimal rounding. Proved: `bilinear_negative`. So "IOB is never negative for
non-negative doses" (R18) is false for oref0's bilinear curve; the strongest version is
"≥ −0.00023 × dose" (not yet proved).

### Tests that were not generalised (M6)
| test | why |
|---|---|
| DB-17, DB-35, DB-39 ("high-temp when eventual BG is high": rate above basal) | The natural general claim, "eventualBG ≥ max_bg and IOB < max_iob ⇒ rate ≥ basal", is false: `insulinReq` uses `min(minPredBG, eventualBG)`, so a low `minPredBG` gives a rate below basal even when eventualBG is high (and an SMB-enabled run can set an SMB zero temp). A true version needs `min(minPredBG, eventualBG) ≥ target_bg`, no SMB and no running temp; it is plausible but was not proved. The tests' own assertions are proved by evaluation. |
| DB-19 (a running temp > 2× insulinReq is replaced) | branch-specific; only the concrete check is proved |
| IOB-24, IOB-25 (temps with no duration / percent temps add no IOB) | would need a theorem about the whole pump-history pipeline (history.js); checked by conformance only |
| BAS-02 (basalLookup) | `basalLookup` sorts with `List.mergeSort`, which the kernel cannot evaluate; checked by conformance (`native_decide`) only |

## Found or sharpened by the independent review (2026-11-18, of commit a95cea8)

### F-11 — An undated glucose reading disables the staleness check (safety)
Previously listed only as quirk Q2. If `glucose_status` has no `date` (or the CGM entry
has no `date`, `display_time` or `dateString`, so `getLastGlucose` returns NaN), then
`minAgo` is NaN, `minAgo > 12 || minAgo < -5` is false, and the reading is used however
old it is. Concrete input: BG 250 mg/dL, delta/short/long avgdelta +5, no date, test
profile (`current_basal` 0.9, `max_basal` 3.5), IOB 0, autosens 1, no temp running →
oref0 issues **3.5 U/h for 30 min** (its maximum). The same reading dated 60 minutes
earlier is refused as stale.
```
node -e '…determine_basal({glucose:250,delta:5,short_avgdelta:5,long_avgdelta:5},{duration:0,rate:0,temp:"absolute"},{iob:0,activity:0},prof,{ratio:1},{},t,false,null,now)'
→ rate 3.5, duration 30, "adj. req. rate: 5.9 to maxSafeBasal: 3.5, no temp, setting 3.5U/hr."
```
Proved: `undated_glucose_max_rate` (both the 3.5 U/h result and the stale refusal when
dated) and `undated_never_stale` (no undated reading is ever stale). R12 is therefore
stated only for dated readings (`cgm_unreliable_no_increase`). `aid-lean --safe` refuses
undated readings (DESIGN, "What `aid-lean --safe` rejects").
**In a closed loop** (`docs/SIM.md`, 30 patients × 2 days, the last reading repeated
without a date during two 45-minute dropouts a day): no harm. The repeated reading has
delta 0, so oref0's flat-CGM check (F-18) catches it and no temp is raised; against
plain dropout, mean BG +0.2 mg/dL and insulin −0.05 U/day on average. The F-11 input
above (an undated reading with non-zero deltas) did not arise in this scenario.

### F-12 — Missing `max_basal` / `max_daily_basal` disables the clamp (R14)
`getMaxSafeBasal` is `Math.min(max_basal, 3·max_daily_basal, 4·current_basal)`; with
either input missing it is NaN, `rate > maxSafeBasal` is always false, and no clamp is
applied. Concrete input: test profile without `max_basal` and `max_daily_basal`, BG 300
and rising, IOB 0 → oref0 issues **5.9 U/h** (basal 0.9 + 2 × max_iob 2.5), 6.6 × the
scheduled basal. Reproduced in Node. Proved: `missing_max_basal_no_clamp`, which also
shows `validInputB` is false for this input, so `aid-lean --safe` refuses it (exit 2).
Without `--safe`, aid-lean reproduces oref0's 5.9 U/h.
**In a closed loop** (`docs/SIM.md`, 30 patients × 2 days, profile without `max_basal`,
both arms identical): 1,064 decisions per arm above the configured `max_basal` (monitor R1),
up to 9.8 × it (median of the per-patient maxima 3.8 ×); +1.9 U/day insulin and −10 mg/dL
mean BG on average; time below 54 mg/dL 4.8 % against 1.6 % with the profile intact; 18
of 30 patients spent more time below 70.

### F-13 — Exact and floating-point IOB differ by more than one rounding unit
**Resolved** by modelling binary64 in the core (second review, step 3; DESIGN "Numbers"):
both examples below now give oref0's result. Kept for the record.

F-09 understated this. A tie in an *intermediate* value can change a later integer
decision. Example (iob/history.js lines 545-548): a temp of 0.05 U/h against a basal of
0.2 U/h for 30 min. Exactly, `netBasalRate·30·10/6 = −7.5`, `Math.round` gives −7,
`netBasalAmount = −0.07`, `tempBolusCount = round(1.4) = 1` temp bolus. In JavaScript
`0.05 − 0.2 = −0.15000000000000002`, the product is −7.500000000000001, which rounds to
−8, giving 2 temp boluses: 0.05 U more negative insulin. The reviewer counted 1302 such
(temp, basal, duration) combinations. Differential testing of determine_basal (pilot,
2000 random inputs) also shows ties in the 2-decimal prediction sums propagating into
`minGuardBG`, `eventualBG`, `insulinReq` and, in 3 cases, the issued rate (e.g. 3.15
vs 3.2 U/h). The divergence is still caused by exact ties, but its effect on outputs is
not bounded by one unit of the final rounding.

The most severe case found (difftest pilot, seed 1): `minDelta − bgi = −6 − (−6.05)`.
Exactly this is 0.05, so `ci = round(0.05, 1) = 0.1 > 0` and the UAM predictions switch
on (determine-basal.js line 681); in doubles it is 0.04999999999999982, `ci = 0`, and they
stay off. oref0 then issues a **30-minute zero temp** (eventualBG −147) while aid-lean
issues the **neutral basal 2.05 U/h** (eventualBG 162). oref0's decision is discontinuous
at `ci = 0`, and floating-point noise decides which side a tie lands on. Neither result
is "the" correct one; it shows that exact-rational faithfulness cannot give
decision-level agreement everywhere. Bit-exact agreement would need IEEE-754 double
emulation in the core (possible with rationals: round each operation to the nearest
double), at the cost of harder proofs.

### F-14 — Mismatches without a rounding tie: multiplication error printed in reasons
**Resolved** (second review, step 3): with binary64 arithmetic aid-lean prints oref0's
values; `node scripts/difftest/regress.js` reproduces all 4 outputs byte for byte.

The 4 of 100,000 differential-test mismatches (seed 7) whose oref0 run hit no
near-tie `Math.round` (cases 22322, 28557, 65907, 66816) all differ only in the
reason text, at "to maxSafeBasal: …". `getMaxSafeBasal` computes
`3 × max_daily_basal` in doubles: 3 × 1.3 = 3.9000000000000004, 3 × 1.48 =
4.4399999999999995, 3 × 2.52 = 7.5600000000000005, 3 × 3.8 = 11.399999999999999; oref0
prints these, aid-lean (exact arithmetic) printed 3.9, 4.44, 7.56, 11.4. The issued rates
agree. Cause: binary64 rounding of a multiplication, not a tie and not a transcription
error. The inputs and oref0 outputs are kept in `scripts/difftest/regression-no-tie.jsonl`
as regression cases for the IEEE-754 model (LOG, step 3 of the second review).

### F-15 — With exact arithmetic, aid-lean's dose differs from oref0's in 82/100,000 cases, usually higher
**Resolved** (second review, step 3): with binary64 arithmetic all 100,000 outputs of the
same run (seed 7) are byte-identical to oref0's (`docs/difftest.json`), and
`scripts/difftest/regress.js` gives oref0's rate on the 5 worst cases below.

Differential testing (seed 7, 100,000 valid random inputs): the issued temp basal rate
differs in 82 cases. aid-lean's rate is higher in 76, lower in 3, and in 3 one side
issues no rate. Differences range from −0.06 to +0.8 U/h (median +0.05). Cause: an exact
rounding tie that oref0's doubles round the other way (F-13), at a decision point: the
hypo threshold comparison (`minGuardBG 82 < 83` in oref0, 83 in aid-lean), the carb
impact `ci > 0` that switches COB/UAM predictions on, or the 0.05 U/h rate grid. The worst
cases are oref0 zero temps where aid-lean issues insulin:
- case 90274: oref0 0 U/h, aid-lean 0.8 U/h (30 min). BG 267 (prev 274, 283), current_basal 1.7, sens 77, carb_ratio 19.6, min/max_bg 126/146, iob 1.823, activity 0.0214, autosens 1.1, mealCOB 0/0, SMB allowed true, UAM false.
- case 15683: oref0 0 U/h, aid-lean 0.575 U/h (30 min). BG 262 (prev 270, 281), current_basal 0.8, sens 106, carb_ratio 16.1, min/max_bg 129/142, iob 0.055, activity 0.0296, autosens 0.73, mealCOB 47/61, SMB allowed true, UAM false.
- case 41082: oref0 0 U/h, aid-lean 0.475 U/h (30 min). BG 349 (prev 354, 359), current_basal 0.5, sens 40, carb_ratio 10.3, min/max_bg 118/124, iob 5.571, activity 0.024, autosens 0.95, mealCOB 5/79, SMB allowed false, UAM true.
Full inputs: `scripts/difftest/worst-rate-diffs.jsonl` (top 5 by difference).
**Safety reading:** each aid-lean decision still satisfies the proved safety theorems
(they hold for every valid input), but aid-lean is not a drop-in equivalent of oref0 on
these inputs, and its deviation is more often towards more insulin. This is the reason
for modelling binary64 exactly (second review, step 3).

### F-16 — Double rounding in the safety statements (theorem statements changed)
With the core computing in IEEE-754 doubles (second review, step 3), some properties
that held exactly for rational arithmetic hold only up to rounding, and some proofs need
the inputs to be doubles. Every statement that changed, and why:

| theorem | before (exact rationals) | now (doubles) | why |
|---|---|---|---|
| all safety theorems (via `ValidProfile`) | V1, V2 as numbers | V10 added: `current_basal` and `max_basal` are doubles (`rd x = x`), `max_basal ≤ 2^30` U/h | `rd(1 · cb) ≥ cb` needs `cb` to be a double; `round_basal` is idempotent only below a bound. Every number parsed from JSON is a double; 2^30 U/h is not a restriction in practice |
| V5 (`autosens_max`) | `n/100` | the double nearest `n/100`, `0 ≤ n ≤ 2^40` | 0.01 steps are not doubles |
| `microbolus_limits` (H2) | `u ≤ maxBolus`, `iob + u ≤ max_iob` | `u ≤ maxBolus + maxBolus/2^50 + 2^-90`, `iob + u ≤ max_iob + (max_iob − iob)/2^44 + 2^-79` | in doubles `floor(y·k)/k` can round one ulp above `y` (`k` = 1/bolus_increment is itself rounded), and `max_iob − iob` is rounded. The excess is below 10⁻¹² U for any realistic `max_iob` |
| `low_glucose_suspend` (H3) | a running temp left in place has rate 0 | its rate `x` satisfies `rd x = x → x = 0` | the "close enough" test `0.8·x ≤ 0 ≤ 1.2·x` in doubles also accepts non-double rationals with \|x\| < 2^-1074; the only double among them is 0 |
| `roundBasal_overshoot` (H6) | `rbR M ≤ M + 1/40` (or `+ 1/20` from 10 U/h) | needs `0 ≤ M`; bound `+ (M+1)/2^50` | `M · scale` and the quotient are rounded |
| `rate_can_exceed_maxSafeBasal` (F-04) | 0.83 → 0.85 | the doubles nearest 0.83 and 0.85 | same counterexample, values as doubles |
| `roundBasal_nearest` (DB-01..05) | `|rts·s − x·s| ≤ 1/2` | needs `0 ≤ x`; `±(x·s+1)/2^50`; lower bound `≤` instead of `<` | rounding of `x·s` and the quotient |
| `bilinear_at_zero` (IOB-01) | `iobContrib = insulin` | `= rd(insulin)` (the dose as a double) | the final multiplication is rounded |
| `bilinear_after_dia` (IOB-01) | `180 ≤ 3/dia · m` | `180 + 180/2^50 ≤ 3/dia · m` and `dia ≤ 1000` h; and new `bilinear_after_dia'` with the exact hypothesis on the computed scaled time, `180 ≤ rd(rd(3/dia) · m)` (used for the test instance at m = 180) | the scaled time is computed in doubles; the DIA bound keeps the absolute rounding error below the relative one |
| `maxDailyBasal_ge` (BAS-01) | every scheduled rate `≤ maxDailyBasal` | rates `≥ 0`; `r ≤ m + m/2^51 + 2^-90` | oref0 computes `maxRate * 1000 / 1000`, which in doubles can be one ulp below `maxRate` |
| internal: `tempTargetRatio_pos` | ratio `> 0` | `≥ 0` | a positive quotient can round to 0 (only below 2^-1075) |
| internal: `DoseHyp.hbgrid`, `smbLowTemp_bound` | basal is `k/40` | basal is the double nearest `n/s`, `s ∈ {10,20,40}`; the SMB duration is an integer | 0.025 is not a double; the bound `round(basal·d/30, 2) ≤ basal` is re-proved by an error analysis |

Unchanged: H1 (`rate_le_roundBasal_maxSafeBasal`, `rate_le_maxSafeBasal_of_grid`), H4
(`iob_at_max`), H5 (`cgmError_no_increase`, `cgm_unreliable_no_increase` with the same
12.05 / −5.05 minute hypotheses, proved by monotonicity of rounding and kernel evaluation
at the threshold), `missing_*`, `undated_glucose_max_rate`, `missing_max_basal_no_clamp`,
`setTempBasal_rate_bound`, `roundBasal_monotone`. All are proved for the double model.

## Found by the virtual-patient harness (M11)

### F-17 — Carbs dated after the decision time: division by zero, aid-lean and oref0 differ
**Open.** Found 2026-11-18 by the first smoke run of `sim/`, which (through a time-zone
bug in the harness, since fixed) gave determine-basal a `currentTime` 2 h before the
carb entry: `meal_data.lastCarbTime` 2 h in the future. The profile is valid (V0–V10).
Then `lastCarbAge` = −120 min, `remainingCATime` = 3 + 1.5·(−120)/60 = 0, and
determine-basal.js divides by it (`remainingCIpeak`). JavaScript gives `Infinity`, the
Lean core `NaN` (DESIGN D1), so the COB and UAM predictions differ: oref0 prints
`predBGs.COB`/`UAM` and `minPredBG 39, … COBpredBG 39, UAMpredBG 39`, aid-lean has no
COB/UAM curves and `minPredBG 55`. In this case the issued rate and duration agree (a
zero temp, from `minGuardBG 34 < 75`). Reproduce: `sim/regression-future-carbs.json`
(input and both outputs; aid-lean's difference also appears with oref0's own IOB,
through `aid-lean batch`).
**Consequence:** DESIGN D1 claimed that valid input never divides by zero; that is false
for meal data, which the validity conditions V0–V10 do not constrain. Future-dated carb
entries are possible in practice (Nightscout accepts them; a phone clock can be ahead).
Not yet checked: whether the rate can differ, and whether `--safe` should reject
`lastCarbTime > currentTime` (as it rejects carbs without `lastCarbTime`, F-06).

### F-18 — Flat CGM data below the threshold: no zero temp (R8 does not cover it)
**Open.** Found 2026-11-19 by the safety monitor in the overnight closed-loop runs
(`docs/SIM.md`). determine-basal.js lines 177-185 treat a reading as a CGM error when
`delta` is exactly 0 and both average deltas are within ±1 (above 60 mg/dL): it then only
replaces a high temp or shortens a long zero temp, and otherwise does nothing, **whatever
the glucose**. Two ways this happened at a reading below `threshold` (75 mg/dL here),
with a non-zero basal running:
- the first reading after a gap of more than ~40 minutes: `getLastGlucose`
  (glucose-get-last.js lines 66-84) finds no earlier reading in its windows and returns
  `delta`, `short_avgdelta` and `long_avgdelta` = 0. 12 decisions (7 in dropout runs,
  5 in F-11 runs), e.g. adolescent#005 at 15:45 after the 15:00-15:45 dropout: CGM 68,
  "CGM data is unchanged (68+0)", the scheduled 0.7 U/h runs; the next reading gets a
  120-min zero temp;
- a genuinely flat low CGM: 4 decisions (1 in an F-12 run, 3 in a 7-day run), e.g.
  child#009 (7 days, meal seed 2) at 16:15-16:25 on day 6: CGM 65, 65, 65 with true BG
  61-63; a neutral 0.4 U/h temp is left running for 15 minutes.
These 16 are oref0-arm decisions; the paired aid-lean runs made the same 13 (the 7-day
run's aid-lean twin was discarded at the 12-hour deadline), so the monitor counted 29 R8
violations in all. **This is not a counterexample to a theorem:** `low_glucose_suspend` assumes `dbPrelude inp = .ok
pre`, and the prelude fails on `cgmFlat` (part of `cgmError`). But REQUIREMENTS R8/R9 said
only "fresh, non-error glucose reading", which a reader takes as excluding error codes,
not flat data; the text now states the exclusion. Consequence in these runs: small (each
episode ends at the next reading that differs), but the insulin is given when BG is
already low. Not yet checked: whether a stuck sensor reading low for longer can keep the
basal running for longer (the flat check needs `delta` = 0 exactly, so noise ends it).

## Found by the timing work (2026-11-19, `docs/timing-plan.md`)

### F-19 — With an unrounded basal, a stale reading can still give a rate above the schedule (P1)
With `current_basal = 0.83` U/h, oref0 compares with and issues
`profile_current_basal = round_basal(0.83) = 0.85` U/h. On a stale reading (20 minutes
old) with a 2 U/h temp running, the CGM-error branch replaces the temp with 0.85 U/h,
which is above the scheduled 0.83 U/h. Checked by `decide` in
`LeanAID/Time/Examples.lean` (`staleInput`). P1 is stated, as the plan says, against
the rounded basal; the gap to the schedule is at most half a pump increment (F-04).

### F-20 — A stopped loop can leave a zero temp running for 120 minutes (P4b)
oref0 issues zero temps of up to 120 minutes (lines 741 and 898; `durationReq` is
rounded to 30-minute steps and capped at 120). If the loop stops right after such a
temp is accepted, the pump delivers nothing for 120 minutes before the schedule
resumes. This is low delivery, not overdose. Run `zeroRun` in
`LeanAID/Conformance/TimeRuns.lean`: glucose 80, 70, 60 mg/dL, the cycle at minute 10
issues 0 U/h for 120 minutes, and the pump rate is 0 until minute 130 and then the
scheduled 1 U/h (`zeroRun_cycle`, `zeroRun_pump`, by `native_decide`).

### F-21 — R21 in the plain reading (form I2) does not hold: microboluses can stack past `max_iob`
The microbolus guard compares the *computed* IOB, which includes the negative IOB of
temps below the scheduled basal. After two hours of zero temps the computed IOB is about
−1.2 U, and the guard then allows microboluses whose own IOB exceeds `max_iob`. Run
`i2Run` in `LeanAID/Conformance/TimeRuns.lean`: `max_iob` 0.5 U, microboluses of 0.5 U
(minute 130) and 0.2 U (minute 135); at minute 140 the IOB of these two microboluses
alone is above 0.69 U (`i2_fails`). At each microbolus the guard of form I1 held
(`i2Run_I1`). So R21 holds at most in form I1 (the lifted guard), not in form I2.

### F-22 — `Iob.generate` cannot be evaluated by the kernel or reasoned about
`calcTempTreatments` (lib/iob/history.js, transcribed in `LeanAID/Core/Iob.lean`) uses a
`while` loop (line 495), which Lean compiles to a `partial` function that is opaque to
the kernel, and `sortByKey` and `basalLookup` use `List.mergeSort`, which `decide` does
not unfold. So no theorem can state what IOB or `lastBolusTime` `generate` returns for a
given history, and concrete runs that call it can only be checked by `native_decide`.
Not a bug in oref0; a limit of the transcription for proofs. A refactor of the loop
into structural recursion (with the existing fuel bound) and of the sort into a
structural sort would remove it; that is a change of `LeanAID/Core` and is left to the
maintainer. The timing theorems that need a fact about `generate` take it as an
explicit hypothesis (see `docs/LOG.md`, T5 and T6).

### F-11 in the run model
In the T2 run model the glucose status is `getLastGlucose` of dated or undated CGM
entries. When the entries carry no date, every age is NaN, `getLastGlucose` finds no
deltas and returns delta 0, and the flat-CGM check (F-18) stops any increase
(`undated_flat` in `LeanAID/Conformance/TimeRuns.lean`). The F-11 input (undated, with
non-zero deltas) does not arise from these entries. It can still arise from entries
with a `display_time` or `dateString` that do not parse, or from other sources of
`glucose_status`.

### P1 "dated" is not proved (statement recorded, not weakened silently)
The plan's P1 says that a cycle that increases insulin has a dated reading. Per call
this is false (F-11). In the run model it would need a lemma about `getLastGlucose`
that is not done. So `p1_faithful` states that `cgmStale` is false, which includes a
NaN age, and `p1_derived` takes a whole-number date as a hypothesis. A status date that
`getLastGlucose` averages from two readings less than 2.5 minutes apart can be a half
millisecond; `p1_derived` then does not apply. See `docs/LOG.md`, T3.
