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
How common (`scripts/findings/f04-search.js`): with scheduled basals on the pump grid and
`max_basal` typed with two decimals, the issued rate exceeds the limit in 15–20 % of
combinations (40 % of those where `max_basal` is the binding limit); never when
`max_basal` is a multiple of 0.1 U/h. Overshoot at most 0.02 U/h in these ranges.

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
| Q6 | iob/history.js 58–77 | `splitTimespan` shares `splitFound` across elements of a pass: once one element is split, later unsplit elements of the same pass are dropped. Safety consequence: F-24 |
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

## Found by the work on runs (`LeanAID/Time/`)

`docs/timing-results.md` ranks the theorems about runs. F-20 and F-21 are checked by
`native_decide` on runs of the Lean model (`LeanAID/Conformance/TimeRuns.lean`). These runs
encode the pump history with decimal millisecond timestamps (`encodeAction`), not with
the ISO strings of a real pump history, and they were not replayed in JavaScript. F-22 and
F-23 were confirmed with oref0 0.7.1 under Node. F-19 is checked only on the Lean
transcription.

### F-19 — With an unrounded controller basal, the stale-data response can issue a rate above it
oref0 rounds `profile.current_basal` to the pump grid (`determine-basal.js:142`), and the
CGM-error branch issues that rounded value (lines 198-204). With `current_basal = 0.83`
U/h and the default 0.05 grid, a reading 20 minutes old with a 2 U/h temp running makes
oref0 replace the temp by 0.85 U/h, which is above 0.83 U/h. Checked by `decide` in
`LeanAID/Time/Examples.lean` (`staleInput`). Autotune writes basals with three decimals,
so it can produce such a value. A basal programmed on the pump is already on its grid.
The issued rate is a reduction of the running temp, and the excess is 0.01 U over 30
minutes. Dosing severity: low.

### F-20 — A stopped loop can leave a zero temp running for 120 minutes
In the low-glucose branch oref0 requests zero temps of 30 to 120 minutes
(`determine-basal.js:919` and 993), and `setTempBasal` keeps the requested duration
(`basal-set-temp.js:54`). If the loop stops right after such a temp is accepted, the pump
delivers no basal for up to 120 minutes. This is intended low-glucose protection. After a
loss of the loop its effect is underdelivery: 2 U less than the schedule at 1 U/h.
`p4b_fail_safe` proves the 120-minute bound. Run `zeroRun`: glucose 80, 70 and 60 mg/dL,
and the cycle at minute 10 issues 0 U/h for 120 minutes (`zeroRun_cycle_kernel`). The
modeled pump rate is 0 at minute 10 and at minute 130 − 1 ms, and 1 U/h from minute 130
(`zeroRun_pump`). Dosing severity: low. The zero temp is deliberate (the comment at
`determine-basal.js:918` says "always set a 30-120m zero temp"), oref0 issues it only when BG
is low or predicted low, and its length comes from the insulin to withhold. After a loss of
the loop the effect is underdelivery, the safer direction.

### F-21 — The IOB of microboluses alone can exceed `max_iob` after low temps
oref0 compares net IOB with `max_iob` (`determine-basal.js:1045` and 1062). Net IOB includes
the negative IOB of temps below the scheduled basal (`iob/history.js:553`). After two hours
of zero temps the net IOB in the model is about −1.2 U, and the guard then allows
microboluses whose own IOB exceeds `max_iob`. Run `i2Run`: `max_iob` 0.5 U, microboluses
of 0.5 U at minute 130 and 0.2 U at minute 135. At minute 140 their IOB is above 0.69 U
(`i2_fails`), and at each microbolus the guard `IOB + units ≤ 0.5` held (`i2Run_I1`).
So R21 holds at most for net IOB, not for the IOB of microboluses alone. The run does not
show net IOB above `max_iob` or an overdose. Its glucose trace (two hours at 60 mg/dL,
then a rise of 15 mg/dL every 5 minutes) is possible but contrived. Dosing severity: low.
The microboluses deliver more than `max_iob` beyond the scheduled basal, but oref0 defines
the limit on net IOB on purpose, and the run shows no overdose.

### F-22 — A basal schedule whose last entry has rate 0 gives no `current_basal`
`basalLookup` sorts the schedule by `i` and returns `undefined` when the rate of the last
sorted entry is 0 (`lib/profile/basal.js:14-19`), at every time of day. The controller then
sees no `current_basal`, and every cycle fails. The transcription does the same
(`basalLookup_last_zero`), and `ValidSchedule` rejects such a schedule (`envZ`).
`scripts/probe-basal-zero.js` confirms it under Node: with rates 1 and 0 U/h from 0:00 and
6:00, `determine_basal` returns "Error: could not get current basal rate" with no rate.
Dosing severity: low. The loop stops issuing commands and the pump runs its own schedule.
The risk is that the user does not see that the loop stopped.

### F-23 — Low glucose suspend with a NaN duration: the pump rejects the zero temp
In the low-glucose branch (`determine-basal.js:914-918`) the duration is
`min(120, max(30, round(round(60 * (target_bg - minGuardBG) / sens / current_basal) / 30) * 30))`.
If `minGuardBG` is NaN, oref0 requests rate 0 with a NaN duration (`"duration": null` in
JSON). `minGuardBG` is NaN when three conditions hold: `enableUAM` is on, the carb branch
of the guard is taken (`cid` is nonzero or `remainingCIpeak > 0`, lines 729-740), and
`fractionCarbsLeft = mealCOB / carbs` (line 709) is NaN or infinite, as when `mealCOB > 0`
and `carbs` is missing or 0. `scripts/probe-lgs-nan.js` shows it with BG 60 mg/dL rising
3 mg/dL per 5 minutes (cases A and B). Case D has the same COB and carbs but falling BG;
the carb branch is not taken there, and `minGuardBG` stays finite (44 mg/dL):
```
A ... {"bg":60,"rate":0,"duration":null,"reason":"... minGuardBG NaN<70"}
```
The pump model rejects this command, so a running positive temp continues.
`low_glucose_pump` states this case. `LeanAID/Conformance/F23Run.lean` checks a legal run with
a 2 U/h temp in the pump history: the theorem applies to it (`f23Run_covered`), its second
case holds (`f23Run_second`), and the temp keeps running (`f23Run_rate`). With `carbs` 30 the
same run has a finite `minGuardBG` and the pump accepts the zero temp (`f23RunC_checks`). We found no path through `lib/meal/total.js` that
produces this input, but we did not prove that none exists. `aid-lean --safe` now refuses
`mealCOB` without positive carbs. `LeanAID/Patched/LowGlucose.lean` models oref0 with the
NaN duration replaced by 30 minutes, and `lgs_patched_valid` proves that the pump accepts
its low-glucose command. `LeanAID/Core` is unchanged. Dosing severity: medium, but only if two
conditions hold that we did not show. First, oref0 must get this input: as said above, we
found no path through `lib/meal/total.js`, and we did not check apps that build their own
meal data. Second, the real pump driver must keep the old temp. The rig sends the command
with `mdt settempbasal` (`bin/oref0-pump-loop.sh:360`), which is not in `vendor/`. If the
driver reads `null` as 0, a Medtronic pump cancels the temp and runs the schedule, which is
milder. If both conditions hold, a high temp can continue at low glucose for up to 30
minutes.

### F-11 in the run model
In the run model the glucose status is `getLastGlucose` of the readings. When the readings
carry no date, every age is NaN, `getLastGlucose` finds no deltas, and it returns delta 0.
In the run `undated_flat` (last BG 200 mg/dL) the flat-CGM check (F-18) then stops any
increase. So the F-11 input (undated, with nonzero deltas) needs a `glucose_status` from
another source. `undated_flat` is one run, not a general theorem.

### Hypotheses of the run theorems
- `p1_dated` and `p1_true_age_head` assume `DatedReadings`: every reading has a positive
  finite recorded date. Undated readings (F-11) are excluded, not handled.
- True ages enter only through `RecordedNear δ`: each recorded date is within δ ms of the
  true time. The model has no other link between the two.
- `p1_true_age` and `getLastGlucose_date_between` assume `DoubleDates`: every recorded date
  is a positive double of the model. `Binary64.rd` has no exponent limit, so this admits
  values above `Number.MAX_VALUE`.
- `p1_true_age_head` assumes `HeadSpaced`: every reading after the newest one with a truthy
  value is at least 2.5 minutes older. Then `getLastGlucose` averages nothing. Readings
  less than 2.5 minutes apart, exact duplicates and backfilled readings that arrive out of
  date order are not covered.
- The readings of the run model carry only a value and a recorded date: no `sgv`, device,
  noise or type.
- `p6_delivered_sched` assumes `SmbMinutesOk env`: `maxSMBBasalMinutes` is absent or
  finite. Otherwise oref0 computes a NaN microbolus cap. The cap `smbCapOf env` is the
  model's rounding of (largest schedule rate) · max(30, maxSMB, maxUAM) / 60.
- `p5_gap` covers boluses in the run's action log only. A bolus in `env.initHistory` is not
  covered, and `Legal` puts no condition on that history: with initial records out of date
  order, oref0's record scan skips the newer one.
- `low_glucose_pump` assumes `InitDouble env`: the initial temp, if any, has a double rate.
  `low_glucose_suspend` concludes that a running temp left in place has rate 0 only for a
  double rate (`keepRunning_zero`). `rate_double` covers every rate a cycle issues, so only
  the initial temp is assumed.
- `low_glucose_pump` assumes `LowCycle`: BG or `minGuardBG` is below the threshold and
  oref0's first dose branch (`determine-basal.js:908-911`) is not taken.
- `temp_bound` and `p4b_fail_safe` assume `InitRemaining env t0`: the initial temp ends at
  most 120 minutes after `t0`, or 30 minutes with a positive rate. Their conclusion for the
  initial temp counts from `max tp.start t0`.
- The controller's `current_basal` and the pump's fallback rate both come from
  `env.profile.basalprofile`. With autotune, oref0 replaces the controller's basals
  (`bin/oref0-get-profile.js:239`) while the pump keeps its own schedule. `p4a_expiry`,
  `p4b_fail_safe`, `rate_envelope`, `p6_basal` and `p6_delivered` cover only equal
  schedules.
- The pump executes each accepted command exactly once and at once, and `currenttemp` is
  the true pump state. Lost acknowledgements, delays and stale pump reads are not modeled.


## Found by comparison with Screven et al. (arXiv:2606.13882)

Screven et al., "A Principled Framework for Safe Algorithm Updates in Automated Insulin
Delivery Systems" (2026), port Trio's oref from JavaScript to Swift. They report a
`splitTimespan` bug that drops pump events and causes 99.7% of the IOB differences
between the two versions. We had transcribed the same behavior as QUIRK Q6 without
rating it. We did not check that Trio's code is the same as oref0 0.7.1 here.

### F-24 — A temp longer than 30 minutes that crosses a basal schedule entry or midnight can lose pieces, and their insulin
`splitTimespan` (`iob/history.js` lines 50-80) cuts a temp into pieces of at most 30
minutes, at the start times of the basal schedule and at midnight. The flag `splitFound` is shared by
all pieces of one pass. So once a piece splits, every later piece of the same pass that
does not split is dropped (Q6), and its insulin is missing from IOB. Not every such temp
loses a piece: in cases C and D below, no pass has an unsplit piece after a piece that
splits, and unsplit pieces before the first split survive.
`LeanAID/Proofs/SplitTimespan.lean` states one pass exactly (`splitPass_fst`). On one
example, it checks with the kernel that a 60-minute zero temp from 05:50 with a basal
change at 06:00 keeps only the pieces 05:50-06:00 and 06:00-06:20 (`q6_drops_zero_temp`).
A fixed pass that keeps unsplit pieces also keeps 06:20-06:50 (`q6_fixed_keeps`).
`scripts/probe-split-timespan.js` runs oref0 under Node and a copy of `history.js` with
the fix, loaded in memory, on one temp each. The schedule is 1 U/h before 06:00 and
1.2 U/h after, except in cases B and H (1 U/h all day). Net temp insulin of the treatments (oref0, fixed, exact integral) and IOB
at 07:00 and 08:00, for H at 01:00 and 02:00 (oref0, fixed):
```
A zero temp 60m from 05:50   -0.55 / -1.15 / -1.17 U   07:00 -0.434 / -0.995   08:00 -0.239 / -0.601
F 2 U/h temp 60m from 05:50   0.40 /  0.80 /  0.83 U   07:00  0.311 /  0.685   08:00  0.170 /  0.410
G zero temp 90m from 05:20   -1.05 / -1.65 / -1.67 U   07:00 -0.735 / -1.297   08:00 -0.381 / -0.743
H zero temp 60m from 23:50   -0.50 / -1.00 / -1.00 U   01:00 -0.393 / -0.861   02:00 -0.217 / -0.518
```
So Q6 loses 0.60 U (A, G), 0.50 U (H, a flat schedule, at midnight) and 0.40 U (F) of net
temp insulin. The rest of the gap to the
exact integral is oref0's rounding, which the fix keeps. In cases B, C, D and E the fix
changes nothing: no piece is lost. These are probe results, not general proofs.
Q6 also cuts a temp that is never delivered. For its zero-temp forecast, `lib/iob` adds a
240-minute zero temp starting one minute after now (`find_insulin(inputs, 240)`,
`lib/iob/index.js` line 13) and reports its IOB as `iobWithZeroTemp`. `determine-basal`
uses it for the ZT forecast and `minZTGuardBG`. When this imagined temp crosses a schedule entry or midnight, it can
lose pieces too.
A lost piece whose rate is below the schedule, such as part of a zero temp, makes net IOB
too high. A lost piece above the schedule makes it too low. oref0's own positive temps
last 30 minutes, and its zero temps last 30 to 120 minutes. The IOB error depends on the
time: in cases A and G it is 0.56 U at 07:00 and 0.36 U at 08:00.
The virtual patients rate the effect on dosing (`docs/SIM.md`, "F-24"). With a basal
schedule of six steps, 30 patients, 3 meal seeds and 2 days, oref0 with the fix ran in
shadow on every input of oref0 (51,840 steps). IOB differed in 810 steps (1.56 %, 13 of
90 runs), by at most 0.64 U, and always in the same direction: oref0's IOB was too high.
The temp differed in 162 steps (0.31 %). Where both set a temp, the fixed version set a
higher rate by 0.19 U/h on average (−0.45 to +1.15 U/h). In closed loop, the fixed oref0
changed 12 of 90 runs. Time below 70 and below 54 did not change in any run. No run moved
more than 2 steps (0.35 percentage points) in a glucose band, 0.54 mg/dL in mean glucose
or 0.094 U/day in insulin. Insulin rose in 8 runs and fell in 4, by +0.002 U/day on
average. With a flat schedule, current IOB, actions, delivered insulin and glucose were
identical in all 90 pairs. Only the zero-temp IOB differed, in every flat run, at
20:30-20:55, when the imagined 240-minute zero temp crosses midnight. This changed the
forecasts or the reason text in 69 steps of 39 runs, and no action. Dosing severity: low.
In these runs Q6 makes oref0 give slightly less insulin on average, with small changes in
glucose. Not
covered by the runs: long manual high temps, which lose insulin in the other direction
(case F), SMB, other schedules, and runs longer than 2 days. Screven et al. found nearly the same
clinical outcome in simulation for their whole Swift port, which fixes this bug among
others, so their result does not rate this bug alone.
`LeanAID/Core` is unchanged.

## Found by the earlier timing work (T0, 2026-11-19), used by the UPPAAL replay

Before the rebase onto `main` (2026-11-23) this finding was F-22. It comes from the
earlier timing design (`docs/timing-plan.md`), and the UPPAAL replay (U3) relies on
it. `main` uses F-22 to F-24 for other findings, so the findings of this branch are
now F-25 to F-30.

### F-25 — `Iob.generate` cannot be evaluated by the kernel (limit of the transcription)
This is not a finding about oref0. `calcTempTreatments` (lib/iob/history.js,
transcribed in `LeanAID/Core/Iob.lean`) has two `while` loops (`Core/Iob.lean:430` and
`:495`), which Lean compiles to definitions the kernel does not unfold, and `sortByKey`
and `basalLookup` use `List.mergeSort`, which `decide` does not unfold. So `decide`
cannot evaluate concrete runs that call `generate`; they are checked by `native_decide`.
A theorem about what IOB or `lastBolusTime` `generate` returns can be stated, but its
proof needs facts about these definitions that are not available now. Two ways are
proposed and not done: a refactor of both loops into structural recursion (with the
existing fuel bound) and a check of the proof interface of `List.mergeSort`; or
theorems that take the needed fact as a hypothesis (`BolusSeen`, `docs/LOG.md`, T5).

Update after the rebase (2026-11-23, not rechecked in detail): `main` removed the two
`while` loops of `calcTempTreatments` (commit c00ffc2) and checks one cycle with the
kernel (`zeroRun_cycle_kernel`). `basalLookup` still sorts with `List.mergeSort`
(BAS-02). `Legal.bolusSeen` on `main` proves BolusSeen for legal runs. The UPPAAL
replay still checks its runs with `native_decide`.

## Found by the Munta run (U4, 2026-11-20, `uppaal/u4/`)

F-26 and F-27 are about the verified model checker Munta (commit `62cb1a4`, built by
`uppaal/u0b/setup_munta.sh`), not about oref0. Neither makes Munta give a wrong
answer in its own semantics. Both matter when a network is translated from UPPAAL
to Munta.

### F-26 — In Munta, time can pass in a committed location
In UPPAAL, time cannot pass while a process is in a committed location. In Munta,
"committed" only limits which process moves next. The network
`uppaal/u4/committed_delay.muntax` (UPPAAL: `committed_delay.xml`) resets `x` and enters
a committed location whose only edge out needs `x >= 5`. UPPAAL finds `E<> P.L2`
unreachable, and Munta finds it reachable. With the location also urgent, Munta
finds it unreachable. Before the fix, Munta reported P1 as not satisfied on the
lowered `nopump` network, with a path that lets time pass inside a step
(`uppaal/u4/p1_munta_smallest.muntax`). The U0b test `committed_chain` checked only
which process moves, so U0b missed this difference. Fix: the Munta writer
(`uppaal/munta.py`, `write_munta`) marks every committed location also as urgent.
`uppaal/u0b/README.md` records it as item 7 of "Semantic differences".

### F-27 — Munta's local clock ceilings can be too small, and Munta then rejects the network
On the 12-location network `uppaal/u4/ceiling_minimal.muntax`, with one clock guard
`x < 183`, Munta's own precondition "Ceiling resets" fails, and Munta prints "Input
invalid" with no result. UPPAAL accepts the network. A patched copy of Munta that
printed the ceilings (during U4, not committed) showed the cause: `local_ceiling`
gives ceiling 0 at the two entry locations, from which the guard is reachable
without a reset of `x`. So Munta refuses the input; it gives no wrong answer. Workaround in
`uppaal/munta.py` (`ceiling_loops`): every location gets a self-loop whose guard has
a contradictory data atom and every clock at its largest constant. The loop never
fires, so the behavior does not change, and UPPAAL checks the same network.
`uppaal/u0b/README.md` records it as input limit 17.

## Candidate findings from the extended models (U5, 2026-11-22, `uppaal/extensions.md`)

F-28 to F-30 come from UPPAAL models that extend the abstraction with behaviors
that T2 excludes. They are not results about T2 or about oref0. Each trace is a
run of an extended model, not a T2 run, so U3 does not replay it. Each waits for
an extended T2 in Lean. Each can be spurious, because the contract allows more
outputs than oref0 gives. The traces are in `uppaal/traces/u5/`, and the results
are in `uppaal/results.json` (IDs `U5-...`).

### F-28 — With delayed execution, P4b and the SMB spacing fail (candidate, extended model)
In the `delayed` model, an accepted command waits in a queue of 2 and executes at
most 300 s after its step. P4b-120 and P4b-30 fail: in trace `U5-delay-P4b-120`,
the last step at t0 issues a zero temp of 120 minutes and closes the run, and the
temp starts at t0 + 300 s. So it still runs 7200 s after the close. With the bound
shifted by the delay (7500 s and 2100 s), both queries hold on the model. P5-pair
fails: in trace `U5-delay-P5-pair`, steps at 0 s and 1 s each issue a microbolus.
The second decision does not see the first microbolus, because it has not
executed yet. Both execute at 1 s. P5-issued still holds, because the guard and
the observer read the same executed history.

### F-29 — With lost acknowledgements, a retry repeats a microbolus (candidate, extended model)
In the `lostack` model, a command can execute and lose its acknowledgement. A
later step can retry it with the same identity, without a new decision. P5-pair
fails: in trace `U5-ack-P5-pair`, a microbolus executes at 0 s with a lost
acknowledgement, and its retry at 1 s executes again. P5-issued holds, because a
retry is not a decision. With a pump that ignores a copy of a command that it
executed (`lostack-dedup`), P5-pair holds. P4b-120 and P4b-30 hold on the `lostack`
model, because retries happen only in steps, so nothing executes after the close.

### F-30 — With two loops, a decision from an old snapshot breaks the SMB spacing (candidate, extended model)
In the `twoloops` model, each loop takes its own snapshot, and its spacing guard
reads the snapshot. P5-pair fails: in trace `U5-two-P5-pair`, loop 1 takes a
snapshot at 0 s, the other loop issues a microbolus at 0.5 s, and loop 1 issues a
microbolus at 1 s from its old snapshot. Both execute. P5-issued also fails
(trace `U5-two-P5-issued`: a user bolus comes between the snapshot and the
decision). P4b-120 and P4b-30 hold on the model, because each command executes in
its own step.
