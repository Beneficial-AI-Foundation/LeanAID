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
Proved in Lean: `rate_can_exceed_maxSafeBasal`. Strongest true statements proved:
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
stated only for dated readings (`cgm_unreliable_no_increase`).

### F-12 — Missing `max_basal` / `max_daily_basal` disables the clamp (R14)
`getMaxSafeBasal` is `Math.min(max_basal, 3·max_daily_basal, 4·current_basal)`; with
either input missing it is NaN, `rate > maxSafeBasal` is always false, and no clamp is
applied. Concrete input: test profile without `max_basal` and `max_daily_basal`, BG 300
and rising, IOB 0 → oref0 issues **5.9 U/h** (basal 0.9 + 2 × max_iob 2.5), 6.6 × the
scheduled basal. Reproduced in Node. Proved: `missing_max_basal_no_clamp`, which also
shows `validInputB` is false for this input, so `aid-lean --safe` refuses it (exit 2).
Without `--safe`, aid-lean reproduces oref0's 5.9 U/h.

### F-13 — Exact and floating-point IOB differ by more than one rounding unit
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
