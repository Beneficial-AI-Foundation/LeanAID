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
finite issued rates, and the `aid-lean` shell rejects such inputs (M7).

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
| Q2 | 149–150 | missing glucose `date` → `minAgo` NaN → staleness check skipped (every oref0 test) |
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
  IOB test calls differ in `activity` by 0.0001 because the exact value is a tie.

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
