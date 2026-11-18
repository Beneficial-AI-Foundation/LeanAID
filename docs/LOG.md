# LeanAID experiment log

All times are local (EET, UTC+2). One agent session (Claude Opus 5.5 in Claude Code).

---

## M0 – Setup

**Start:** 2026-11-18 12:05 · **End:** 2026-11-18 12:55

### What was done
- Cloned `https://github.com/openaps/oref0` into `vendor/oref0`, checked out
  `88cf032aa74ff25f69464a7d9cd601ee3940c0b3` (tag 0.7.1). `vendor/` is git-ignored;
  nothing in it was edited.
- `npm install --no-save` inside `vendor/oref0` (only oref0's declared packages).
- Lake project: `lean-toolchain` = `leanprover/lean4:v4.36.0`, library `LeanAID`,
  executable `aid-lean`, `@[test_driver]` script for `lake test`.
- `scripts/check.sh`: rejects `sorry` anywhere; `partial`, `unsafe`, `@[extern]`,
  `implemented_by`, `Float`, Mathlib imports in `LeanAID/Core`; `native_decide`
  outside `LeanAID/Conformance`; any `axiom` declaration. It prints `#print axioms`
  for every theorem listed in `scripts/headline.txt` and fails if any depends on an
  axiom other than `propext`, `Classical.choice`, `Quot.sound`. Verified that it
  fails on a planted `sorry` and `partial def`.

### oref0's own test suite (Node v24.21.0, `TZ=UTC mocha tests/*.js`)

**234 passing, 10 failing.** Per file:

| file | passing | failing | note |
|---|---|---|---|
| basal.test.js | 2 | 0 | |
| bolus.test.js | 1 | 0 | out of scope (bolus wizard parsing) |
| check-syntax.test.js | 128 | 1 | `bin/oref0-cron-every-minute.sh` fails `bash -n` on macOS bash 3.2; not in scope |
| cobhistory.test.js | 1 | 0 | |
| determine-basal.test.js | 52 | 0 | 10 `round_basal` + 42 `determine-basal` |
| get-last-glucose.test.js | 5 | 0 | |
| iob.test.js | 25 | 0 | |
| profile.test.js | 0 | 7 | all fail with `TypeError: Cannot read properties of undefined (reading 'hasOwnProperty')`: the test calls `require('../lib/profile')(inputs)` but `generate` now takes `(final_result, inputs, opts)`. Upstream test rot, not an algorithm failure. Profile generation is outside the dose decision. |
| set-temp-basal.test.js | 12 | 0 | |
| tests-in-shell.test.js | 1 | 2 | shell tests depend on GNU tools / Linux; out of scope |
| with-raw-glucose.test.js | 5 | 0 | |

Every test of the in-scope code (determine-basal, round-basal, set-temp-basal, iob,
get-last-glucose, basal lookup, cob history) passes under Node.

### Decisions
- **No Mathlib.** Core Lean 4.36 ships `Rat` with order lemmas, and `grind` closes
  linear goals over `Rat`. Avoiding Mathlib keeps builds fast and makes the
  "core depends only on Lean core" rule trivially true. Revisit if a proof needs it.
- **Numbers: exact rationals plus an explicit `NaN`.** While reading
  `determine-basal.test.js` I found that oref0's own tests pass objects with missing
  fields (no `date` on `glucose_status`, no `lastCarbTime` on `meal_data`, no
  `carb_ratio` on one profile). JavaScript turns these into `NaN`, and the algorithm
  carries the `NaN` through several branches (e.g. a missing glucose date makes the
  staleness check `minAgo > 12` false, so it is silently skipped). A faithful
  transcription must reproduce this, so the core works over
  `JsNum := nan | fin Rat`. See `docs/DESIGN.md`.
- `decide` cannot evaluate `Rat` arithmetic (gcd is well-founded recursion), so
  conformance will use `native_decide`, which the rules allow in `LeanAID/Conformance`
  only.

### What was hard / surprises
- The kickoff counts 70 determine-basal tests. The file has 70 `it(...)` blocks:
  47 active and 23 disabled (12 with `//it(`, 11 inside two `/* ... */` blocks). One
  active block is a loop that mocha runs as 6 tests, hence mocha's 52.
  (Corrected during M1; my first count at M0 was 52 + 18.)
- `iob.test.js` has 25 active tests and 1 commented out (26 total).

---

## M1 – Test inventory

**Start:** 2026-11-18 12:55 · **End:** 2026-11-18 13:35

### What was done
- `scripts/inventory.js` extracts every `it(...)` block (active or commented out) from
  the six in-scope test files: inputs written in the test and its assertions →
  `docs/tests-inventory.json`.
- `scripts/test-classes.json`: first classification A/B/C/D per test, with the general
  property each A/B test is an instance of. `scripts/tests_md.js` renders
  `docs/TESTS.md`.
- `scripts/capture/` runs the same mocha tests with a hook that records every
  top-level call to an in-scope function (arguments deep-copied *before* the call,
  because oref0 mutates its inputs) and its result, tagged with the running test.
  `Date.now()` / `new Date()` are frozen at 2026-11-18T12:00:00Z and `TZ=UTC`, so the
  iob tests (which build timestamps from "now") have fixed inputs.
  Output: `scripts/capture/out/*.json` (42 determine_basal, 10 round_basal,
  13 setTempBasal, 51 iob, 5 getLastGlucose, 2+1 basal, 1 findMealInputs calls).

### Totals
116 test blocks: 48 A, 11 B, 33 C, 24 D (disabled upstream).

### Observations (to FINDINGS)
- **No determine-basal test reaches the prediction code.** Every test passes a single
  IOB object instead of the IOB array produced by `oref0-calculate-iob`; the
  prediction loop calls `iobArray.forEach`, which throws on a plain object, and the
  `catch` swallows it ("Optional feature Advanced Meal Assist disabled"). So
  `minPredBG`, `minGuardBG` are 999 in all 42 calls, COB/UAM/ZT predictions are never
  computed, and the SMB branch is never entered (`microBolusAllowed` is never passed).
- **DB-51 is vacuous**: its profile has the key `"max_bg "` (trailing space), so oref0
  returns `Error: could not determine target_bg` and the test's "no rate set" assertion
  holds because of the error.
- Tests mutate the shared `profile` object (DB-65 to DB-70 inherit
  `current_basal_safety_multiplier`, `max_daily_safety_multiplier`, `max_basal`,
  `current_basal`, `model` from earlier tests). Conformance must use the captured
  per-call inputs, not the textual defaults.
- `meal_data` in the shared defaults has `carbs: 50` but no `lastCarbTime`, so
  `remainingCATime` is `NaN` in every determine-basal test.
- DB-68's profile has no `carb_ratio`; oref0 reports `CR: NaN` in its reason string.

### Decision
- Disabled (D) tests are not asserted: their expectations were disabled by the oref0
  authors and several use an obsolete input format (`avgdelta`). Where their inputs are
  complete, conformance will run them through both Node and Lean and require equal
  outputs.
- An attempt to auto-uncomment the disabled tests and run them under Node was
  abandoned: the heuristic also re-enabled commented-out assertions inside active
  tests, so its pass/fail counts were meaningless.

---

## M2 – Requirements and traceability

**Start:** 2026-11-18 13:35 · **End:** 2026-11-18 14:05

### What was done
- Located the two FDA papers on PMC (PMC2864162, PMC3262707). PMC marks both as free
  to read but **not open access**, so I read them from PMC but did not store copies in
  `refs/` (the repository is meant to be pushed publicly). `refs/README.md` cites them
  with links and lists the table/requirement IDs used.
- Downloaded 21 CFR 862.1356 and 880.5730 (public domain) from the eCFR API into
  `refs/` as text. (First attempts failed: the renderer endpoint 404s and the
  versioner endpoint requires `Accept-Encoding`; `curl --compressed` worked.)
- `docs/REQUIREMENTS.md`: 23 numbered requirements (R1–R23) plus an out-of-scope
  table, each with sources and status. The pump-oriented requirements of SR2011 are
  adapted to a controller ("shall not deliver" → "shall not command").
- `docs/TRACEABILITY.md`: source → requirement → theorem → test table; theorem
  column to be filled at M5/M6.

### Decisions
- "Valid input" is deferred to M5 and will be one Lean definition (`ValidInput`) used
  by every theorem, documented in `docs/DESIGN.md`.
- Out-of-bounds input (R14) is handled in `aid-lean` by shell-side validation, which is
  not verified; for oref0 it is a testing question, and I expect findings (NaN paths).

---

## M3 – Transcription

**Start:** 2026-11-18 14:05 · **End:** 2026-11-18 16:40

### What was done
Transcribed into `LeanAID/Core` (pure, Lean core only, no forbidden constructs):

| oref0 file | Lean module | notes |
|---|---|---|
| `lib/round-basal.js` | `RoundBasal.lean` | |
| `lib/basal-set-temp.js` | `BasalSetTemp.lean` | `getMaxSafeBasal`, `setTempBasal` |
| `lib/determine-basal/determine-basal.js` | `DetermineBasal.lean` | three phases: `dbPrelude` (l.128-423, early returns as `Except`), `dbPredict` (l.428-903), `dbDose` (l.905-1188) |
| `lib/iob/calculate.js`, `total.js`, `history.js`, `index.js`; `basalLookup`/`maxDailyBasal` of `lib/profile/basal.js` | `Iob.lean` | |
| `lib/glucose-get-last.js` | `Glucose.lean` | |
| `lib/meal/history.js` | `MealHistory.lean` | |
| `Math.exp` | `Exp.lean` | halving + degree-30 Taylor + squaring, 2^-128 grid |
| JS numbers, `Math.round`, `toFixed`, `Number→String` | `JsNum.lean` | |
| `Date` (`toString`, `toISOString`, `getMinutes`) | `DateFmt.lean` | |
| `JSON.stringify(rT)` | `JsonOut.lean` | exact key order per return path |

### Plan change: COB calculation deferred
`lib/meal/total.js` and `lib/determine-basal/cob.js` (carbs on board, i.e. producing
`meal_data`) are **not transcribed yet**. Reading `cob.js` showed it is stateful in
ways that need careful modelling: it mutates the shared `profile.current_basal`, and
its IOB lookups use an `iob_inputs.clock` left over from the *previous* call — on the
first call that clock is `undefined`, so moment-timezone substitutes the **wall
clock**, making `oref0-meal` depend on when it runs. No oref0 test exercises it.
`determine_basal` and `oref0-determine-basal` take `meal_data` as an input, so the dose
decision is complete without it. Decision: finish the minimum result (M4–M7) first and
come back to COB afterwards; until then the project page and report state that COB
computation is not transcribed.

### What was hard
- **JS `undefined`/`NaN` semantics.** Every input field is `Option`; arithmetic uses
  `NaN` for `undefined`, comparisons with `NaN` are false, `!==` distinguishes
  `undefined` from `NaN`. oref0's own tests depend on this (missing `date`,
  `lastCarbTime`, `carb_ratio`).
- **Output fidelity.** To compare with oref0 byte for byte I reproduced
  `JSON.stringify` key order for each return path (the SMB path sets `rate` before
  `duration`; the eventualBG error object already carries `temp`/`deliverAt`),
  number printing, `toFixed`, and `Date.prototype.toString`.
- **Structure-instance layout**: multi-line `{ a := .., b := .. }` with continuation
  lines indented less than the first field fails to parse; the generator and the
  IOB module were reformatted.
- **Aliasing in history.js** (found by conformance, see M4): modelled with an
  `origin` index on temp events.

### Quirks reproduced on purpose (QUIRK Qn in the code; details in FINDINGS)
Q1 `forEach` on a single IOB object throws → no predictions; Q2 missing glucose date
→ staleness check skipped; Q3 implicit globals `COBpredBG`/`UAMpredBG`; Q4
`maxCOBPredBG` compared against `maxIOBPredBG`; Q5 missing `lastCarbTime` → NaN
`remainingCATime`; Q6 `splitTimespan` drops events; Q7 `lastSuspendTime` string
compared with numbers; Q8 in-place mutation of aliased temp events.

---

## M4 – Conformance

**Start:** 2026-11-18 15:20 (overlapping M3) · **End:** 2026-11-18 16:45

### What was done
- `scripts/gen_conformance.js` turns the captured calls into Lean data
  (`LeanAID/Conformance/Data/*.lean`, generated): exact decimal literals, `undefined`
  → `none`, pump-history timestamps parsed with oref0's own moment-timezone.
- `scripts/capture/disabled.js` replays the inputs of the 23 disabled determine-basal
  tests through Node (their assertions are not used).
- `LeanAID/Conformance/Checks.lean`: one `native_decide` theorem per suite.

### Results
| suite | cases | exact agreement |
|---|---|---|
| determine_basal (active tests) | 42 | 42 (identical JSON, incl. reason strings) |
| determine_basal (disabled tests' inputs) | 23 | 23 |
| round_basal | 10 | 10 |
| setTempBasal | 13 | 13 (rate, duration, reason) |
| basalLookup / maxDailyBasal | 2 / 1 | 2 / 1 |
| getLastGlucose | 5 | 5 (identical JSON) |
| meal history (cobhistory) | 1 | 1 |
| lib/iob generate (48-element IOB arrays) | 51 | 49 exact; 2 differ only at proved rounding ties |

### Failures found and fixed on the way
1. IOB lastTemp in 4 suspend tests (IOB-15, 17, 18, 19): oref0's `splitAroundSuspends`
   mutates temp-basal objects in place, and unsplit events are the same objects as the
   `tempHistory` entries returned to index.js, so the mutation leaks into `lastTemp`
   (oref0 reports a lastTemp **duration of −15 min** in IOB-17). Modelled as QUIRK Q8.
   First attempt broke IOB-16 because my clone marking did not apply (a text
   substitution silently missed after reformatting); fixed.
2. The eventualBG error object carries `temp` and `deliverAt` (disabled tests DB-54..63,
   old `avgdelta` input format → `NaN` eventualBG).

### Not exact: rounding ties (2 IOB calls, test IOB-26)
At 15 minutes after a 1 U bolus with DIA 4 h (bilinear curve), activity is
11.25 × 1/9000 = 0.00125 exactly. Exact arithmetic rounds the tie up (0.0013);
JavaScript's doubles compute 0.0012499999… and round down (0.0012). Same at 75 minutes
(0.00625). `iob_ties` checks that these are the only differences and that each is an
exact tie. This is the expected cost of exact arithmetic (DESIGN D2).

---

## M5 – Safety envelope (headline theorems)

**Start:** 2026-11-18 16:45 · **End:** 2026-11-18 21:30

### Results (all checked by `lake build`, no `sorry`, axioms: propext, Classical.choice, Quot.sound)
| id | theorem | statement |
|---|---|---|
| H1 | `rate_le_roundBasal_maxSafeBasal`, `rate_le_maxSafeBasal_of_grid` | valid input ⇒ every finite issued rate ∈ [0, round_basal(maxSafeBasal)]; ≤ maxSafeBasal when it is on the pump grid |
| H2 | `microbolus_limits` | a finite microbolus u: u > 0, u ≤ maxBolus, iob + u ≤ max_iob, last bolus > SMBInterval ago |
| H3 | `low_glucose_suspend` | BG or minGuardBG below threshold, not (BG below threshold and rising) ⇒ zero temp (or running zero temp kept), no microbolus |
| H4 | `iob_at_max` | iob ≥ max_iob ⇒ no microbolus, every finite rate ≤ adjusted basal |
| H5 | `cgmError_no_increase`, `missing_current_basal`, `missing_targets`, `missing_iob` | error-coded/noisy/stale/flat CGM ⇒ no increase, no microbolus; missing inputs ⇒ error |
| H6 | `rate_can_exceed_maxSafeBasal` (finding), `roundBasal_overshoot`, `roundBasal_monotone` | rounding can exceed the limit by ≤ half an increment |

### What was hard
- **Reasoning through the transcription.** Unfolding the whole prelude timed out
  (`whnf` heartbeats); `simp` on `dbPredict` hit its step limit; `split` picked the
  wrong `if` inside `setTempBasal`. Each was solved by naming sub-steps in the core
  (stage functions with one early exit each, `keepRunning`, `smbLowTemp`,
  `smbReasonUnits` as one `addReason`, `highTempSet`, `capInsulinReq`,
  `tempTargetRatio`, building `rT` as one literal). Every refactor was re-checked
  against oref0 by the conformance suite (65/65 after each). The SMB refactor merged
  several `rT.reason +=` steps into one concatenation; this is equal by associativity
  of string append, and is checked by differential testing (no oref0 test reaches it).
- **The SMB low temp bound.** `round(basal·d/30, 2) ≤ basal` is false for arbitrary
  basal (e.g. basal 0.025, d = 30 gives 0.03). It holds because the basal comes out of
  `round_basal` (a multiple of 0.025) and d < 30; the proof goes through the 1/40 grid.
- **Microbolus ≤ room below max_iob.** `insulinReq` is rounded to 3 decimals *after*
  the max_iob cap, so it can exceed the cap by 0.0005. The bound still holds because
  the microbolus is at most half of it, and a positive rounded value implies the room
  is at least 0.0005.
- `simp` normal forms: unfolding `HMul.hMul` also unfolded `*` on `Rat`; replaced by a
  file of `@[simp]` lemmas on finite `JsNum`s.
- Failed attempts: `generalize` with `_` holes (stuck typeclass problems); `rw` through
  `dbPredict` projections (motive not type correct). Replaced by lemmas stated for an
  arbitrary context `c : Ctx` and instantiated.

### Plan changes / decisions
- "Valid input" (`Spec/Valid.lean`, DESIGN) required one condition I had not expected:
  the sensitivity-adjusted basal must be within maxSafeBasal (V5), because the SMB low
  temp bypasses the clamp (F-05).
- Theorems about rates are stated for *finite* issued rates. oref0 can issue `rate: NaN`
  (F-06, confirmed in Node), which is a finding, not something to prove away.
- R4 (duration bounds) is not proved: durations can be NaN for inputs that are valid
  under V0–V9 but have inconsistent meal data. Left as planned.
- Mathlib still not needed.

### Findings confirmed in Node
F-04 (0.83 → 0.85 U/h) and F-06 (`rate: null`, reason "setting NaNU/hr").
