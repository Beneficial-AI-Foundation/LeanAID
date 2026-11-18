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
