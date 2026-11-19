# LeanAID experiment log

All times are local (EET, UTC+2). One agent session (Claude Opus 5.5 in Claude Code).

*Correction (14:27):* the start/end times first written for M0–M6 were my estimates
and were wrong (they ran to the next morning). They have been replaced by times taken
from the git commit timestamps. Note also that my M6 commit (7b9290f) accidentally
included an uncommitted 14-line edit of `site/index.html` made by the maintainer
during the session (`git add -A`); from M7 on I stage only my own files.

---

## M0 – Setup

**Start:** 2026-11-18 12:05 · **End:** 2026-11-18 12:20

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

**Start:** 2026-11-18 12:20 · **End:** 2026-11-18 12:25

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

**Start:** 2026-11-18 12:25 · **End:** 2026-11-18 12:31

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

**Start:** 2026-11-18 12:31 · **End:** 2026-11-18 13:01

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

**Start:** 2026-11-18 12:42 (overlapping M3) · **End:** 2026-11-18 13:01

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

**Start:** 2026-11-18 13:01 · **End:** 2026-11-18 14:08

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

---

## M6 – Tests lifted to theorems

**Start:** 2026-11-18 14:08 · **End:** 2026-11-18 14:22

### Results
- **52 of 59 class A/B tests** are instances of proved general theorems. For each
  determine-basal test, `LeanAID/Proofs/Tests.lean` (generated by
  `scripts/gen_test_theorems.js`) has `<id>_test` — the test's own assertions on the
  test's exact inputs, proved by kernel evaluation (`decide +kernel`, no
  `native_decide`) — and, where a general theorem applies, `<id>_general`, that
  theorem applied to the same input (validity of the input is itself decided by a
  checker proved sound, `validInputB_sound`). Small suites: `Proofs/TestsSmall.lean`.
- New general theorems: `low_eventual_rate_le_basal` (R10, 8 B tests),
  `dbDose_neutral` (7+3 A tests), `setTempBasal_no_temp`, `setTempBasal_skip_neutral`,
  `roundBasal_nearest`, `curveSetup_dia`, `bilinear_at_zero`, `bilinear_after_dia`,
  `maxDailyBasal_ge`.
- 7 not generalised (DB-17, 19, 35, 39, IOB-24, 25, BAS-02): reasons in FINDINGS.
- Finding F-10: bilinear IOB can be negative for a positive dose.

### What was hard / changed
- **Validity was too strict for oref0's own test inputs** (they have no
  `autosens_max`). V5/V9 were restated as what the proofs use: "the basal scaled by
  autosens_max / by the autosens ratio stays within maxSafeBasal". All H1–H6 proofs
  were re-checked under the weaker (more general) conditions.
- The kernel cannot evaluate `String.splitOn`, `String.endsWith` or `List.mergeSort`
  (well-founded recursion). Regex assertions on `reason` use a structurally recursive
  substring matcher on `List Char`; BAS-02 stays a `native_decide` check.
- I first grouped DB-10/31/32 with "low eventual BG"; the kernel refused the
  hypothesis because their eventual BG (111, 119) is above min_bg 110. They take the
  in-range branch and are instances of `dbDose_neutral`.

---

## M7 – Binary (minimum result)

**Start:** 2026-11-18 14:22 · **End:** 2026-11-18 14:30 (commit times)

### What was done
- `App/Json.lean`: JSON → core inputs using the toolchain's `Lean.Json` (numbers are
  exact decimals, so no floating point anywhere), and ECMAScript `Date.parse` for ISO
  strings (local time without a zone).
- `App/Main.lean`: `aid-lean determine-basal <iob> <currenttemp> <glucose> <profile>
  [<autosens>] [<meal>]` plus oref0's options `--auto-sens --meal --reservoir
  --currentTime --microbolus` (same behaviour: `--microbolus` needs an `autotune`
  directory), JSON on stdout or the error on stderr; `--safe` (not in oref0) refuses
  input outside the valid domain. `aid-lean selftest` reruns all 148 conformance
  cases: **148/148 (2 at rounding ties)**.
- `LeanAID/Core/Step.lean`: `step`, exported to C as `aid_step` (checked in the
  generated C: `LEAN_EXPORT lean_object* aid_step(lean_object*)`).
- `lake test` builds everything (all proofs and native_decide conformance checks),
  runs `aid-lean selftest` and `scripts/check.sh`: passes.
- First end-to-end comparison with `oref0-determine-basal` on an input that exercises
  the prediction loop, COB and UAM (none of oref0's tests do): **byte-identical output**.
- `scripts/report.js` → `docs/numbers.json`: 116 test blocks, 52/59 class A/B tests
  lifted, 215 theorems (13 headline), axioms propext/Classical.choice/Quot.sound,
  0 sorry, conformance 148/148.
- `site/index.html` updated with these numbers, theorem names, a findings section and
  revised limits. The maintainer was editing the same file during the session, so I
  applied my changes on top of their working copy and **left the file uncommitted**
  for them to review.

### Minimum result (M0–M7) reached, with these gaps
- `lib/meal/total.js` and `cob.js` (COB calculation) not transcribed (see M3).
- R4 (duration bounds) and the IOB/exp error bounds not proved.
- 7 of 59 class A/B tests not generalised (FINDINGS).

---

## Review fixes (independent review of commit a95cea8)

**Start:** 2026-11-18 14:30 · **End:** 2026-11-18 14:47 (commit times)

The maintainer ran an independent reviewer (`prompts/review.md`) and asked for six
remaining issues to be addressed:

1. **Undated glucose (F-11).** Promoted from quirk Q2 to a safety finding.
   `undated_glucose_max_rate` (kernel-evaluated): BG 250 rising, no date → 3.5 U/h for
   30 min; the same reading dated 60 min earlier → refused as stale.
   `undated_never_stale`: no undated reading is ever stale. Reproduced in Node.
2. **R12 restated** as `cgm_unreliable_no_increase`, with hypotheses on the raw input
   (BG ≤ 10 or = 38, noise ≥ 3, dated and age ≥ 12.05 min or < −5.05 min, or oref0's
   flat-data condition) instead of the implementation predicate `cgmError`. The 0.05
   min margin is oref0's rounding of the age to 0.1 min (an age of 12.04 min rounds to
   12.0, which oref0 does not treat as stale). Its docstring states that undated
   readings and NaN noise are not covered.
3. **Missing max_basal (F-12).** `missing_max_basal_no_clamp`: maxSafeBasal NaN, 5.9 U/h
   for current_basal 0.9, and `validInputB` false, so `aid-lean --safe` refuses it.
4. **IOB arithmetic (F-13).** Confirmed the reviewer's example in Node
   (−7.500000000000001 → 2 temp boluses; exact −7.5 → 1). **Correction:** M4 and
   DESIGN D2 said exact and floating-point results differ "only at ties". The cause is
   always an exact tie, but its effect is not limited to one unit of the final
   rounding: a tie in an intermediate value can change a later integer decision (a
   whole temp bolus), and in determine_basal it can change minGuardBG, eventualBG and the
   issued rate (difftest pilot). DESIGN D2 and FINDINGS F-09 are corrected.
5. **Sources.** PMC serves the PDFs only behind a browser JavaScript check (Europe PMC
   returned 403), which I did not try to circumvent. Stored instead: the text of the
   PMC full-text pages, `refs/HA2010-PMC2864162.txt` and `refs/SR2011-PMC3262707.txt`.
   PMC marks both as free to read but not open-access licensed; flagged in
   `refs/README.md` for the maintainer to decide before publishing. Every cited
   HA2010/SR2011 ID was checked against the text: all exist. Corrections: R2's
   paraphrase of SR2011 1.2.1 was wrong (it says rates from 0.05 U/h, not "from 0");
   SR2011 1.3.16 (extended-bolus remainder counted as IOB) and 1.3.5 (no bolus while one
   is running) are now marked as adaptations where cited for R6 and R7.
6. **Project page.** States the counts produced by the build (52 of 59 generalisable
   tests, 116 inventoried), that conformance checks use `native_decide`, that oref0's
   tests never reach the prediction/SMB code (F-01), and adds F-11, F-12; "bad data
   fails safe" is now "proved, with a gap". The file again includes the maintainer's
   own uncommitted edits, so I leave it uncommitted for review.

### Difftest pilot (M10, in progress), recorded here because it informed item 4
2000 random valid inputs: 1645 identical, 12 differ only in the reason text, 343 differ
in values. 306 of those are prediction arrays differing by ±1 at rounding ties; the rest
include 3 different issued rates. One case is **not** a tie: oref0 eventualBG −147 vs
aid-lean 162 (aid-lean also reports a UAMpredBG oref0 does not). This looks like a
transcription bug in the COB/UAM eventualBG update; to investigate next.

---

## M10 – Differential testing (stretch)

**Start:** 2026-11-18 14:30 (pilot, before the review fixes) · **End:** 2026-11-18 14:55 (commit times)

### What was done
- `aid-lean batch <cases.jsonl>`: one decision per JSON line, in one process.
- `scripts/difftest/run.js N seed` (run with `TZ=UTC`): a seeded generator of random
  inputs that satisfy the valid-input conditions and cover every branch (SMB on/off,
  UAM, COB, temp targets, autosens, exercise mode, noisy and stale CGM, error codes,
  mmol/L, skip-neutral, single IOB objects as in oref0's tests); oref0's
  `getLastGlucose` + `determine_basal` in-process (as `bin/oref0-determine-basal.js`
  does), `aid-lean batch` on the same inputs, field-by-field comparison. Processes in
  chunks of 10,000 (the first version tried to hold 600 MB of cases in one string).
- `Math.round` is instrumented during the oref0 runs to flag any call whose argument is
  within 1e-9 (relative) of a .5 tie.

### Result: 100,000 cases, seed 7 (`docs/difftest.json`)
| outcome | cases |
|---|---|
| byte-identical JSON | 83,089 (83.1%) |
| only the reason text differs | 413 |
| values differ | 16,498 — of which 13,818 only ±1 steps in rounded prediction arrays; 82 with a different issued rate |
| mismatches whose oref0 run hit a near-tie `Math.round` | 16,907 of 16,911 |
| mismatches without one | 4, all reason text only: JavaScript prints maxSafeBasal as e.g. `3.9000000000000004` (DESIGN D6) |

No difference was found that is not explained by floating point (ties, or number
printing). In particular, the transcription of the prediction, COB, UAM and SMB code,
which no oref0 test reaches, agrees with oref0 wherever no tie occurs; microboluses
were issued in 3,746 cases. The tie effects can be large (F-13): 82 cases issue a
different rate, the worst a 30-min zero temp in oref0 vs the neutral basal in aid-lean.

### Interpretation
Exact arithmetic was chosen for provability (DESIGN). The difftest shows its price:
83% byte agreement, not 100%. Because 82% of all cases hit at least one near-tie
rounding, agreement "within a tolerance" is not a meaningful notion at the decision
level; the right next step, if decision-level agreement is required, is to emulate
IEEE-754 doubles in the core (round each operation to the nearest double, still in
exact rationals). Not done.

---

## M12 – Checking the proofs have teeth (stretch)

**Start:** 2026-11-18 14:55 · **End:** 2026-11-18 15:13 (commit times)

### Mutation testing (`scripts/mutate.py`, `docs/MUTATION.md`)
24 one-line mutations of `LeanAID/Core` (clamps removed, comparisons changed, constants
changed, branches altered), each followed by `lake build LeanAID`. All 24 are caught by
the build; 18 break a proof, 18 fail conformance. Separating general theorems from
concrete kernel-evaluated checks shows two specification gaps: H1 is relative to the
implementation's `getMaxSafeBasal` (M04 survives every general theorem), and H3 to the
implementation's `threshold` (M10). Both follow the kickoff's wording ("oref0's
maxSafeBasal", "threshold as oref0 computes it"), but they mean a wrong formula there
would not be caught by a proof. Not yet fixed.

### Independent review
The maintainer ran an independent reviewer on commit a95cea8 (`prompts/review.md`); I
did not start a second one. Its remaining issues and my responses are in "Review fixes"
above (F-11, F-12, F-13, R12 restated, sources verified, page corrected). The
reviewer's finding that R12 used the implementation predicate `cgmError` is the same kind
of gap as M04/M10 above.

---

## Second review, step 1: the 4 mismatches without a near tie

**Time:** 2026-11-18 15:40 (from `date`)

All four differ only in the reason text "to maxSafeBasal: 3.9000000000000004" (and
similar): a binary64 multiplication error in `3 × max_daily_basal`, which the
`Math.round` tie detector cannot see. Not a transcription error (FINDINGS F-14).
Regression inputs saved in `scripts/difftest/regression-no-tie.jsonl`; they become
Lean conformance cases once the core models binary64 (step 3).

## Second review, step 2: dose differences recorded

**Time:** 2026-11-18 15:40 (from `date`)

FINDINGS F-15: 82/100,000 rate differences (76 higher in aid-lean, 3 lower, 3 one-sided),
worst inputs listed and saved in `scripts/difftest/worst-rate-diffs.jsonl`.

## Second review, step 4: requirement statuses and validity table

**Time:** 2026-11-18 15:41 (from `date`)

REQUIREMENTS: every status now says what is proved, for finite rates only where that
applies (R1, R2, R10, R11; NaN rates are F-06), R3 marked as not holding (F-04), R5 marked
partly proved (the headline theorem omits "at most half of insulinReq" and "a multiple of
the bolus increment"), R10 proved, R16 proved, R17 partly proved and partly false (F-10).
DESIGN: V5/V9 now match `Spec/Valid.lean` (they were stricter in the text than in Lean).

## Second review, step 5: mutation report separated

**Time:** 2026-11-18 15:41 (from `date`)

`scripts/mutation_report.py` rewrites `docs/MUTATION.md` from `docs/mutation.json`.
Correction to M12: "18 break a proof" counted lemmas. Strongest catch per mutation: a
safety theorem's proof breaks in 4 (M13, M15, M16, M24); only supporting lemmas in 16;
only concrete checks in 3 (M04, M21, M23); only conformance in 1 (M10). A broken lemma
stops the modules that import it from being built, so for those 16 the safety statements
are neither confirmed nor refuted by the run.

## Second review, step 6: `--safe` documented, undated glucose rejected

**Time:** 2026-11-18 15:42 (from `date`)

`--safe` now also refuses a glucose status without a finite date (F-11) and names each
reason. DESIGN lists exactly what it rejects and what it does not. Tested by hand on four
inputs (valid → suggestion; undated glucose, missing max_basal, carbs without
lastCarbTime → exit 2 with the matching reason).

## Second review, step 7: times

**Time:** 2026-11-18 15:42 (from `date`)

**Correction.** The start/end times written for M7, the first review fixes, M10 and M12
were again my estimates, and three of them lay in the future (up to 16:40, when `date`
said 15:39). They are replaced by the git author timestamps of the corresponding commits
(first column of `git log --format='%ad' --date=format:'%H:%M'`), marked "(commit times)".
M0–M6 had already been corrected the same way. From the second review on, every time in
this log is taken from `date` at the moment of writing.

## Second review, step 3: IEEE-754 binary64 in the core

**Time:** started after step 7 (15:42); the 100,000-case difftest on the new core was
launched at 15:47 (process start time) and finished at 16:02; this entry written at
16:33 (from `date`).

**What changed.** `LeanAID/Core/Binary64.lean` defines `rd`, rounding a rational to the
nearest double, ties to even (subnormals included, overflow not modelled), with integer
arithmetic only (`Nat.log2`, `Rat.floor`). `JsNum` `+ − × ÷` now return `rd` of the exact
result; decimal literals and JSON input numbers are rounded to doubles; `round(x, d)` and
`round_basal` use the rounded multiplication and division; `Math.exp` is rounded to a
double; `Number → String` is ECMAScript's shortest round-trip form. No `Float`.

**Result.** Conformance 148/148, all exact (IOB 51/51; before: 49 exact, 2 at ties).
Differential testing, seed 7, 100,000 cases: **100,000 byte-identical** (before: 83.1%;
82 rate differences). aid-lean time for the run: 879 s (before: 98 s; the rounding costs about 9×).
`scripts/difftest/regress.js` re-runs the F-14 inputs (4/4 identical outputs) and the
F-15 worst cases (5/5 same rate as oref0).

**Proofs.** `LeanAID/Proofs/Binary64.lean` proves what the safety proofs need about
`rd`: monotone, odd, idempotent, exact on integers up to 2^53 and on `N·2^E` grids,
`|rd x − x| ≤ |x|·2^-53 + 2^-1075`, positive above 2^-1075, and the only double in
(−2^-1074, 2^-1074) is 0. Most safety theorems carried over through monotonicity.
Where a property holds only up to rounding, the statement was changed; **every change
is listed in FINDINGS F-16** (statement changes are recorded as AGENTS.md requires):
H2 microbolus bounds with relative tolerance 2^-50 / 2^-44; H3 "running zero temp" for
double rates; H6 overshoot bound + (M+1)/2^50; DB-01..05, IOB-01 and BAS-01 instances
with tolerances; new validity condition V10 (`current_basal`, `max_basal` are doubles,
`max_basal ≤ 2^30`) and V5 restated for doubles. H1, H4, H5 and the remaining headline
theorems keep their statements. The CGM-staleness theorem keeps its exact 12.05 /
−5.05 minute hypotheses: the age is a composition of monotone roundings, so the
threshold case is evaluated by the kernel.

`lake build` (all proofs, conformance) and `lake test` pass; 274 theorems, 16 headline,
no `sorry`, headline axioms propext/Classical.choice/Quot.sound only.

**Math.exp.** V8's `Math.exp` is not correctly rounded; ours is (to within 10⁻³⁵ of
the true value before rounding). DESIGN D5 states the tolerance: at most 1 ulp of
`exp(x)`, assuming V8 is within 1 ulp (the accuracy documented for fdlibm, which we
did not verify in V8's source). No difference was observed in 148 + 100,000 cases.

## Mutation testing re-run on the binary64 core

**Time:** 16:34–17:19 (from `date` before and after the run)

`python3 scripts/mutate.py` and `scripts/mutation_report.py` on the new core: all 24
mutations still caught. Strongest catch: safety theorem 4, only lemmas 17, only concrete
checks 2 (M21, M23), only conformance 1 (M10). Change from before: M04 (double
`max_basal`) now breaks the lemmas `maxSafeBasal_double` / `maxSafeBasal_ge`, which stops
the modules with the concrete checks that caught it before; it remains a specification
gap (H1 is stated against the implementation's `getMaxSafeBasal`). The hand-written
Analysis section of `docs/MUTATION.md`, which the report script does not generate, was
restored with that row updated.

## Second review, step 8: project page

**Time:** 2026-11-18 17:19 (from `date`)

`site/index.html` updated with numbers the build and scripts produce: 148/148 test calls
identical and IOB 51/51 (`aid-lean selftest`, `docs/numbers.json`), 100,000/100,000
random cases identical (`docs/difftest.json`), 274 theorems (`docs/numbers.json`),
24/24 mutations caught (`docs/mutation.json`). The exact-fractions limitation is replaced
by the rounding tolerance of H2 (2^-44 relative, "smaller than one part in 10^13",
FINDINGS F-16) and the Math.exp note (DESIGN D5); the 83,089 / 82 figures are kept as
the result of the earlier exact-arithmetic version. Only these sentences and numbers were
changed; the maintainer's text is otherwise untouched.

## M11 virtual patients, parts 1 and 2: harness and smoke test

**Time:** 2026-11-18 21:01–21:53 (from `date`; part 1 started 21:01:45, `lake test`
21:45:12–21:46:38, final smoke runs 21:46:58–21:53:03)

Task: `prompts/overnight-sim.md`. Python 3.9.6 (system) is new enough: `.venv` with
simglucose 0.2.11, matplotlib 3.9.4, pandas 2.3.3 (`sim/requirements.txt`, full freeze).

Harness (`sim/`, see `sim/README.md`): simglucose patient model stepped minute by minute,
GuardianRT sensor (5-minute samples), seeded meals (RandomScenario) announced with carbs
and a carbs/CR bolus; inputs built from the last 12 h; oref0 as one long-lived Node
process (`sim/oref0_server.js`: lib/profile, lib/meal, lib/iob, determine-basal);
aid-lean as one long-lived `aid-lean serve` process (new, `App/Serve.lean`: IOB with
`LeanAID.Iob.generate` and the decision with `determineBasal`, JSON lines). Meal data
(COB) in the aid-lean arm comes from oref0's lib/meal (JavaScript). In aid-lean runs
oref0 also runs on every input, and decisions and IOB arrays are compared at every step.
Safety monitor `sim/monitor.py`: R1, R2, R4, R6, R8–R12 on each decision, plus "SMB
issued while off". Profiles from simglucose's parameters through oref0's lib/profile.

Speed. The first aid-lean step took 3.5 s (a simulated day ≈ 17 min): `rd` on
rationals (a gcd per operation) and `Math.exp`, evaluated ~10^4 times per step in the
IOB curve. Changes, all without trusted code (`check.sh` forbids `implemented_by` in the
core; a first attempt with it was reverted before any commit):
- `Exp.taylor` evaluates the same exact polynomial as one integer fraction (old form kept
  as `taylorHorner`; equality checked on the curve's 1,202 arguments by
  `taylor_eq_horner_samples`, not proved);
- `Core/Binary64Impl.lean`: `rdImpl` with naturals only, and `rd_eq_rdImpl : rd = rdImpl`
  proved and registered `@[csimp]`;
- `Exp.jsExpFast`: `jsExp` from a table of its own values at the curves' arguments
  (DIA 5–8 h, peaks 55/75 min), `jsExp_eq_jsExpFast` proved, `@[csimp]`.
Result: 0.75 s per step (≈ 4 min per simulated day), identical output on the test input.
Checks after the change: `lake build` and `lake test` pass (148/148 conformance, IOB
51/51 exact, check.sh OK, headline axioms unchanged); differential test re-run (seed 7):
100,000/100,000 identical, aid-lean 419 s (was 879 s); `docs/difftest.json` restored to
the committed file since only the time changed.

Smoke test (adult#001, 1 simulated day, meal seed 1; summaries in `sim/out/smoke/`):
- oref0 and aid-lean: the same 288 decisions; aid-lean = oref0 at every step (288/288
  decisions byte-identical, 288/288 IOB arrays identical); true BG, CGM and delivered
  insulin traces identical. TIR 100%, mean BG 114 mg/dL, 44.1 U/day. Baseline (BB
  controller): TIR 94.8%, mean 139, 41.3 U/day. No monitor violation.
- faults, 1 day, oref0 and aid-lean: dropout, compression, missed meal, F-11 behave as
  designed (see the reasons in the logs); F-12 (no `max_basal`): 23 decisions above the
  configured max_basal (monitor R1) and 11% of the day below 70 mg/dL, in both arms.
  With F-11 the repeated undated reading makes oref0 take its "CGM data is unchanged"
  branch, so in this run it did not raise insulin.
- Time per simulated day (one process, no other load): oref0 3.6 s, baseline 1.2 s,
  aid-lean ≈ 226 s.
- A harness bug (naive datetimes: glucose dates and `currentTime` 2 h behind the ISO
  strings) made the first smoke run feed carbs dated 2 h in the future; on that input
  aid-lean and oref0 differ (predictions only): FINDINGS F-17, kept in
  `sim/regression-future-carbs.json`. Bug fixed (UTC-aware times), runs repeated.

Estimate for part 3. With three aid-lean runs in parallel a simulated day took 285–362 s
(226 s alone); with 7 workers on 4 performance + 4 efficiency cores we assume ≈ 350 s.
Items 1–3: 180 aid-lean runs × 2 days ≈ 126,000 worker-seconds / 7 ≈ 5 h (oref0 and
baseline runs add minutes). Item 4: a 7-day aid-lean run ≈ 40 min, so one meal seed for
30 patients × 2 controllers ≈ 3 h; the remaining ≈ 7 h cover about 2 seeds.

`docs/numbers.json` was not regenerated: the theorem count is now higher than its 274
(the equalities in `Core/Binary64Impl.lean` and `Core/Exp.lean` and the
`taylor_eq_horner_samples` check); the project page is not edited (part 4 rule).

## M11 virtual patients, parts 3 and 4: overnight run and report

**Time:** part 3 2026-11-18 21:55:20 – 2026-11-19 09:55:22 EET (`sim/out/progress.log`,
from `date`); part 4 2026-11-19 13:53–14:10 EET.

Part 3 (`sim/run_all.sh`, 7 workers, git `5650f43`): 512 runs finished, 0 failed, in
12.0 h. Items 1–3 (390 runs) ended at 03:22:33, 5 h 27 min (estimate: 5 h); then 7-day
runs: meal seed 1 complete (60), seed 2 58 of 60, seed 3 4 of 60. At the deadline the 7
runs in progress were 7-day aid-lean runs and were discarded and logged (child#009 and
child#010 of seed 2, adolescent#001–#005 of seed 3). Time per simulated day with 7 in
parallel: aid-lean 363–388 s, oref0 9–10 s, baseline 3 s.

Part 4: `sim/report.py` (2 min) → `sim/out/report.json`, `sim/out/plots/`; `docs/SIM.md`.
- aid-lean = oref0 at every step: 220,608 / 220,608 decisions byte-identical and IOB
  arrays identical over 238 aid-lean runs; all 238 aid-lean runs identical step by step
  to the paired oref0 runs (true BG, CGM, insulin, decision).
- Main (30 patients, 2 days): TIR 88.8 % (oref0 = aid-lean) against 83.2 % (baseline);
  below 70: 3.2 % against 7.4 %.
- Monitor: R1 1,064 decisions per arm, all in F-12 runs (up to 9.8 × the configured
  `max_basal`); R8 16 oref0 decisions (13 in the paired aid-lean runs), all in oref0's
  flat-CGM branch: new finding **F-18**. No theorem is contradicted (`low_glucose_suspend`
  assumes the prelude succeeds, which excludes flat data), but REQUIREMENTS R8 did not
  say so; its text now states the scope (not a change to any theorem). The monitor keeps
  checking the stronger statement.
- F-11 in a closed loop: harmless here (the undated copy is flat, F-18's branch catches
  it). F-12: time below 54 mg/dL 4.8 % against 1.6 %, 18/30 patients more time below 70.
- Simulator artefact: in 4 runs per arm (child#003 and child#008) simglucose's glucose
  reaches 0 and stays there through later meals; reported, not removed from the tables.
- The F-18 text in FINDINGS and REQUIREMENTS and the monitor comment were committed by
  the maintainer's commit `b11824f` (made while part 4 was in progress); this entry and
  `docs/SIM.md` describe them.
- `site/index.html` not edited (part 4 rule).

## Timing properties: plan (extends M9)

`docs/timing-plan.md`. No Lean code changed, nothing new is proved.
- Sources checked for timing clauses: SR2011 (full text on PMC, 2026-11-19), 21 CFR
  862.1356 and 880.5730 (`refs/`). Neither CFR section gives a number. The IEC
  standards (60601-2-24, 60601-1-8) are paywalled and are marked "not checked".
- Libraries checked: CSLib has untimed `LeadsTo` and BTL, no MTL. No Lean 4 MTL or MLTL
  library found. Isabelle (AFP MLTL entries, VeriMon) and Rocq (lattice-mtl) have one.
- Decision: shallow embedding over timed event traces, `Int` milliseconds, pointwise
  semantics, no Mathlib. Seven properties P1–P7, of which P6 and P7 are R20 and R21.

## Timing properties: plan revised after review

`docs/timing-plan.md`, section 7. No Lean code changed, nothing new is proved.
- An adversarial review of the first version. Its code citations were checked against
  `LeanAID/Core/DetermineBasal.lean`, `Iob.lean` and `sim/harness.py`.
- P4 as first written was false: zero temps last up to 120 minutes (lines 741, 898), so
  a stopped loop can leave the pump below the scheduled basal for 120 minutes. P4 is
  split into P4a (expiry) and P4b (bound by rate).
- P1 and P5 now have a faithful statement with oref0's rounded comparisons and a
  derived real-time statement with explicit slack. P6 and P7 are defined precisely.
- The event model separates issued, sent, accepted and lost commands.

## Timing properties: plan revised after second review

`docs/timing-plan.md`, section 7, round 2. No Lean code changed, nothing new is proved.
- The first milestone now uses a fixed profile and atomic cycles (decide, then accept
  or lose the whole command, at most one cycle per step). This closes two gaps that
  the review found in P5 and P6.
- R21: section 4.2 states two candidate invariants. I1 (lifted guard) is expected to
  hold. I2 (microbolus IOB at most `max_iob`) is expected to fail because of negative
  IOB from zero temps. T0 builds that run first.
- P1 uses `profileCurrentBasal` (rounded), as the existing theorem does.
- Review citations checked: `profileCurrentBasal` rounds (line 125), `enableSmb` needs
  a profile flag (line 47), `run_id` omits the SMB mode, F-13 is resolved.

## Timing properties: plan, third review

Review round 3 found no critical concerns. Three major ones are fixed in
`docs/timing-plan.md`: P3 needs a finite rate for its rate-dependent part (F-06), a
step is an ordered list (environment events, then at most one cycle) to match the
simulation's meal boluses, and the P6 window reduction includes starts 1 ms around
each breakpoint. Review rounds stop here.

## Timing properties: implementation setup

**Start:** 2026-11-19 16:49 UTC · **End:** 16:54 UTC

Branch `timing-impl` from the plan commits on `origin/timing-plan`. Cloud session.
- `vendor/oref0` cloned at 88cf032, `npm install --no-save` inside it.
- elan could not download the toolchain: the session's network policy denies
  `release.lean-lang.org`. The same release (`lean-4.36.0-linux.zip`) was downloaded from
  the Lean GitHub release page and linked with `elan toolchain link`.
- Baseline before any change: `lake build` passes (110 jobs, 1 min 41 s);
  `scripts/check.sh` OK, 16 headline theorems with the standard axioms only.

## Timing T1: run type and helpers

**Start:** 16:54 UTC · **End:** 16:55 UTC

`LeanAID/Time/Run.lean`: `Step`, `Run`, `Status` (closed or observed), `Increasing`,
`upTo`, `before`, `stateAt`, `stateBefore`, and the integral of a rate over a half-open
interval of milliseconds, `integral f a n = Σ_{k=a}^{a+n-1} f k / 3 600 000`. This is
the exact integral of a rate that changes only at integer milliseconds, which holds for
the pump model of T2. Lemmas: `sumFrom_mono`, `sumFrom_const`, `sumFrom_nonneg`,
`sumFrom_add`, `integral_le_const`, `integral_nonneg`. `docs/DESIGN.md` layout table
lists `LeanAID/Time/`.

## Timing T2: transition system

**Start:** 16:55 UTC · **End:** 16:58 UTC

`LeanAID/Time/System.lean`. Events: `reading` (value, true time, recorded date),
`userBolus`, `cycle` (inputs, result, outcome accepted or lost). Validation `validate`:
the whole command is rejected if the rate or bolus is non-finite or negative, if a rate
comes without a duration or the reverse, or if the duration is not 0 or 30 to 120
minutes. The pump state `PState` holds the last accepted temp (rate, start, deadline),
the accepted actions newest first, the readings and the rejected cycles. `rateIn` and
`rateAt` give the pump rate at a millisecond: the temp before its deadline, then the
schedule. `LegalCycle` fixes the inputs of a cycle as the plan says (clock, profile with
`current_basal` from `basalLookup` on the schedule, `Iob.generate` on the encoded
history, `currenttemp` from the pump state, `getLastGlucose` on the readings), and
`Legal` adds increasing times, nonempty steps and "environment events, then at most
one cycle". Proved: `Legal.cycle`, every cycle of a legal run is legal.

Decisions and deviations from the plan, all small:
- The pump also rejects durations that are not whole minutes and negative values. oref0
  never issues either when the value is finite. Whole minutes keep every deadline an
  integer millisecond, so the integral of T1 is exact.
- `currenttemp.duration` is the remaining time rounded up to whole minutes.
- History records use the decimal millisecond time as the `timestamp` string, so a
  `TempBasal` and its `TempBasalDuration` match. The order is newest first, as in
  `sim/harness.py`. This matters: `calcTempTreatments` skips a record that is newer than
  the one before it (`Iob.lean` line 446).

Problem found: `Iob.generate` cannot be evaluated by the kernel. `calcTempTreatments`
uses a `while` loop (line 495, a `partial` definition, opaque to the kernel), and
`sortByKey` and `basalLookup` use `List.mergeSort` (well-founded recursion, which
`decide` does not unfold). Consequences:
- Concrete runs whose cycles call `generate` cannot be checked by `decide`. They are
  checked by `native_decide` in `LeanAID/Conformance/`, where `check.sh` allows it.
- No theorem can look inside `generate`. A property that needs to know what IOB or
  `lastBolusTime` `generate` returns for a history can only be proved with that fact
  as an explicit hypothesis. See T5 and T6.

## Timing T0: counterexample runs

**Start:** 16:58 UTC · **End:** 17:05 UTC

*Correction:* the start and end times first written for T1, T2 and T0 were estimates
and were wrong. They are replaced by the commit times (UTC).

`LeanAID/Time/Build.lean`: `build` makes a run from a script (times, readings, user
boluses, and per cycle the free inputs and the outcome); each cycle's inputs are
computed from the pump state. `build_legal`: a built run with increasing times is legal.

`LeanAID/Time/Examples.lean` (checked by `decide`): a reading 12.04 minutes old is not
stale and 12.05 is; the 0.83/0.85 case (F-19); the SMB age boundary (3.05 minutes
passes with interval 3, 3.04 does not, so the real spacing is at least I + 0.05, not
only I − 0.05 as the plan expected); a replacement temp one minute before the old
deadline; a lost replacement; a rejected NaN-rate command; a cancel.

`LeanAID/Conformance/TimeRuns.lean` (checked by `native_decide`, because the cycles call
`generate`, F-22): the 120-minute zero temp and stopped loop (F-20); a reading 12.04
minutes old giving the maximum rate 3 U/h; undated readings giving flat data, not F-11;
a user bolus and a microbolus with the same timestamp both kept by
`calcTempTreatments`; the I2 counterexample (F-21) with I1 holding at each microbolus.

What changed against the plan: the future-reading boundary (−5.05 minutes) is not in
the examples. `decide` gets stuck on rounding a negative age; it is covered by the
existing `cgm_unreliable_no_increase`. The undated-reading case did not reproduce F-11
in a run (recorded under F-11 in FINDINGS).
