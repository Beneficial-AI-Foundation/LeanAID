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

**Start:** 2026-11-18 14:22 · **End:** 2026-11-18 14:45

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

**Start:** 2026-11-18 14:50 · **End:** 2026-11-18 15:25

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

**Start:** 2026-11-18 14:50 (pilot) · **End:** 2026-11-18 15:45

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

**Start:** 2026-11-18 15:45 · **End:** 2026-11-18 16:40

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
