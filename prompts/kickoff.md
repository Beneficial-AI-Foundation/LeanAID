# LeanAID kickoff prompt

You are building **LeanAID**: a Lean 4 version of the OpenAPS **oref0** insulin dosing
algorithm, with machine-checked proofs of its safety properties, compiled to a native
binary that behaves like the original. The purpose is to show that an agent can
formally verify real, deployed, safety-critical software ("vericoding").

Read `AGENTS.md` first and follow it throughout. The current project page is
`site/index.html`; it describes the plan you are now carrying out.

Work through the milestones below in order. The **minimum result** is milestones
M0–M7. Everything after that is the **stretch result**. Reach the minimum before
starting any stretch work. Commit after each milestone.

---

## Fixed inputs

- **oref0**: `https://github.com/openaps/oref0`, branch `master`, commit
  `88cf032aa74ff25f69464a7d9cd601ee3940c0b3` (release 0.7.1, MIT licence). Clone it
  into `vendor/oref0` at exactly that commit. Do not modify it.
- **Lean**: toolchain `leanprover/lean4:v4.36.0` (installed). Write it to
  `lean-toolchain`.
- **Node**: v24 (installed) for running oref0 as the reference.
- **Python**: 3.9 is installed. If simglucose needs newer, create a project venv with
  `uv` or `python3 -m venv` in `.venv/` (git-ignored).
- **Regulatory and safety sources** (cite these; download open-access copies into
  `refs/` where possible):
  - Y. Zhang, P. L. Jones, R. Jetley, *A hazard analysis for a generic insulin
    infusion pump*, J. Diabetes Sci. Technol. 4(2):263–283, 2010. PMID 20307387.
  - Y. Zhang, R. Jetley, P. L. Jones, A. Ray, *Generic safety requirements for
    developing safe insulin pump software*, J. Diabetes Sci. Technol. 5(6):1403–1419,
    2011. PMID 22226258.
  - 21 CFR 862.1356 (interoperable automated glycemic controller), in particular
    (b)(2)(iii) hazard traceability and (b)(3)(iv) safe operation on out-of-bounds data.
  - 21 CFR 880.5730 (alternate controller enabled infusion pump).

## Scope

In scope: the dose decision of oref0, meaning `lib/determine-basal/determine-basal.js`
and what it depends on for a single decision (insulin on board from `lib/iob/`, carbs
on board from `lib/meal/`, glucose status, basal rounding, profile handling, and the
safety limits). Autosens is an input (`sensitivityRatio`), not computed.

Out of scope: autotune, the autosens calculation, pump and CGM drivers, Nightscout,
shell scripts.

## Design rules

1. **Faithful transcription.** Translate oref0 function by function, keeping its names
   (in Lean style) and structure, with a comment pointing to the JS file and line
   range for each function. When oref0 has a quirk, reproduce it and note it in
   `docs/FINDINGS.md`. Do not "improve" the algorithm.
2. **Numbers.** No `Float` anywhere in the verified core. Use exact rationals or
   fixed-point integers; choose one, justify it in `docs/DESIGN.md`. Where oref0's
   output depends on JavaScript rounding (`Math.round`, `toFixed`, `round_basal`),
   implement that rounding exactly and prove its key properties. oref0's exponential
   insulin curve uses `Math.exp`: implement a rational approximation and prove an
   error bound for it.
3. **Pure core.** The core is pure functions only. Expose one entry point
   `step : Profile → Inputs → Result` (or close to it) and mark it
   `@[export aid_step]` with plain types, so it can later run on seL4. JSON parsing,
   command-line handling and I/O live in a separate shell.
4. **Forbidden in the core:** `sorry`, `partial`, `unsafe`, `@[extern]`,
   `implemented_by`, `native_decide` (allowed only in conformance files), and new
   `axiom` declarations.
5. **Libraries.** The core and the binary depend only on Lean core and, if needed,
   Batteries. Mathlib may be used in proof and specification modules only.
6. **Theorem statements before proofs.** For each requirement, write the statement
   first in plain English (in `docs/REQUIREMENTS.md`) and then in Lean. Statements must
   talk about the transcribed oref0 functions, not about a wrapper added later.

## Suggested layout

```
lean-toolchain, lakefile.lean
LeanAID/Core/…        transcription of oref0 (pure)
LeanAID/Spec/…        mathematical specification (insulin on board, safety envelope)
LeanAID/Proofs/…      theorems
LeanAID/Conformance/… oref0 test cases as Lean data and checks
App/Main.lean         aid-lean command-line shell
scripts/              differential testing, mutation testing, report generation
sim/                  simglucose harness
docs/                 DESIGN, REQUIREMENTS, TRACEABILITY, FINDINGS, LOG
vendor/oref0          pinned reference (git-ignored or submodule; do not edit)
refs/                 downloaded sources
```

---

## Milestones

### M0 – Setup
Lake project builds; `vendor/oref0` at the pinned commit; oref0's own tests run under
Node (`npm install` then its mocha tests) and their results are recorded in `docs/LOG.md`.
CI-style check script `scripts/check.sh` that fails on any forbidden construct and
prints `#print axioms` for every headline theorem.

### M1 – Test inventory
Extract every test in `tests/determine-basal.test.js` (70) and `tests/iob.test.js` (26),
plus the small test files that touch the in-scope code. For each, record in
`docs/TESTS.md`: name, inputs, expected output, and a first classification:
**A** generalises to a universal property, **B** generalises to a directional property,
**C** only meaningful as a concrete check.

### M2 – Requirements and traceability
From the sources above, write `docs/REQUIREMENTS.md`: numbered requirements in plain
English, each citing the hazard or regulation clause it comes from. Mark each as
*to prove*, *to test*, or *out of scope (reason)*. Start `docs/TRACEABILITY.md`:
source → requirement → theorem → test or simulation scenario.

### M3 – Transcription
Transcribe the in-scope oref0 code into `LeanAID/Core`. It must compile with no
forbidden constructs.

### M4 – Conformance
Encode every oref0 test from M1 as Lean data and show the Lean implementation produces
the expected result, by `decide` where possible, otherwise `native_decide` in
`LeanAID/Conformance`. Target: all tests pass. Any failure is a transcription bug to
fix, or a documented finding if oref0's test is itself inconsistent.

### M5 – Safety envelope (headline theorems)
Prove, for every valid input:
- the temp basal rate is between 0 and oref0's `maxSafeBasal`
  (min of `max_basal`, `max_daily_safety_multiplier × max daily basal`,
  `current_basal_safety_multiplier × current basal`);
- any microbolus respects oref0's limits and never takes insulin on board above `max_iob`;
- when glucose is below oref0's threshold (as oref0 computes it) and not rising, the
  rate is zero and no microbolus is given;
- with insulin on board at or above `max_iob`, the rate does not exceed the scheduled basal;
- invalid input, stale or error-coded glucose leads to an error or no increase in
  insulin, never more;
- basal rounding never pushes a rate above a limit.
State exactly what "valid input" means and justify it. If oref0 does not satisfy one of
these, do not weaken silently: record a finding with a concrete counterexample input,
then prove the strongest true version.

### M6 – Tests lifted to theorems
For every class A and B test, prove the general theorem it is an instance of, and
derive the original test as a corollary. Produce `docs/TESTS.md` columns: test →
theorem name → status. Tests that would not generalise go to `docs/FINDINGS.md` with
the reason.

### M7 – Binary
`lake build` produces `aid-lean` with:
- `aid-lean determine-basal <iob.json> <currenttemp.json> <glucose.json> <profile.json> [<autosens.json>] [<meal.json>]`
  with the same inputs and the same JSON output fields as `oref0-determine-basal`;
- `aid-lean selftest`, which reruns the conformance cases and reports N/N.
`lake test` runs conformance and the checks in `scripts/check.sh`.
Update `site/index.html` with the real numbers so far (see "Project page" below).
**This is the minimum result.**

### M8 – Insulin on board against the specification (stretch)
Define insulin on board mathematically in `LeanAID/Spec` (dose history combined with the
insulin activity curve) and prove the implementation equals it, or is within the proved
error bound for the exponential curve. Prove: never negative for non-negative doses,
non-increasing without new doses, zero after the duration of insulin action, additive
over doses, and unaffected by suspended periods.

### M9 – Properties over time (stretch)
Model a pump that executes commands, and a run as a list of 5-minute steps. Prove for
any input sequence: insulin delivered in any window stays below the bound implied by
the limits, and repeated cycles never stack insulin on board above `max_iob`.

### M10 – Differential testing (stretch)
`scripts/difftest`: generate many random valid inputs (at least 100,000), run both Node
oref0 and `aid-lean`, compare outputs exactly or within a stated tolerance, and report
any differences with the input that caused them.

### M11 – Virtual patients (stretch)
`sim/`: closed loop with `simglucose` (install from PyPI in `.venv`). Each 5 minutes,
build oref0's inputs from the simulated history, call `aid-lean`, apply the result.
Run all built-in virtual patients over at least 2 days, once with `aid-lean` and once
with Node oref0. Report time in range (70–180 mg/dL), time below 70 and 54, and plots.
Add fault-injection runs: sensor dropout, compression low, missed meal announcement.
Note in the report that simglucose is an open reimplementation of the 2008 UVA/Padova
model, not FDA-accepted evidence.

### M12 – Checking the proofs have teeth (stretch)
- `scripts/mutate`: apply at least 20 small mutations to the core (remove a clamp,
  flip a comparison, change a constant, drop a branch) and record which theorems
  break for each. A mutation that breaks no theorem and passes conformance is a gap in
  the specification; list it.
- Review: start a fresh reviewer session or subagent that reads only
  `docs/REQUIREMENTS.md` and the Lean theorem statements (not the proofs), and reports
  any statement that is weaker than its requirement, vacuous, or restates the
  implementation. Record its report and your responses in `docs/LOG.md`.

---

## Project page

At M7 and at the end, update `site/index.html`:
- Replace planned numbers with real ones, ideally generated by a script from the build
  (`scripts/report`): tests lifted, theorems, axioms, conformance N/N.
- Fill the test → theorem table with real theorem names and statuses.
- Add a findings section, the traceability table, and (if done) simulator plots.
- Keep the "Assumptions and limits" section accurate. Keep "Research artifact. Not for
  dosing insulin."
Keep the existing style. Do not push.

## Experiment log

Keep `docs/LOG.md` throughout: for each milestone, start and end time, what was hard,
proof attempts that failed and why, decisions taken, and any point where you needed to
change a plan. This log is a main output of the experiment.

## When you finish

Write `docs/REPORT.md`: what was achieved per milestone, headline numbers, findings,
what remains, and the exact commands to reproduce everything. Then stop.
