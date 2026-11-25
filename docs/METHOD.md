# How the work was done

LeanAID is an experiment in **agentic formal verification**: can an AI agent take real,
deployed, safety-critical software, translate it into a proof assistant, prove safety
properties about it, and show that the translation still behaves like the original? This
page describes how the agents were set up, what the people did, and how the results were
checked.

## Who did what

- **The agent** was Claude Opus 5.5 in Claude Code, running on a laptop. It wrote the Lean
  code, the proofs, the test scripts, the virtual-patient harness and most of the
  documentation, and ran every test.
- **The maintainer** at the Beneficial AI Foundation set the goal and the rules, wrote the
  task descriptions given to the agent, answered its questions, approved anything that
  needed approval (installing packages, network access), and decided what was published. A
  second Claude Code session helped the maintainer draft the task descriptions and review
  the agents' work.
- **Independent reviewers** were separate agent sessions with no access to the working
  folder (see below).

## The task

The first task description fixed the inputs and the rules, and split the work into
milestones:

- **Fixed inputs**: oref0 at commit `88cf032` (release 0.7.1), never modified; Lean 4.36.0;
  Node for running oref0 as the reference; the FDA-authored hazard analysis (2010), the
  generic safety requirements for insulin pump software (2011), and 21 CFR 862.1356 and
  880.5730 as the sources of safety requirements.
- **Design rules**:
  - translate function by function, keeping oref0's names and structure, with a pointer to
    the JavaScript file and lines;
  - reproduce oref0's quirks and record them; do not improve the algorithm;
  - no floating point in the translated core;
  - a pure core with a single entry point;
  - no `sorry`, `partial`, `unsafe`, `native_decide` (outside the conformance checks) or
    new axioms;
  - state each requirement in plain English first, then in Lean, about the translated
    functions themselves.
- **Milestones**, with a minimum result (M0–M7) to reach before any further work:

| | milestone |
|---|---|
| M0 | setup: pinned oref0, Lake project, `scripts/check.sh` |
| M1 | inventory of oref0's tests |
| M2 | safety requirements, traced to the hazard analysis and the regulations |
| M3 | translation |
| M4 | conformance: oref0's test cases replayed in Lean |
| M5 | safety theorems |
| M6 | oref0's tests generalized to theorems |
| M7 | the `aid-lean` executable |
| later | differential testing, mutation testing, virtual patients, coverage |

Later task descriptions covered the virtual-patient experiment, the reproduction scripts
for the findings, and branch coverage. Each said what to do, what was out of bounds, and
when to stop and ask.

## The rules every session followed

These rules applied to every agent session (summarized):

- **Git.** Commit locally after each milestone. Never push: the maintainer reviews and
  pushes. Never rewrite existing history.
- **Honesty.**
  - Never claim something is proved unless `lake build` checks it with no `sorry`.
  - Never weaken a theorem statement to make a proof go through without recording it in
    `docs/FINDINGS.md`.
  - Never edit oref0's sources or tests to make the Lean code agree.
  - The project page may only state results that the build and test scripts actually
    produce, and must mark anything else as planned.
- **Safety.** This is a research artifact; nothing may be presented as fit for dosing
  insulin. Download or run nothing except the pinned oref0, Lean and its libraries, the npm
  packages oref0 declares, and the named Python packages.

## How the results are checked

The agent's word is not taken for anything. Every claim is checked by a program:

- **Proofs** are checked by Lean's kernel. `scripts/check.sh` rejects `sorry`, forbidden
  constructs and new axioms, and prints the axioms each headline theorem depends on;
  continuous integration builds everything and flags any new `sorry`.
- **Faithfulness** of the translation is checked by running both programs on the same
  inputs (oref0's own tests, 200,000 random cases, 30 virtual patients) and comparing the
  outputs, and by branch coverage of oref0 (`docs/COVERAGE.md`).
- **Whether the proofs say anything** is checked by mutation testing: 24 deliberate bugs
  planted in the Lean code, each of which must break a proof or a test
  (`docs/MUTATION.md`).
- **Numbers on the project page** come from files written by the scripts
  (`docs/numbers.json`, `docs/difftest.json`, `docs/iobtest.json`, `docs/coverage.json`,
  `sim/out/report.json`).

## Independent reviews

The maintainer ran a separate agent as a reviewer. It worked on its own clone, could not see
or change the working folder, and was told to report, not fix. Its report, and a second round
of review that followed, led to changes:

- It recognized that undated glucose readings, which the building agent had recorded as a
  quirk of oref0, are a safety problem (F-11), and it found that a missing maximum-basal
  setting switches the rate cap off (F-12).
- It showed that computing with exact fractions, as the agent had done, can differ from
  JavaScript's rounded arithmetic (F-13). In the second round, the random cases that differed
  from oref0 were traced to the same cause (F-15). The core was then rewritten to round every
  operation exactly as JavaScript does, and all 100,000 cases became identical.
- The second round asked for requirement statuses, the mutation report and the `--safe` option to be
  stated precisely.

## Timeline

| when | what |
|---|---|
| 18 November, 12:05–14:30 | minimum result, M0 to M7, in one agent session |
| 18 November, afternoon | first review and fixes; 100,000-case differential test; mutation testing; second review; JavaScript rounding in the core |
| 18–19 November, 21:55–09:55 | virtual patients: 512 closed-loop runs, unattended overnight |
| 19–23 November | runs of the loop over many cycles; reproduction scripts for the findings |
| 23 November | branch coverage and the 100,000-case pump-history test |

## What went wrong, and how it was caught

- **The agent's own translation had errors.** The pump-history test found two places where
  the Lean code did not follow oref0 (F-25). They were fixed before anything was proved
  about that code. This is why the tests against the original matter as much as the proofs.
- **Exact arithmetic is not faithful arithmetic.** Computing exactly changed some doses
  compared with oref0 (F-15). Modelling JavaScript's rounding fixed it, and some theorem
  statements then had to allow tiny rounding errors. Every changed statement is listed
  (F-16).
- **Some proofs were weaker than they looked.** Mutation testing showed that two safety
  theorems are stated in terms of oref0's own computed limits, so a wrong formula for the
  limit would not break them (`docs/MUTATION.md`).
- **A proof attempt found a real bug.** The proof that the dose never exceeds the maximum
  rate failed, and the counterexample (0.83 U/h rounded up to 0.85 U/h) is finding F-04.
