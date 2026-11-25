# LeanAID: oref0 in Lean 4

**Research artifact. Not a medical device. Nothing here may be used to dose insulin.**

[oref0](https://github.com/openaps/oref0) is the open-source algorithm that decides insulin
doses in do-it-yourself automated insulin delivery systems (OpenAPS, and the dosing logic of
AndroidAPS, Trio and iAPS). It is written in JavaScript and has never been reviewed by a
regulator.

This repository contains:

1. **A translation of oref0 0.7.1 into Lean 4**, function by function: the dose decision
   (`determine-basal`), the temp-basal cap and rounding, insulin on board, the basal schedule,
   the glucose status and the meal history. Arithmetic follows JavaScript exactly: every
   operation is computed on rationals and rounded to the nearest IEEE-754 double, with
   JavaScript's NaN behaviour. The core uses no `Float`.
2. **A native executable, `aid-lean`**, compiled from the same Lean code through Lean's C
   backend. `aid-lean determine-basal` takes the same files and prints the same JSON as
   `oref0-determine-basal`, so it can replace it.
3. **Tests against the original**, on the same inputs:
   - oref0's own test cases: 148 of 148 identical;
   - 100,000 random dose decisions: 100,000 identical, output byte for byte;
   - 100,000 random pump histories through insulin on board, meal history and the basal
     schedule: 100,000 identical;
   - **branch coverage**: every branch of the translated oref0 files is taken by at least one
     of these comparisons, except 10 shown unreachable (with the lines that prove it) and one
     used only by code that is not translated ([docs/COVERAGE.md](docs/COVERAGE.md));
   - **virtual patients**: 30 simulated patients (simglucose), 512 closed-loop runs of 2 to 7
     days; in the runs driven by `aid-lean`, all 220,608 decisions are identical to oref0's
     ([docs/SIM.md](docs/SIM.md)).
4. **Machine-checked proofs**: 314 theorems, no `sorry`, standard axioms only. They include
   safety rules traced to FDA research on insulin pumps (never above the maximum rate, no
   insulin when glucose is low, no extra insulin at the insulin-on-board limit, bad sensor
   data never adds insulin), and 52 of oref0's unit tests generalized to every valid input.
5. **Findings in oref0**, each reproduced by running the original
   ([docs/FINDINGS.md](docs/FINDINGS.md)). The main ones: a glucose reading with no date is
   never treated as stale (F-11); a missing maximum-basal setting switches the rate cap off
   (F-12); rounding after capping can exceed the cap by half a pump step (F-04); a long temp
   basal crossing a schedule change or midnight can lose part of its insulin in the
   insulin-on-board calculation (F-24).

The work was carried out by an AI agent and checked by Lean: a proof counts only if `lake
build` accepts it. How the agents were set up, what people did, and how the results were
checked: [docs/METHOD.md](docs/METHOD.md).

Project page: <https://beneficial-ai-foundation.github.io/LeanAID/>

## Layout

| path | contents |
|---|---|
| `LeanAID/Core/` | the translation of oref0 (JavaScript numbers, determine-basal, IOB, meal history, basal schedule) |
| `LeanAID/Proofs/` | safety theorems and oref0's tests as general theorems |
| `LeanAID/Conformance/` | oref0's test cases replayed in Lean |
| `LeanAID/Time/` | a model of the loop over many cycles, and theorems about runs |
| `LeanAID/Fixed/` | the corrected version: fixes for F-04, F-11, F-12, F-23, F-24, with proofs that nothing else changed ([docs/FIXED.md](docs/FIXED.md)) |
| `App/` | the `aid-lean` executable |
| `scripts/difftest/` | differential tests against oref0 |
| `scripts/coverage/` | branch coverage of oref0 |
| `scripts/findings/` | one reproduction script per main finding |
| `sim/` | virtual-patient harness (simglucose) |
| `docs/` | design, requirements and traceability, findings, coverage, simulation results |
| `site/` | the project page |

## Build and check

Prerequisites: [elan](https://github.com/leanprover/elan) (the Lean version is in
`lean-toolchain`).

```bash
lake build                         # the translation, all proofs, the conformance checks
lake test                          # build + aid-lean selftest + scripts/check.sh
.lake/build/bin/aid-lean selftest  # replays oref0's test cases
```

## Compare with oref0

Needs Node 24 and oref0 at the pinned commit in `vendor/oref0`:

```bash
git clone https://github.com/openaps/oref0 vendor/oref0
git -C vendor/oref0 checkout 88cf032aa74ff25f69464a7d9cd601ee3940c0b3
(cd vendor/oref0 && npm install --no-save)

bash scripts/check.sh                             # forbidden constructs, axioms, findings, targeted cases
TZ=UTC node scripts/difftest/run.js 100000 7      # random dose decisions
TZ=UTC node scripts/difftest/iob.js 100000 1      # random pump histories (hours of CPU time)
bash scripts/coverage/run.sh                      # branch coverage (about 50 minutes)
node scripts/findings/run.js                      # reproduce F-04, F-11, F-12 on oref0
python3 scripts/mutate.py                         # mutation testing
node scripts/report.js                            # docs/numbers.json
```

One decision, as `oref0-determine-basal`:

```bash
.lake/build/bin/aid-lean determine-basal iob.json currenttemp.json glucose.json profile.json \
  --auto-sens autosens.json --meal meal.json [--microbolus] [--currentTime T] [--safe]
```

`--safe` refuses inputs with an undated glucose reading, a missing maximum-basal setting or
carbs without a meal time. Without it, `aid-lean` decides exactly as oref0 does, findings
included.

## Limits

- The proofs are about what the algorithm decides, not about a patient's glucose.
- They assume consistent settings (for example a maximum rate at least the scheduled rate).
- Carbs on board (`lib/meal/total.js`, `cob.js`) are not translated; they are an input, as
  in oref0's command-line tool.
- The conformance checks use `native_decide` and so trust Lean's compiler; the safety
  theorems are checked by the kernel. The executable also trusts the C compiler.
- The virtual patients are simglucose's (an open reimplementation of the 2008 UVA/Padova
  simulator), which is not FDA-accepted evidence.

## Licence

MIT, Copyright (c) 2026 Beneficial AI Foundation (`LICENSE`). The translation and the
captured test data are derived from oref0, Copyright (c) 2015-2019 OpenAPS Contributors,
also under the MIT licence; see `NOTICE.md`.
