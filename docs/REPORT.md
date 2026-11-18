# LeanAID report

A Lean 4 transcription of the OpenAPS oref0 dose decision (oref0 0.7.1, commit
88cf032), with machine-checked safety theorems, a native binary, conformance and
differential testing against the original JavaScript. One agent session, 2026-11-18;
the full experiment log is `docs/LOG.md`.

**Research artifact. Not for dosing insulin.**

## Headline numbers (`docs/numbers.json`, `docs/difftest.json`, `docs/mutation.json`)

| | |
|---|---|
| oref0 test blocks inventoried | 116 (70 determine-basal, 26 iob, 20 others); classes A 48, B 11, C 33, disabled 24 |
| class A/B tests proved as instances of general theorems | 52 of 59 |
| theorems in `LeanAID/Proofs` | 220 (16 headline), no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound` |
| conformance on every in-scope call of oref0's tests | 148/148 (146 exact, 2 IOB values at a rounding tie) |
| differential testing, 100,000 random valid inputs | 83.1% byte-identical; every difference traced to floating-point rounding; no transcription error found |
| mutation testing | 24 mutations, all caught by the build. Strongest catch: a safety theorem's proof breaks in 4; only a supporting lemma breaks in 16 (downstream safety modules are then not built, so this does not show a safety property is violated); only concrete checks in 3; only conformance in 1. Specification gaps: H1 and H3 are relative to oref0's own maxSafeBasal and threshold |
| binary | `aid-lean determine-basal` (same CLI and JSON as `oref0-determine-basal`), `aid-lean selftest`, `aid-lean batch` |

## Per milestone

| milestone | status |
|---|---|
| M0 setup | done. oref0 pinned; its suite: 234 pass, 10 fail (profile tests broken upstream, shell/syntax tests platform-dependent); all in-scope tests pass |
| M1 test inventory | done. `docs/TESTS.md` |
| M2 requirements, traceability | done. 23 requirements, each traced to HA2010/SR2011/21 CFR clauses (IDs verified against the texts) |
| M3 transcription | **done except carbs on board**: determine-basal, setTempBasal, round_basal, IOB (calculate/total/history/index), basal lookup, glucose-get-last, meal history. Not transcribed: `lib/meal/total.js`, `lib/determine-basal/cob.js` (COB calculation; an input of the decision, as in the CLI) |
| M4 conformance | done. 148/148 |
| M5 safety envelope | done, with findings: H1 rate ≤ round_basal(maxSafeBasal) (F-04: can exceed maxSafeBasal by ≤ half an increment); H2 microbolus limits; H3 low glucose suspend; H4 IOB ≥ max_iob; H5 bad/missing data (dated readings only, F-11); H6 rounding. R4 (durations) not proved |
| M6 tests lifted | 52/59; the 7 others explained in FINDINGS (3 because the obvious general rule is false) |
| M7 binary | done; `lake test` passes |
| M8 IOB vs specification | not done. Found F-10 (bilinear IOB negative for a positive dose). The `exp` error bound is argued, not proved |
| M9 properties over time | not done |
| M10 differential testing | done (see above) |
| M11 virtual patients | not done |
| M12 mutation testing, review | done. `docs/MUTATION.md`: all 24 caught; gaps: H1 and H3 are stated relative to the implementation's maxSafeBasal and threshold. Independent review run by the maintainer; responses in LOG "Review fixes" |

## Findings (details: `docs/FINDINGS.md`)

- **F-04** Rounding after clamping lets the temp basal exceed `maxSafeBasal` by up to half
  a pump increment (0.83 → 0.85 U/h; also seen in random inputs: 4.44 → 4.45).
- **F-11** A glucose reading without a date is never stale: BG 250 rising → maximum rate
  3.5 U/h, however old the reading.
- **F-12** Missing `max_basal` or `max_daily_basal` makes maxSafeBasal NaN and disables
  the clamp: 5.9 U/h for a 0.9 U/h basal.
- **F-06** Carbs without `lastCarbTime` → `rate: null` (NaN) for 30 min.
- **F-05** The SMB low temp bypasses the clamp (safe only while the adjusted basal is
  within maxSafeBasal).
- **F-10** The bilinear IOB curve is negative just before DIA.
- **F-13** Exact vs floating-point results differ at ties, and a tie can flip a decision
  (a 30-min zero temp in oref0 vs the neutral basal here).
- **F-01** oref0's tests never reach predictions, COB, UAM or SMB; F-02/03/07/08 other
  test-suite issues; Q1–Q10 reproduced quirks.

## What remains

1. Transcribe COB (`meal/total.js`, `cob.js`), including its wall-clock dependence.
2. Prove R4 (durations), the `exp` error bound (needs Mathlib's `Real.exp` in a Spec
   module), IOB against a specification (M8), properties over time (M9).
3. Decision-level agreement with oref0: emulate IEEE-754 doubles in the core.
4. Virtual-patient simulation (M11).
5. Generalise DB-17/35/39 with the correct hypotheses.
6. Close the mutation gaps: state the H1 ceiling and the H3 threshold independently of the implementation.

## Reproduce

```bash
# prerequisites: elan (Lean 4.36.0 from lean-toolchain), Node 24
git clone https://github.com/openaps/oref0 vendor/oref0
git -C vendor/oref0 checkout 88cf032aa74ff25f69464a7d9cd601ee3940c0b3
(cd vendor/oref0 && npm install --no-save)

lake build                      # transcription, all proofs, conformance checks
lake test                       # build + aid-lean selftest + scripts/check.sh
bash scripts/check.sh           # forbidden constructs, #print axioms of headline theorems
.lake/build/bin/aid-lean selftest

# regenerate test data and theorems
bash scripts/capture/run.sh     # oref0's tests under Node with a capture hook
node scripts/inventory.js && node scripts/tests_md.js
node scripts/gen_conformance.js && node scripts/gen_test_theorems.js

TZ=UTC node scripts/difftest/run.js 100000 7     # differential testing
python3 scripts/mutate.py                        # mutation testing
node scripts/report.js                           # docs/numbers.json

# one decision, as oref0-determine-basal
.lake/build/bin/aid-lean determine-basal iob.json currenttemp.json glucose.json profile.json \
  --auto-sens autosens.json --meal meal.json [--microbolus] [--currentTime T] [--safe]
```
