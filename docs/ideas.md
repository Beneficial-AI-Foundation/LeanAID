# Ideas for later

Status: ideas only. Nothing here is planned, built or checked.

## 1. The T2 model in Isabelle, with Munta and metric temporal logics

Written 2026-11-19, from the discussion that led to `docs/uppaal-plan.md`.

The idea is to translate the Lean model to Isabelle/HOL and to reason about runs
there. Isabelle has tools for timed and metric properties that Lean does not have:

- Munta: a timed-automata model checker that is verified in Isabelle/HOL, with a
  formal semantics of networks of timed automata,
- the AFP entries on metric first-order temporal logic (MFOTL) and metric first-order
  dynamic logic (MFODL), with the verified monitors VeriMon and the optimized
  MFODL monitor,
- the AFP entry `Mission_Time_LTL` (MLTL, discrete time with bounded intervals).

Possible results:

- a proved link between the T2 model and its timed-automata abstraction (level 3 of
  `docs/uppaal-plan.md` section 5): an abstraction function and a simulation proof,
  both in one logic,
- the timing properties of `docs/timing-plan.md` section 4 as MFOTL formulas, with a
  verified monitor for logs from `sim/` (a replacement for item T7),
- P6 (window sums) through the aggregation operators of the MFODL monitor. Their fit
  to the integral of section 4.1 of the timing plan is an open question.

Open questions:

- How much to translate. The whole of `determine_basal` is about a thousand lines and
  its Lean proofs depend on the Lean definitions. A smaller start is the T2 layer
  only (`LeanAID/Time/`). The per-call theorems then become axioms of the controller
  contract, as in `docs/uppaal-plan.md` section 3.3.
- How to keep the two models equal. Options are a hand translation checked by
  differential tests on the conformance suite, or a generator from one source.
- Which Isabelle and AFP versions, and whether they match the versions that Munta
  needs.
- The tool rule in `AGENTS.md` must allow Isabelle and the AFP first.

The names of the AFP entries above are from memory. Check them before citing them.
