# Traceability

Source → requirement → theorem → test or simulation scenario.
CFR862 (b)(2)(iii) asks for "a traceability analysis demonstrating that all hazards are
adequately controlled"; this table is the algorithm-level part of such an analysis.

Theorem names refer to `LeanAID/Proofs/*.lean`. Status: **proved** (checked by
`lake build`, no `sorry`, standard axioms only), **planned**, **tested**, **finding**
(oref0 does not satisfy the requirement as written; see `docs/FINDINGS.md`).

The column "model-checked (kind)" is apart from the status. A model-checked result is
about the UPPAAL abstraction of the T2 run model (`docs/uppaal-plan.md`), not about T2
runs or oref0. It is not proved. The proved simulation from the T2 runs in the class R_U to
the model (plan section 7, level 3) is not done. R_U restricts T2 runs, for example
to a constant positive schedule and readings at least 150 s apart. The kinds:

- UPPAAL: `verifyta` 5.1.0-beta5 answers the query, run by `scripts/uppaal.sh`
  (`uppaal/results.json`).
- Munta: the Isabelle-verified checker Munta gives the same answer on the network
  lowered for it, and the three U0b gates pass on that network: the UPPAAL deadlock
  check, the Munta deadlock check, and UPPAAL `E<> false` without an error
  (`uppaal/u4/run_u4.py`, `uppaal/u4/results.json`, `uppaal/u4/results-u5b.json`).
  The lowering is argued, not proved.
- T2 replay: a UPPAAL trace is turned into a T2 run, and a theorem checked by
  `lake build` (`native_decide`) states that the run matches the trace, or for a
  mutation trace that it does not match (`uppaal/replay.py`, `uppaal/replay.json`). A replay checks one trace, not the
  property.

| source | requirement | theorem | tests / scenarios | status | model-checked (kind) |
|---|---|---|---|---|---|
| SR2011 1.2.5; HA2010 1.1, 2.14; CFR880 (b)(7)(ii) | R1 temp basal ceiling | `rate_le_roundBasal_maxSafeBasal`, `rate_le_maxSafeBasal_of_grid`, `setTempBasal_rate_bound` | DB-18, DB-65–68, STB-05–07, STB-09–10 | proved up to half a pump increment; finding F-04 | — |
| SR2011 1.7.1, 1.2.1 | R2 no negative rate | `rate_le_roundBasal_maxSafeBasal` (0 ≤ r) | STB-08 | proved | — |
| SR2011 1.2.1; CFR880 (b)(7)(ii) | R3 rounding | `rate_can_exceed_maxSafeBasal`, `roundBasal_overshoot`, `roundBasal_monotone` | DB-01–05, DB-68–70 | finding F-04; strongest true version proved | — |
| SR2011 1.2.5 | R4 duration | — | DB-08, DB-14 | planned (NaN durations possible on invalid input, see F-06) | P3 on the model: UPPAAL, Munta (see below) |
| SR2011 1.3.1, 1.3.2 | R5 microbolus limits | `microbolus_limits` | none in oref0's suite (F-01) | proved (u > 0, u ≤ maxBolus) | — |
| SR2011 1.3.16; HA2010 3.1.3 | R6 microbolus ≤ max_iob | `microbolus_limits` | none in oref0's suite (F-01) | proved (iob + u ≤ max_iob) | — |
| SR2011 1.3.5 | R7 microbolus spacing | `microbolus_limits` | none in oref0's suite (F-01) | proved (lastBolusAge > SMBInterval) | P5-issued, P5-pair on the model: UPPAAL, Munta (see below) |
| HA2010 1.1; SR2011 1.3.14 | R8 low glucose suspend | `low_glucose_suspend` | DB-23–25 | proved | — |
| HA2010 1.1 | R9 predicted low suspend | `low_glucose_suspend` | none in oref0's suite (F-01) | proved | — |
| HA2010 1.1 | R10 low eventualBG | (M6) | DB-08, 13, 14, 26–28, 34, 64 | planned | — |
| SR2011 1.3.16; HA2010 3.1.3 | R11 IOB ≥ max_iob | `iob_at_max` | DB-22 | proved | — |
| HA2010 3.1.2; SR2011 1.3.12; CFR862 (b)(3)(iv), (b)(1)(vi) | R12 unreliable glucose | `cgm_unreliable_no_increase` (independent hypotheses), `cgmError_no_increase` | DB-44, DB-45 | proved for dated readings; **undated readings not covered, finding F-11** (`undated_glucose_max_rate`) | P1 on the model: UPPAAL, Munta (see below) |
| CFR862 (b)(3)(iv) | R13 missing inputs → error | `missing_current_basal`, `missing_targets`, `missing_iob` | DB-43, DB-46, DB-47 | proved | — |
| CFR862 (b)(3)(iv) | R14 other out-of-bounds input | `missing_max_basal_no_clamp` (finding) | differential tests on invalid input (M10) | finding F-06 (oref0 issues rate NaN); `aid-lean --safe` refuses inputs outside the valid domain (shell, not verified) | — |
| HA2010 4.6.3; CFR862 (b)(3)(iii) | R15 pump state disagreement | `stPumpHistory_error` (lemma: the early return is `setTempBasal(0,0)`) | none in oref0's suite | proved as lemma | — |
| SR2011 1.3.11; HA2010 3.1.3 | R16 DIA lower bounds | (M6) | IOB-08 | planned | — |
| HA2010 3.1.3 | R17 IOB of one dose | (M6/M8) | IOB-01–07 | planned | — |
| HA2010 3.1.3 | R18 IOB = specification | (M8) | IOB-10–26 | planned (stretch) | — |
| SR2011 1.8.2 | R19 suspended time | (M8) | IOB-15–20 | planned | — |
| HA2010 1.1, 2.14 | R20 bounded delivery | (M9) | simulation (M11) | planned (stretch) | not checked: P6 is outside the UPPAAL plan |
| SR2011 1.3.16 | R21 no stacking | (M9) | simulation (M11) | planned (stretch) | — |
| CFR862 (b)(4) | R22 determinism | by construction | `scripts/check.sh` | `scripts/check.sh` passes | — |
| CFR862 (b)(2)(iii) | R23 faithfulness | `Conformance.Checks` (native_decide) | conformance (M4), difftest (M10), simulation (M11) | tested: 65/65 determine-basal, 49+2 ties/51 iob, all small suites | — |


## Timing properties and the UPPAAL abstraction

The timing properties P1 to P6 are stated in `docs/timing-plan.md` (section 4) over
runs of the T2 model. The proved theorems are in `LeanAID/Time/` and are in
`scripts/headline.txt`. The model checks are in `uppaal/`. Each column is a
different kind of evidence. Only the column "proved" says that a property holds on
T2 runs. The other columns are about the model or about single traces.

UPPAAL statuses are from `uppaal/results.json` (104 queries, all with their expected
status). The model variant of each query is in parentheses: `free` is the U1a pump
with a free command choice, `nopump` is the U1b contract model without the pump,
`relaxed` and `nobolus` are the other U1b variants (`uppaal/README.md`, "Model
variants"). `nopump` relates to the contract model by an argument, not by a check.
Munta statuses are from `uppaal/u4/results.json` (U4) and
`uppaal/u4/results-u5b.json` (U5b). Replay results are from `uppaal/replay.json`.

| property | proved (`lake build`) | model-checked: UPPAAL | model-checked: Munta | T2 replay of traces |
|---|---|---|---|---|
| P1 freshness | `p1_faithful`. `p1_derived` with a whole-number status date as a hypothesis | P1 holds (`nopump`). Witnesses P1-w-noread, P1-w-inc reachable. Mutations M-P1-rejected-high, M-P1-nan-units, M-P1-no-hasreading fail | P1 holds, P1-w-noread reachable, the three mutations fail (U4). P1-w-inc unsupported (clock) | P1-w-noread and R-P1-w-inc realized. P1-w-inc unresolved. The three mutation traces are not realizable (`p1_faithful`) |
| P2 rate bound | `p2_rate_bound` | not checked: the contract assumes it | not checked | — |
| P3 durations | `issued_temp_ok`, `p3_temp_ok` | P3 holds (`nopump`). M-P3-positive-120 fails | P3 holds, M-P3-positive-120 fails (U4) | M-P3-positive-120 is not realizable (`p3_temp_ok`) |
| P4a expiry | `p4a_expiry` | P4a holds (`free`). Witnesses P4a-w-running, P4a-w-expired, P4a-w-cancel, collision reachable. Mutations M-ignore-cancel, M-reject-initial, M-drop-temp, M-no-y-reset fail | P4a and most witnesses unsupported (clock). P4a-w-cancel: timeout on the U1a pump (U4), reachable on the reduced pump (U5b). Collision: not run on the U1a pump (U4), reachable on the reduced pump (U5b) | the four witnesses realized on the T2 pump. The four mutation traces are not realized |
| P4b-120 fail-safe | `p4b_fail_safe` (with `InvTemp` on the initial temp) | P4b-120 holds (`free`). P4b-120-w reachable. M-no-upper-bound fails | unsupported (clock) | P4b-120-w realized. M-no-upper-bound not realized |
| P4b-30 fail-safe | `p4b_fail_safe` | P4b-30 holds (`relaxed`). Without the contract it fails (P4b-30-free, `free`), as the plan expects. M-P4b-30 fails | unsupported (clock) | P4b-30-free and P4b-30-free-w realized on the T2 pump. M-P4b-30 is not realizable (`p3_temp_ok`) |
| P5 faithful | `p5_faithful` | P5-issued holds (`nopump`). Witnesses P5-w-first, P5-w-spaced, P5-w-early reachable. M-P5-user fails, and M-P5-user-w is reachable on that mutant. P5-clock holds, M-P5-clock fails | P5-issued holds, P5-w-first and R-P5-w-first reachable, M-P5-user fails (U4). The other witnesses, P5-clock and M-P5-clock unsupported (clock) | P5-w-early, R-P5-w-first, R-P5-w-spaced, R-P5-w-early realized. P5-w-first and P5-w-spaced unresolved. M-P5-user and M-P5-user-w are not realizable (`p5_faithful`, `smb_spacing` under BolusSeen). M-P5-clock: observable part realized, the clock fault has no T2 counterpart |
| P5 derived (spacing of accepted microboluses) | not proved over runs. `smb_guard_iff`, `lastBolusAge_guard_iff` and `smb_spacing` (BolusSeen as a hypothesis) give the guard as a time bound | P5-pair holds (`nopump`). P5-pair-w, P5-w-bolus, P5-w-user-cycle reachable | P5-pair holds. P5-pair-w, P5-w-bolus, P5-w-user-cycle and their `R-` witnesses reachable (U4) | R-P5-pair-w, R-P5-w-bolus, P5-w-user-cycle, R-P5-w-user-cycle realized. P5-pair-w and P5-w-bolus unresolved |
| P6 delivered insulin | `rate_envelope`, `p6_basal` (rate part only) | not checked (outside the plan) | not checked | — |
| F-20 (zero temp after a stopped loop) | finding, run `zeroRun` (`native_decide`, `LeanAID/Conformance/TimeRuns.lean`) | F-20 reachable (contract model). R-F-20 reachable (`nobolus`) | unsupported (clock) | R-F-20 realized. F-20 unresolved |
| model property: CGM readings | — (an assumption of the model) | `cgm` holds (`nopump`). cgm-w reachable. M-cgm-first fails | `cgm` holds, M-cgm-first fails (U4) | cgm-w realized. M-cgm-first not replayed |
| model property: no bolus from a rejected command | — | `bolus` holds (`free`). bolus-w, reject-bolus-w reachable. M-reject-bolus fails | not run on the U1a pump (U4). On the reduced pump: `bolus` holds, bolus-w and reject-bolus-w reachable, M-reject-bolus fails (U5b) | bolus-w, reject-bolus-w realized. M-reject-bolus not realized |
| model property: no deadlock | — | `deadlock` holds (`free`), `deadlock-contract` holds (`nopump`). M-missing-reject fails | `deadlock-contract` holds (U4). `deadlock`: timeout on the U1a pump (U4), holds on the reduced pump (U5b). M-missing-reject: see the U5b table | not replayed: deadlock is a property of the automata |
| model property: run start and close | — | close-no-steps-w, prerun-w-t0, prerun-w-old reachable | close-no-steps-w: not run on the U1a pump (U4), reachable on the reduced pump (U5b). The two pre-run witnesses unsupported (clock) | close-no-steps-w, prerun-w-t0, prerun-w-old realized |

Replay totals (`uppaal/replay.json`): 24 traces realized, 10 of U1a on the T2 pump and
14 of U1b on legal T2 runs in R_U. The observable part of M-P5-clock is realized as
well. Six U1a mutation traces are not realized, each at the fault of its mutant.
Seven U1b mutation traces are not realizable by the Lean theorems named above. Six
shortest witnesses are unresolved, and each has a realized `R-` witness. Two traces
are not replayed (M-missing-reject, M-cgm-first).

Munta totals: U4 gives 21 answers on `nopump` (holds 6, fails 6, reachable 9), each
equal to UPPAAL with the three gates passed. Of the other 37 queries of `check.ALL`,
28 are unsupported because they read a clock, 3 time out at 1800 s on the U1a pump,
and 6 were not run on the U1a pump to save time.

### U5b: Munta answers on the reduced pump

`munta.few_durations` keeps the issued durations -1, 0, 1, 30, 120 and 121, so the
pump has the durations 30 and 120 only. The reduced network is a restriction of the
U1a network. All nine pump queries without a clock get a Munta answer equal to UPPAAL
(`uppaal/u4/results-u5b.json`). The transfer to the U1a pump is recorded per query:

| query | Munta | U0b gates | transfer to the U1a pump |
|---|---|---|---|
| P4a-w-cancel, collision, bolus-w, reject-bolus-w, close-no-steps-w | reachable | pass | direct: the witness is a run of the U1a network |
| M-reject-bolus | fails | pass | direct, to the mutant: the counterexample is a run of the U1a mutant |
| `bolus`, `deadlock` | holds | pass | by a written argument, not checked (`uppaal/README.md`, "Reduced pump (U5b)") |
| M-missing-reject | fails | the UPPAAL and Munta deadlock gates fail by design, because the mutant deadlocks | does not count |

So eight answers count for the U1a pump: six by direct transfer and two by the
argument.

### U5: results on extended models

The U5 models extend the abstraction with behaviors that T2 excludes
(`uppaal/extensions.md`): delayed execution, lost acknowledgement, and two loops.
Their results are UPPAAL results on the extended models, not results about T2 or
oref0, and they have no Munta run. Their traces are in `uppaal/traces/u5/`. They are
not T2 runs and are not replayed. The failures are candidate findings F-25 to F-27
(`docs/FINDINGS.md`). They can be spurious, because the contract allows more outputs
than oref0 gives. Each extension has a pump part, which checks P4b, and a bolus part,
which checks P5. The delayed pump part issues a reduced set of commands
(`uppaal/extensions.md`). Statuses from `uppaal/results.json` (IDs `U5-...`):

| model | P4b-120, P4b-30 | P5-issued | P5-pair | candidate finding |
|---|---|---|---|---|
| `u5-base` (no extension) | hold | holds | holds | — |
| `delayed` | fail. They hold with the bounds 7500 s and 2100 s | holds | fails | F-25 |
| `lostack` | hold | holds | fails | F-26 |
| `lostack-dedup` | not checked | holds | holds | — |
| `twoloops` | hold | fails | fails | F-27 |
