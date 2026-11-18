# Traceability

Source → requirement → theorem → test or simulation scenario.
CFR862 (b)(2)(iii) asks for "a traceability analysis demonstrating that all hazards are
adequately controlled"; this table is the algorithm-level part of such an analysis.

Theorem names refer to `LeanAID/Proofs/*.lean`. Status: **proved** (checked by
`lake build`, no `sorry`, standard axioms only), **planned**, **tested**, **finding**
(oref0 does not satisfy the requirement as written; see `docs/FINDINGS.md`).

| source | requirement | theorem | tests / scenarios | status |
|---|---|---|---|---|
| SR2011 1.2.5; HA2010 1.1, 2.14; CFR880 (b)(7)(ii) | R1 temp basal ceiling | `rate_le_roundBasal_maxSafeBasal`, `rate_le_maxSafeBasal_of_grid`, `setTempBasal_rate_bound` | DB-18, DB-65–68, STB-05–07, STB-09–10 | proved up to half a pump increment; finding F-04 |
| SR2011 1.7.1, 1.2.1 | R2 no negative rate | `rate_le_roundBasal_maxSafeBasal` (0 ≤ r) | STB-08 | proved |
| SR2011 1.2.1; CFR880 (b)(7)(ii) | R3 rounding | `rate_can_exceed_maxSafeBasal`, `roundBasal_overshoot`, `roundBasal_monotone` | DB-01–05, DB-68–70 | finding F-04; strongest true version proved |
| SR2011 1.2.5 | R4 duration | — | DB-08, DB-14 | planned (NaN durations possible on invalid input, see F-06) |
| SR2011 1.3.1, 1.3.2 | R5 microbolus limits | `microbolus_limits` | none in oref0's suite (F-01) | proved (u > 0, u ≤ maxBolus) |
| SR2011 1.3.16; HA2010 3.1.3 | R6 microbolus ≤ max_iob | `microbolus_limits` | none in oref0's suite (F-01) | proved (iob + u ≤ max_iob) |
| SR2011 1.3.5 | R7 microbolus spacing | `microbolus_limits` | none in oref0's suite (F-01) | proved (lastBolusAge > SMBInterval) |
| HA2010 1.1; SR2011 1.3.14 | R8 low glucose suspend | `low_glucose_suspend` | DB-23–25 | proved |
| HA2010 1.1 | R9 predicted low suspend | `low_glucose_suspend` | none in oref0's suite (F-01) | proved |
| HA2010 1.1 | R10 low eventualBG | (M6) | DB-08, 13, 14, 26–28, 34, 64 | planned |
| SR2011 1.3.16; HA2010 3.1.3 | R11 IOB ≥ max_iob | `iob_at_max` | DB-22 | proved |
| HA2010 3.1.2; SR2011 1.3.12; CFR862 (b)(3)(iv), (b)(1)(vi) | R12 unreliable glucose | `cgm_unreliable_no_increase` (independent hypotheses), `cgmError_no_increase` | DB-44, DB-45 | proved for dated readings; **undated readings not covered, finding F-11** (`undated_glucose_max_rate`) |
| CFR862 (b)(3)(iv) | R13 missing inputs → error | `missing_current_basal`, `missing_targets`, `missing_iob` | DB-43, DB-46, DB-47 | proved |
| CFR862 (b)(3)(iv) | R14 other out-of-bounds input | `missing_max_basal_no_clamp` (finding) | differential tests on invalid input (M10) | finding F-06 (oref0 issues rate NaN); `aid-lean --safe` refuses inputs outside the valid domain (shell, not verified) |
| HA2010 4.6.3; CFR862 (b)(3)(iii) | R15 pump state disagreement | `stPumpHistory_error` (lemma: the early return is `setTempBasal(0,0)`) | none in oref0's suite | proved as lemma |
| SR2011 1.3.11; HA2010 3.1.3 | R16 DIA lower bounds | (M6) | IOB-08 | planned |
| HA2010 3.1.3 | R17 IOB of one dose | (M6/M8) | IOB-01–07 | planned |
| HA2010 3.1.3 | R18 IOB = specification | (M8) | IOB-10–26 | planned (stretch) |
| SR2011 1.8.2 | R19 suspended time | (M8) | IOB-15–20 | planned |
| HA2010 1.1, 2.14 | R20 bounded delivery | (M9) | simulation (M11) | planned (stretch) |
| SR2011 1.3.16 | R21 no stacking | (M9) | simulation (M11) | planned (stretch) |
| CFR862 (b)(4) | R22 determinism | by construction | `scripts/check.sh` | `scripts/check.sh` passes |
| CFR862 (b)(2)(iii) | R23 faithfulness | `Conformance.Checks` (native_decide) | conformance (M4), difftest (M10), simulation (M11) | tested: 65/65 determine-basal, 49+2 ties/51 iob, all small suites |
