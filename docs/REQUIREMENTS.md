# Requirements

Safety requirements for the oref0 dose decision, written in plain English before any
proof, each traced to the hazard analysis or regulation it comes from. Source keys are
defined in `refs/README.md` (HA2010, SR2011, CFR862, CFR880).

The hazard analyses were written for insulin *pumps*. oref0 is a *controller* that
commands a pump (CFR862 (a)), so each pump requirement is adapted to the controller:
"the pump shall not deliver X" becomes "the controller shall not command X". The
adaptation is stated where it is not obvious.

Status values:
- **to prove**: a Lean theorem about the transcribed oref0 functions (`LeanAID/Core`).
- **to test**: checked by conformance, differential testing or simulation, not proved.
- **out of scope (reason)**.

"Issued rate" means the `rate` field of the result of `determine_basal`, when present.
When `determine_basal` returns no `rate`, the pump keeps running its current temp
basal (or the scheduled basal); requirements about issued rates say so explicitly
when they also constrain that case. "Valid input" is defined in `docs/DESIGN.md`
section "Valid input" and in Lean as `LeanAID.ValidInput`; every requirement below
that says "for valid input" uses exactly that definition.

Theorem names and results are in `docs/TRACEABILITY.md`.

---

## A. Limits on what the controller commands

**R1 – Temp basal ceiling.** For valid input, every issued rate is at most oref0's
`maxSafeBasal = min(max_basal, max_daily_safety_multiplier × max_daily_basal,
current_basal_safety_multiplier × current_basal)` (multipliers default to 3 and 4),
up to pump-increment rounding as stated in R3.
*Sources:* SR2011 1.2.5 (temporary basal rate shall not exceed x U/h); HA2010 1.1
(overdose), 2.14 (unexpected delivery of insulin); CFR880 (b)(7)(ii) (maximum basal
rate is a pump parameter the controller must respect). *Status:* to prove (H1).

**R2 – No negative rate.** For valid input, every issued rate is ≥ 0.
*Sources:* SR2011 1.7.1 (no reverse delivery: a negative rate is not a deliverable
command); SR2011 1.2.1 (rates range from 0 upward). *Status:* to prove (H1).

**R3 – Rounding never pushes a rate above a limit.** Rounding a rate to the pump's
increment (`round_basal`) shall not produce a value above the limit the rate was
clamped to. *Sources:* SR2011 1.2.1 (rates in fixed increments); CFR880 (b)(7)(ii)
(increment size); HA2010 1.1. *Status:* to prove (H6). If oref0 violates it, record
the counterexample (FINDINGS) and prove the strongest true bound.

**R4 – Temp basal duration.** Every issued duration is 0 (cancel) or between 30 and 120
minutes. *Sources:* SR2011 1.2.5 (duration of a temporary basal shall not exceed y
hours). *Status:* to prove.

**R5 – Microbolus limits.** For valid input, an issued microbolus (`units`) is positive,
at most `maxBolus` (oref0's `maxSMBBasalMinutes` / `maxUAMSMBBasalMinutes` worth of
`current_basal`, default 30 minutes), at most half of `insulinReq`, and a multiple of
the bolus increment. *Sources:* SR2011 1.3.1 (maximum bolus dosage limit), 1.3.2
(bolus increments); HA2010 1.1. *Status:* to prove (H2).

**R6 – Microbolus never exceeds max IOB.** For valid input, if a microbolus is issued
then `iob + units ≤ max_iob`. *Sources:* SR2011 1.3.16 (account for unabsorbed
insulin); HA2010 3.1.3 (incorrect IOB), 1.1. *Status:* to prove (H2).

**R7 – Microbolus spacing.** A microbolus is issued only if the last bolus was more than
`SMBInterval` minutes ago (default 3, clamped to 1–10). *Sources:* SR2011 1.3.5 (no
bolus while another is in progress). *Status:* to prove.

## B. Hypoglycaemia protection

**R8 – Low glucose suspend.** For valid input with a fresh, non-error glucose reading:
if BG is below oref0's `threshold` (computed by oref0 from `min_bg`, after its own
adjustments) and BG is not rising (`minDelta ≤ 0`), then the controller commands a
zero temp (or leaves a running zero temp in place) and issues no microbolus.
*Sources:* HA2010 1.1 (overdose leading to hypoglycaemia); SR2011 1.3.14 (no
correction when BG is below target). *Status:* to prove (H3).

**R9 – Predicted low suspend.** Under the same conditions, if oref0's predicted
`minGuardBG` is below `threshold` (whatever the current BG), the controller commands a
zero temp and issues no microbolus. *Sources:* as R8. *Status:* to prove (H3).

**R10 – Low eventual BG never raises insulin.** For valid input, if oref0's `eventualBG`
is below `min_bg`, any issued rate is at most the (sensitivity-adjusted) basal.
*Sources:* HA2010 1.1. *Status:* to prove (lifted from class B tests).

**R11 – IOB at or above max_iob.** For valid input, if `iob ≥ max_iob` then any issued
rate is at most the (sensitivity-adjusted) scheduled basal and no microbolus is issued.
*Sources:* SR2011 1.3.16; HA2010 3.1.3, 1.1. *Status:* to prove (H4).

## C. Bad or missing data

**R12 – Error-coded or unreliable glucose.** If the glucose reading is an error code
(BG ≤ 10 or BG = 38), noisy (`noise ≥ 3`), stale (> 12 minutes old) or from the future
(> 5 minutes), or flat in a way that indicates a failed sensor, then the controller
does not increase insulin: it either replaces a running high temp by the basal rate,
shortens a long zero temp to 30 minutes, or issues nothing; it never issues a
microbolus. *Sources:* HA2010 3.1.2 ("calculator uses obsolete BG readings"); SR2011
1.3.12 (age of the BG reading); CFR862 (b)(3)(iv) (safe operation when data is
outside the specified bounds), (b)(1)(vi) (safe therapy when communication is lost).
*Status:* to prove (H5).

**R13 – Missing required inputs.** If `current_basal`, `min_bg`/`max_bg`, or the IOB data
(or its `iob`/`activity` fields) are missing, the controller returns an error and no
command. *Sources:* CFR862 (b)(3)(iv). *Status:* to prove (H5).

**R14 – Other out-of-bounds inputs.** Inputs outside the valid domain (non-numeric or
non-finite values, zero or negative sensitivity, etc.) shall not lead to an insulin
increase. *Sources:* CFR862 (b)(3)(iv). *Status:* to test for oref0 (we expect
violations; FINDINGS), and enforced in `aid-lean` by input validation in the shell,
which rejects such input with an error. The shell is not verified.

**R15 – Pump state disagreement.** If the currently running temp reported by the pump
disagrees with the last temp in pump history (oref0's check at determine-basal.js
lines 380–392), the controller cancels the temp (rate 0, duration 0).
*Sources:* HA2010 4.6.3 (synchronisation error between components); CFR862
(b)(3)(iii) (sharing of state information). *Status:* to prove.

## D. Insulin on board

**R16 – DIA lower bounds.** IOB is computed with a duration of insulin action of at
least 3 h, and at least 5 h for the exponential curves. *Sources:* SR2011 1.3.11;
HA2010 3.1.3. *Status:* to prove.

**R17 – IOB of a single dose.** For a single non-negative dose, IOB is between 0 and the
dose, equals the dose at the time of delivery, and is 0 once DIA has elapsed.
*Sources:* HA2010 3.1.3. *Status:* to prove (bilinear curve: M5/M6; exponential curve:
M8 with the proved bound on the `exp` approximation).

**R18 – IOB agrees with its specification.** Computed IOB equals the specification's
sum of per-dose insulin remaining (non-negative for non-negative doses, non-increasing
without new doses, additive over doses). *Sources:* HA2010 3.1.3. *Status:* to prove
(stretch, M8).

**R19 – Suspended time delivers nothing.** IOB does not count basal insulin for periods
when the pump was suspended (when `suspend_zeros_iob` is set). *Sources:* SR2011 1.8.2.
*Status:* to test (iob tests IOB-15 to IOB-20); to prove (stretch, M8).

## E. Behaviour over time (stretch, M9)

**R20 – Bounded delivery.** Over any window of 5-minute cycles, the insulin commanded is
bounded by the limits of R1 and R5. *Sources:* HA2010 1.1, 2.14. *Status:* to prove
(stretch).

**R21 – No stacking.** Repeated cycles never stack microboluses past `max_iob`.
*Sources:* SR2011 1.3.16; HA2010 3.1.3. *Status:* to prove (stretch).

## F. Engineering requirements

**R22 – Determinism.** The decision is a pure function of its inputs, including the
current time, so every decision can be replayed for audit. *Sources:* CFR862 (b)(4)
(record of critical events). *Status:* by construction (the core is a pure Lean
function; `scripts/check.sh` rejects escape hatches).

**R23 – Faithfulness.** On oref0's own tests and on random valid inputs, `aid-lean`
produces the same decision as oref0. *Sources:* CFR862 (b)(2)(iii) (controls
validated in the final design). *Status:* to test (M4 conformance, M10 differential
testing).

## G. Out of scope

| topic | source | reason |
|---|---|---|
| Alarms, alerts, reminders | SR2011 §3 | not part of the dose decision (pump / app) |
| Reservoir, occlusion, air in line, priming | SR2011 1.1, 1.4–1.6; CFR880 (b)(1)(ii) | pump hardware |
| Secure pairing and transmission | CFR862 (b)(3)(i)–(ii); CFR880 (b)(3) | communication layer, not the algorithm |
| Logging of critical events | CFR862 (b)(4) | app; R22 makes replay possible |
| Clinical performance, human factors, labelling | CFR862 (b)(1)(i)–(ii), (b)(7)–(8) | require clinical evidence; simulation (M11) is not evidence |
| Bolus calculator and food database | SR2011 1.3.9–1.3.22; HA2010 3.1.1 | oref0 does not recommend manual boluses |
| Clock correctness | HA2010 4.6.1–4.6.2; SR2011 3.3.1 | the clock is an input; R12 covers readings whose time is implausible |
| Autosens and autotune | kickoff scope | their outputs are inputs here (`sensitivityRatio`) |
