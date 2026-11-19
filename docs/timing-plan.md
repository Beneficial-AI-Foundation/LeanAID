# Plan: timing properties (extends M9)

Status: plan, nothing in this file is proved yet. Written 2026-11-19, revised the same
day after an adversarial review. The review and the changes are listed in
section 7.

This plan extends milestone M9 ("Properties over time", `prompts/kickoff.md`) and the
two requirements that M9 already names, R20 (bounded delivery) and R21 (no stacking).
It adds the timing requirements that the standards and the hazard analysis state, and
it fixes how the project will express them in Lean.

## 1. Where the project is now

The Lean model checks one call to `determine_basal`. `LeanAID.step` is a pure function
from one snapshot of inputs to one result. Time appears only as data inside that
snapshot:

- the clock `clock.now` (an explicit input, not `new Date()`),
- the date of the glucose reading (`glucose_status.date`), compared with `now` in
  `cgmStale` (`LeanAID/Core/DetermineBasal.lean:158`). The age `minAgo` is rounded to
  one decimal place before the comparison (`gluVals`, line 144). When the rounded age is
  above 12 minutes or below −5 minutes, the reading is stale. So a reading 12.04 minutes
  old is not stale. The proved theorem `cgm_unreliable_no_increase` uses 12.05 and
  −5.05 minutes for this reason (F-16).
- the date and duration of the last temp basal (R15),
- the pump history, from which `LeanAID/Core/Iob.lean` computes insulin on board over
  the duration of insulin action, and `lastBolusTime`. Temps below the scheduled basal
  enter this history as negative doses (`Iob.lean:549`).
- the time since the last bolus, `lastBolusAge`, also rounded to one decimal place
  before it is compared with `SMBInterval` (R7, line 783),
- the issued duration. Every temp with a positive rate has duration 30 minutes. Zero
  temps have durations from 30 to 120 minutes. The low-glucose branch (line 898) and
  the zero-temp branch (line 741) allow up to 120 minutes. The SMB low temp
  (`smbLowTemp`) allows up to 60 minutes. A duration of 0 cancels the temp. NaN durations
  exist (F-06).
- the 5-minute steps of the glucose predictions.

The model does not contain time passing between calls. It has no loop scheduler, no
pump that executes and ends a temp basal, and no delays or failures in communication.
Clock correctness is out of scope (`docs/REQUIREMENTS.md`, section G), and the model
uses a fixed UTC offset (D7 in `docs/DESIGN.md`). The simulation in `sim/` runs the loop
over virtual time. It writes one log row per 5-minute step, and it runs with
`microBolusAllowed: False` (`sim/harness.py:284`). It is a test, not a proof.

In original OpenAPS, the real-time behavior is outside oref0. Cron runs
`oref0-pump-loop.sh` about every minute. The script fetches CGM and pump data and calls
`determine_basal`. It sends the command to the pump and handles radio timeouts and
retries. The fail-safe is that every temp basal ends at the end of its duration. If
the loop stops, a temp with a positive rate ends after at most 30 minutes. A zero temp
ends after at most 120 minutes. Then the pump returns to the scheduled basal.

The per-call theorems are the base for this plan. Each one shows that one step
satisfies a property. A temporal property states that the property holds at every step
of a run, or that some event follows within a time bound.

## 2. What the sources require about time

Sources marked "checked" were read in full on 2026-11-19. Sources marked "not checked"
are paywalled. Their content here comes from memory and must not be cited until a
person reads the clause.

Section 4 separates three things for each property. The source obligation is what the
source says. The adaptation is how it applies to a controller. The chosen bound is the
number that the project uses. A source that asks for a value to be stated or
reported does not by itself give the number.

### 2.1 SR2011 (generic insulin pump safety requirements), checked

The requirements use parameters (`x`, `y`) instead of fixed numbers. The ones with a
time bound:

| ID | requirement (shortened) | relevance |
|---|---|---|
| 1.1.2 | average flow rate in any continuous x-minute period within ±y % of the programmed rate | pump, sliding window |
| 1.2.5 | temp basal rate at most x U/h, duration at most y hours | controller (R1, R4) |
| 1.2.6 | the temp basal starts immediately after the user accepts it. At its end, the previous basal profile resumes | pump model |
| 1.2.8 | basal paused for more than x minutes: alarm every y minutes up to z hours | alarms, out of scope |
| 1.3.12 | report the BG reading and its time or age used for a correction | freshness (no threshold given) |
| 1.5.4 | if flow is x % low for y seconds, occlusion alarm | pump hardware |
| 1.5.5 | on occlusion, stop flow and alarm within x seconds | pump hardware |
| 1.6.1 | air-in-line alarm within x seconds | pump hardware |
| 1.8.4 | non-delivery mode for more than x minutes: alarm every x minutes | alarms, out of scope |
| 3.3.1 | check the real-time clock every x minutes | clock, out of scope |
| 3.5.2 | on unrecoverable software failure, enter the failsafe state within x seconds | pump |
| 5.4.1 | no user interaction for x hours: stop all delivery and alarm | pump |

### 2.2 21 CFR 862.1356 (controller) and 880.5730 (ACE pump), checked

Text in `refs/`. Neither section gives a number. They require the maker to state timing
values and to test them:

- 862.1356 (b)(1)(vi) and 880.5730 (b)(4): if communication is interrupted, lost or
  re-established, therapy stays safe. 880.5730 (b)(4) gives "reverting to a
  pre-programmed, safe drug delivery rate" as an example. The project adaptation is
  the temp expiry. The project does not claim that the scheduled basal is clinically
  safe, only that the pump returns to it.
- 880.5730 (b)(1)(ii): detect hazards such as occlusions "within a clinically relevant
  timeframe".
- 880.5730 (b)(7)(iv): basal accuracy as the amount delivered up to time points, for
  example 1, 6 and 12 hours after delivery starts.
- 880.5730 (b)(7)(v): "the longest time period that may elapse before an occlusion alarm
  is triggered".
- 862.1356 (b)(4) and 880.5730 (b)(5): record of critical events, including connectivity
  events.

### 2.3 IEC standards, not checked

IEC 60601-2-24 (infusion pumps) measures delivery accuracy over observation windows
(trumpet curves, windows of about 2, 5, 11, 19 and 31 minutes). It also requires the
maker to state the time to an occlusion alarm and the bolus released after the
occlusion clears. IEC 60601-1-8 (alarm systems) defines the alarm condition delay and
the alarm signal generation delay. IEC 62304 (software life cycle) and ISO 14971 (risk
management) give no timing numbers.

### 2.4 Kinds of timing property in these sources

| kind | example | logic needed |
|---|---|---|
| bounded response | occlusion → alarm within T | MTL |
| freshness (past bound) | rate increase → the reading used is at most 12 minutes old | past-time MTL |
| bounded duration | temp basal → scheduled basal at its deadline unless replaced | MTL |
| sliding-window sum | insulin delivered in any 60 minutes ≤ X | integral over a window, see 3.1 |
| sliding-window average | average flow over any L minutes within ±e % | average over a window, see 3.1 |

## 3. Logic and its Lean representation

### 3.1 Choice of logic

MTL (metric temporal logic, Koymans 1990) adds time intervals to the operators of LTL.
On discrete time, bounded MTL operators unroll into finite conjunctions, so MTL is no
more expressive than LTL there. MLTL (Mission-time LTL) is the discrete fragment with
natural-number interval bounds. STL (signal temporal logic, Maler and Ničković 2004)
extends MTL to real-valued signals. Window sums and averages need more than MTL or STL.
Known extensions are AvSTL (averaging operators, Akazaki and Hasuo 2015) and freeze
quantifiers (TPTL, Alur and Henzinger). The expression "STL with aggregation" used in
earlier discussion is a description, not the name of a logic.

The project does not need a named logic. A Lean predicate over runs can state a window
integral directly. A named logic matters only for model checkers or generic monitors.

### 3.2 Existing libraries (checked 2026-11-19)

| library | system | content | use here |
|---|---|---|---|
| CSLib (`leanprover/cslib`) | Lean 4, Mathlib | `Foundations/Data/OmegaSequence/Temporal.lean`: `Step`, `LeadsTo` over infinite sequences, no time bounds. `Logics/BTL`: modal F and P only | reference for `LeadsTo` lemmas |
| LeanLTL (arXiv 2507.01780) | Lean 4 | LTL over finite and infinite traces, formulas contain Lean expressions | possible base, not needed |
| LeanearTemporalLogic | Lean 4 | LTL syntax, semantics, transition systems | reference |
| AFP `Mission_Time_LTL` and related entries | Isabelle | MLTL syntax, semantics, formula progression, translation to regular expressions | reference for definitions and lemmas |
| lattice-mtl (RV 2020) | Rocq | past-time MTL, verified online monitors, sliding-window aggregation, extracted to OCaml | reference for the monitor (T7) |
| VeriMon, Vydra | Isabelle | verified monitors for metric first-order temporal logic and metric dynamic logic | reference |

The search found no Lean 4 MTL or MLTL library that suits this project, and the project
selects none. CSLib depends on Mathlib, and the project has no Mathlib so far.
External model checkers (for example UPPAAL) are not allowed by `AGENTS.md`.

### 3.3 Decision: a fixed-profile cycle model first, temporal predicates on top

Two reviews showed that the meaning of the properties depends on the system model more
than on the temporal operators. So the order is:

1. concrete counterexample runs for the disputed cases (T0),
2. a small transition system with one simple first milestone (T2),
3. the properties as direct predicates over legal runs,
4. generic temporal helpers only where a concrete theorem needs them.

Time is `Int` milliseconds since the epoch, the same unit as `clock.now`.

The first milestone uses an atomic cycle. Steps have strictly increasing times. A
step is an ordered list of events at one time: first environment events (CGM readings,
user boluses, carb entries), then at most one cycle. In a cycle, the loop reads the
inputs, decides, and the pump accepts or loses the whole command. The inputs of a cycle
come from all earlier steps and from the environment events before it in the same
step. This matches `sim/harness.py`, which records a meal bolus at `now` and then calls
the controller at the same `now`. There is at most one cycle per step, so two
decisions never see the same history.
Delayed or uncertain execution is a later extension.

```lean
structure Step (ε : Type) where
  time   : Int          -- epoch milliseconds, as clock.now
  events : List ε       -- the legal-run predicate requires it nonempty

abbrev Run (ε : Type) := List (Step ε)
```

Three notions of state are kept apart:

- the state after a step, a function of the run up to that step,
- the pump state at any time `t` (`stateAt r t`), computed from the last step at or
  before `t`. Temp expiry is a change of `stateAt`, not an event, so a deadline needs
  no recorded event,
- the status of a run: closed (no more steps will come, for example a stopped loop) or
  observed (a log that can continue). The difference matters for obligations whose
  deadline lies after the last step. On a closed run, `stateAt` decides them. On an
  observed run, they are pending.

Theorems are about finite runs. On a closed run they cover every deadline. On an
observed run they cover only deadlines up to the last step. Strictly increasing integer
times grow without bound on an infinite run, so no separate progress assumption is
needed.

A deep embedding (an inductive `Formula` type and a function `sat`) is postponed. If T7
needs a generic monitor for many formulas, add it then.

## 4. Properties to prove

Notation: times in minutes. Every property names the observable that it is about:

- issued: in the `Result` of `LeanAID.step` at a cycle,
- accepted: executed by the pump model (T2), after validation,
- the pump state from `stateAt`.

Three layers are kept apart. Controller-output properties are about issued values. They
need finite-value hypotheses, and NaN outputs stay findings (F-06). Pump validation
rejects non-finite or out-of-range commands. Accepted-action properties are about what
passed validation. A pump that rejects a NaN command does not make the controller
output safe, so a rejection never removes a finding.

Where oref0 compares a rounded value, the plan proves two statements: a faithful one,
with the rounded comparison exactly as the code does it, and a derived one in real
elapsed time with explicit slack. The slack is recorded as the gap between the
requirement and the code, as F-16 does for the per-call theorems.

All properties assume a legal run of the T2 model, the T2 assumptions, and valid input
at every cycle (`LeanAID.ValidInput`).

| ID | layer | property | sources (obligation → adaptation) | existing base |
|---|---|---|---|---|
| P1 | issued | freshness. Faithful: when a cycle issues a rate above `profileCurrentBasal` (the profile basal rounded to the pump increment, oref0 line 142) or a microbolus, its reading is dated and the rounded age is in [−5, 12]. Derived: the real age is in [−5.05, 12.05) | SR2011 1.3.12 (report the age), HA2010 3.1.2 → bound 12 min, chosen by oref0 | `cgm_unreliable_no_increase` (uses `profileCurrentBasal`). F-11 gives a counterexample run with an undated reading. A rate of 0.85 above an unrounded basal of 0.83 with a stale reading is allowed by the code: record that gap |
| P2 | issued | every finite issued rate is at most `round_basal(maxSafeBasal)` of its cycle | R1, SR2011 1.2.5 | `rate_le_roundBasal_maxSafeBasal`. F-04, F-06, F-12 stay findings |
| P3 | issued | (a) every finite issued duration is 0 or in [30, 120]. (b) If the rate is also finite, the duration is 0, or in [30, 120] with rate 0, or exactly 30 with a positive rate. F-06 (NaN rate with duration 30) and NaN durations stay findings | R4, SR2011 1.2.5 | R4 is not proved |
| P4a | pump | an accepted temp with duration d ends exactly d minutes after it was accepted, unless a later accepted temp or cancel replaces it. A microbolus does not end a temp. After the end, the pump runs the scheduled basal until the next accepted temp | 862.1356 (b)(1)(vi), 880.5730 (b)(4), SR2011 1.2.6 → pump model | T2. A lost command changes nothing |
| P4b | pump | on a closed run whose last accepted temp was at time t, the pump runs the scheduled basal from t + 30 at the latest for a positive rate, and from t + 120 at the latest for a zero temp | same | P3 for accepted temps, P4a, the T2 bound on the initial temp. Finding: a stopped loop can leave a zero temp running for 120 minutes (low delivery, not overdose) |
| P5 | issued and accepted | spacing. Faithful: every issued microbolus has rounded `lastBolusAge > smbInterval` at its cycle. Derived: two different accepted microboluses at times t1 ≤ t2 satisfy t2 − t1 > I − 0.05, with I the fixed `smbInterval`. With atomic cycles, two accepted microboluses never share a time | R7, SR2011 1.3.5 (adapted) | `microbolus_limits`. Needs the T2 history encoding: the IOB input of each cycle comes from all earlier accepted actions |
| P6 (R20) | pump | for every half-open window [t, t + W), the delivered-by-command insulin D(t, W) is at most B(W) (section 4.1) | HA2010 1.1, 2.14, SR2011 1.1.2 | P2, P3, P4a, P5, `microbolus_limits` |
| P7 (R21) | issued, computed | no stacking. See section 4.2: the R21 invariant is stated first, then tested against counterexample runs | SR2011 1.3.16, HA2010 3.1.3 | `iob_at_max`, `microbolus_limits`, IOB lemmas (R17, R18) |

### 4.1 P6: the quantity and the bound

The quantity is the insulin of the pump model, not the sum of commanded rate × full
duration. When the loop reissues a 30-minute temp every 5 minutes, that sum counts
overlapping insulin several times. For a window [t, t + W):

```
D(t, W) = ∫_t^{t+W} rate(stateAt r s) ds / 60  +  Σ { u | microbolus u accepted at s, t ≤ s < t + W }
```

The integral is a finite sum of rate × overlap over piecewise-constant segments, in
exact rationals.

The first milestone fixes the profile for the whole run. This removes the case where a
temp accepted under one profile runs into a window under a stricter profile. The
envelope constants are then constants of the run:

- `M`: `round_basal(maxSafeBasal)` over the whole schedule,
- `S`: the largest rate of the pump schedule. The schedule is part of the fixed
  profile, and `current_basal` at each cycle is the schedule rate at that time. T2
  states `S ≤ max_daily_basal` as an assumption, because `ValidProfile` does not give
  it,
- `U`: the largest microbolus (`smbMaxBolus`, from `maxSMBBasalMinutes` or
  `maxUAMSMBBasalMinutes`),
- `I`: the fixed `smbInterval`.

```
B(W) = max(M, S) · W / 60  +  U · (⌊W / (I − 0.05)⌋ + 1)  +  ε_rate · W  +  ε_bolus · (⌊W / (I − 0.05)⌋ + 1)
```

`ε_bolus` is the per-bolus F-16 excess of `microbolus_limits` (U/2^50 + 2^-90), so it
grows with the number of boluses. `ε_rate` is the rate excess of `round_basal`, so it
grows with time. The bound needs the initial state bound of T2: an initial temp has a
rate at most `max(M, S)`. A window with no cycles is covered, because the constants do
not depend on cycles. Profile changes inside a run are a later extension. They need
the envelope over every profile whose commands can still run in the window.

If B(W) cannot be proved in this form, record why in `docs/FINDINGS.md` before
changing it.

### 4.2 P7: the R21 invariant

R21 says: "Repeated cycles never stack microboluses past `max_iob`." A guard at each
cycle plus an accounting identity does not give a run invariant. Computed IOB can rise
without a new bolus: negative contributions from temps below the scheduled basal decay
toward zero (`Iob.lean:549`), and a running high temp keeps adding insulin. With a fixed
profile, changes of `max_iob`, curve, DIA and autosens are excluded for now.

T6 states and tests two candidate invariants before any proof:

- I1 (lifted guard): at every cycle that issues a microbolus u, the computed IOB i of
  that cycle satisfies i + u ≤ `max_iob` + the F-16 allowance. This lifts R6 to runs,
  with the IOB input derived from the run. It is expected to hold.
- I2 (no stacking of boluses): at every time, the part of the computed IOB that comes
  from microboluses is at most `max_iob`. This is the plain reading of R21. It is
  expected to fail: zero temps make the computed IOB negative, and the guard then
  allows microboluses whose sum exceeds `max_iob`. T0 builds this counterexample run.

A frozen accounting lemma is proved as a tool, not as R21. Add one bolus u at time t to
a history, and keep the time t and the profile. Then the computed IOB at t grows by u,
up to stated rounding.

The result is recorded honestly. If I1 holds and I2 fails, `docs/REQUIREMENTS.md` and
`docs/FINDINGS.md` say that R21 holds in form I1 and fails in form I2. The R21 text is
not changed to fit I1.

## 5. Work items

Each item ends with `lake build` and `scripts/check.sh` passing, and a local commit.
New modules are imported in `LeanAID.lean`. New headline theorems are added to
`scripts/headline.txt`, so that `check.sh` audits their axioms. Concrete runs are
checked with `example : ... := by decide` (or `native_decide` only where `check.sh`
allows it), not with `#eval`, so that a wrong result fails the build.

T0. Counterexample runs first, in `LeanAID/Time/Examples.lean`:

- a 120-minute zero temp followed by a stopped loop (P4b),
- a reading 12.04 minutes old that passes the stale check (P1),
- a stale reading with an unrounded basal of 0.83 and an issued 0.85 (P1),
- the SMB spacing boundary (P5),
- an undated reading (F-11),
- a replacement temp near the deadline of the old one (T2),
- zero temps followed by microboluses whose sum exceeds `max_iob` (I2).

These pin down the meaning of each property before any general proof. Some need T2
first. Write those right after T2.

T1. Run type and helpers. New directory `LeanAID/Time/`, Lean core only. Define `Step`,
`Run`, `stateAt` and the integral of a step function over a half-open interval. Prove
only the lemmas that T3 to T6 use. Add the directory to the layout table in
`docs/DESIGN.md`.

T2. Transition system, before any temporal property.

- Events: CGM reading (value, true time, recorded date), cycle (inputs, `Result`,
  outcome accepted or lost), user bolus.
- Command: the `Result` of a cycle gives one command with an optional temp (rate,
  duration) and an optional microbolus. The pump accepts or loses the whole command.
  Lost means never executed. Lost acknowledgements and unknown outcomes are a later
  extension, so the theorems are about an idealized exactly-once pump.
- Validation: the pump rejects a command with a non-finite rate, duration or bolus, or
  a duration outside {0} ∪ [30, 120]. A rejection is logged in the run, and the issued
  value stays visible for P1 to P3.
- Pump state: scheduled basal, or an active temp (rate, start, deadline). A new
  accepted temp replaces the active one. Duration 0 cancels it. A result without a
  `rate` changes nothing.
- Initial state: an initial history (a list of pump records) and an optional active
  temp. The rate of that temp is at most `max(M, S)`. Its remaining duration is at most
  30 minutes for a positive rate and at most 120 minutes for a zero temp.
- History encoding: a function from accepted actions to oref0 pump-history records.
  The IOB input of each cycle equals `Iob.generate` on the initial history plus the
  encoded actions of earlier steps and of the earlier events in its own step. The
  proofs use this pipeline, not an abstract ledger. A user bolus and a microbolus can
  share a timestamp. T0 checks that `Iob.generate` keeps both records.
- Legal run: the `Result` of each cycle equals `LeanAID.step` of its inputs. The run
  gives the inputs. The history is the one above. `currenttemp` comes from the pump
  state and the glucose status from the readings. `clock.now` is the step time. The
  profile is fixed, with `current_basal` from the schedule.

Environment assumptions, stated as hypotheses of the theorems, not as facts: the clock
is correct. Recorded CGM dates equal the true reading times. The profile is fixed.
`S ≤ max_daily_basal`. Concurrent loop runs, replayed or forged commands and
communication security are out of scope.

T3. Per-cycle properties lifted to runs: P1 faithful and derived, P2, P5 faithful.

T4. Prove R4 for finite durations, then P3, P4a and P4b. Record the 120-minute zero
temp after a stopped loop as a finding.

T5. P5 derived, then P6 (R20).

T6. P7: the frozen accounting lemma, I1, and the I2 counterexample. Start with the
exponential curves, where F-10 does not apply. Negative temp contributions remain
there. Then update R21 as described in section 4.2.

T7. Monitor. A decidable checker over finite runs for P1 to P6, with a theorem that it
agrees with the `Prop` definitions. For each obligation it reports satisfied, violated
or pending. Pending obligations of an observed run are never counted as passes. For P6
it checks a fixed list of window lengths, with window starts in integer milliseconds.
A breakpoint is a time where the rate changes or a bolus is accepted. A lemma reduces
"every window start" to finitely many starts: each breakpoint b and b − W, and the
starts 1 ms before and after each of these. The exact breakpoints alone are not enough.
For example, with a 30-minute window, a 2 U/h temp on [0, 30) and a bolus at minute 30,
the start at 1 ms gives more insulin than the starts at 0 and 30.

Inputs:

- synthetic runs, including SMB, lost commands, rejected commands, replacement at the
  deadline, and the T0 cases,
- runs from `sim/` with SMB turned on. `microBolusAllowed: True` alone is not enough,
  because `enableSmb` also needs a profile flag (`DetermineBasal.lean:47`). The run must
  set `enableSMB_high_bg` or `enableSMB_with_temptarget` and must assert that at least
  one microbolus was accepted. Add the SMB mode to `run_id` (`sim/harness.py:159`) so
  that SMB-on and SMB-off results do not overwrite each other.

The harness logs each action where it applies it (accepted temp, accepted bolus, lost
command) instead of rebuilding events from 5-minute rows. These logs are tests, not
proofs. The checker rejects a run with missing fields, NaN fields or times out of
order, and reports rejected runs separately from controller findings. For each
property it reports triggers, complete windows checked, pending obligations and
rejected runs. Report results in `docs/SIM.md`.

T8. Documents. Add P1, P3, P4a, P4b, P5 as new requirements in `docs/REQUIREMENTS.md`
(section E), each with source obligation, adaptation and chosen bound. Update R20 and
R21 with the result of section 4.2. Record theorems in `docs/TRACEABILITY.md`, findings
in `docs/FINDINGS.md`, and each step in `docs/LOG.md`. Change `site/index.html` only
for results that `lake build` checks. Nothing here is a claim of clinical safety.

## 6. Out of scope

As in `docs/REQUIREMENTS.md` section G, these stay out of scope:

- alarms and their timing (SR2011 1.2.8, 1.8.4, section 3),
- occlusion and air-in-line detection (SR2011 1.5, 1.6),
- clock checks (SR2011 3.3.1),
- accuracy of the pump mechanism (SR2011 1.1.2 as a hardware property, IEC
  60601-2-24). P6 uses the insulin of the pump model, not the insulin that the
  mechanism delivers,
- for the first milestone: profile changes, concurrent loop runs, delayed execution,
  lost acknowledgements, replayed or forged commands,
- the physiological meaning of IOB.

Continuous-time semantics is not used, because the pump rate is piecewise constant
between events.

## 7. Review history

Three reviews on 2026-11-19.

Round 1 changes:

- P4 was false: zero temps last up to 120 minutes. Split into P4a (expiry) and P4b
  (fail-safe bound by rate). The claim "every temp ends after 30 minutes" in section 1
  was wrong and is corrected.
- The event model separates issued, accepted and lost commands. Expiry is part of the
  state, not an event.
- P1 and P5 have a faithful rounded statement and a derived real-time statement.
- P6 has a defined quantity (an integral over the pump state) and a half-open window.
- Source obligations, adaptations and chosen bounds are separated. The library claim
  is narrowed.

Round 2 changes:

- P6: a temp accepted under one profile can run into a window under another profile.
  The first milestone fixes the profile, bounds the initial temp, and states the
  rounding allowances as explicit terms.
- P5 and P6: in one batch, two decisions can see the same history. The first milestone
  uses atomic cycles, at most one per step.
- P7: a guard plus an accounting identity does not give R21. Section 4.2 states the
  invariant first (I1, I2) and expects I2 to fail.
- P1: the reference rate is `profileCurrentBasal` (rounded), as in the existing theorem.
- T2: commands are atomic (temp and bolus together), validation is separate from
  controller output, and the IOB input comes from `Iob.generate` on an encoding of
  accepted actions.
- Finite runs are closed or observed, and the monitor reports pending obligations.
- The SMB simulation needs a profile flag, a coverage assertion and its own `run_id`.
- New modules and theorems are wired into the build and the axiom audit.
- F-13 is resolved, so section 4.2 no longer cites it as a cause.

Round 3 found no critical concerns. Changes:

- P3 needs a finite rate for the rate-dependent part. F-06 has a NaN rate with a
  finite duration.
- A step is an ordered list: environment events first, then at most one cycle. This
  fits the simulation, which records a meal bolus and runs the loop at the same time.
- The P6 window reduction includes the starts 1 ms around each breakpoint.

Not taken:

- concurrent loop runs and command security, which the atomic cycle excludes,
- a proved sim adapter. The harness logs actions directly instead,
- a check of the paywalled IEC clauses.
