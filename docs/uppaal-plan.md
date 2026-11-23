# Plan: an UPPAAL abstraction of the T2 model, then Munta

Status: plan, nothing in this file is built or checked yet. Written 2026-11-19 and
revised after nine reviews (section 10). Round 9 found no critical or major problem.

## 1. Goal and what it is not

The goal is a timed-automata model of the T2 transition system
(`LeanAID/Time/System.lean`, `docs/timing-plan.md` section 5). It serves three uses:

1. illustration: UPPAAL's simulator shows traces of the loop, the channel, the pump
   and the CGM over time. An example is the F-20 trace. In it a stopped loop leaves
   a zero temp running for 120 minutes,
2. model checking of timing properties on the abstraction,
3. exploration of the extensions that T2 leaves out (delayed execution, lost
   acknowledgements, two loops), before any Lean work on them.

The model is not a proof about oref0. The controller is replaced by a contract
(section 5). A result from UPPAAL is a result about the abstraction. A result from
Munta is a result about the abstraction from a verified checker. Neither is a `lake
build` result, and neither may be stated as "proved" on `site/index.html`. The page
and the documents say "model-checked on the abstraction" and name the tool.

Two kinds of check are kept apart in every document:

- a contract check: the property restates a guard of the contract, which comes from
  a Lean theorem. The check finds errors in the encoding, not in oref0,
- a pump check: the property is about the pump, channel and step templates, which
  are hand copies of T2 definitions. The check is a second view of a Lean theorem
  about those definitions.

## 2. Precondition: the tool rule

`AGENTS.md` allows only the oref0 checkout, Lean via `lake`, oref0's npm packages and
the kickoff Python packages. `docs/timing-plan.md` section 3.2 says that UPPAAL is not
allowed. Before U1 the maintainer changes `AGENTS.md`. The proposed text:

> - The UPPAAL model checker (`verifyta` and the GUI), installed by the maintainer
>   under an academic licence. Agents do not register or download it.
> - Isabelle and the Archive of Formal Proofs at the versions that Munta needs, and
>   Munta itself, built from source.

The maintainer also updates the sentence in `docs/timing-plan.md` section 3.2. UPPAAL
needs a licence registration, so the maintainer downloads it. Agents never create an
account or accept a licence.

## 3. The run class

The model abstracts a restricted class of T2 runs, called R_U. A later simulation
proof can only cover R_U, because behaviors outside R_U are not in the model. Every
item has a source: a hypothesis of a Lean theorem, or a modelling choice.

| item | kind | source |
|---|---|---|
| `Legal env r` | hypothesis | `LeanAID/Time/System.lean` |
| `ValidRun env r` (every cycle has `ValidInput`) | hypothesis | `p1_faithful`, `p3_temp_ok`, `p5_faithful` |
| `InvTemp env.init`: an initial temp has deadline at most 120 minutes after its start, 30 minutes for a positive rate | hypothesis | `temp_bound`, `p4b_fail_safe` |
| the run has an origin t0, at or before its first step. A run with no steps also has one. An initial temp starts at or before t0 and has a rate ≥ 0. An initial temp whose deadline is at or before t0 counts as no temp | choice | `InvTemp` alone allows a start after t0, and `tempRate` then applies the temp before its start |
| `InvRate B env.init`, `RateCap env B`, and `env.sched k ≤ B` for every k | hypothesis | `rate_envelope`, `p6_basal` |
| BolusSeen: `lastBolusTime` of a cycle is at least the time of every earlier accepted microbolus and positive user bolus, including those earlier in the same step | assumption, not proved (F-22) | T5 handoff in `docs/LOG.md` |
| the schedule has one rate for the whole run, and the rate is positive. `ValidProfile (env.profileAt t)` holds for every t | choice | removes `profileAt` changes during a run. `ValidRun` says nothing on a run without cycles. With a zero schedule rate, `basalLookup` gives `none`, so `pcb` is NaN |
| every reading is dated. Its recorded date and true time equal the time of its step, which is positive. Its value is finite and above 38 | choice | excludes F-11 and future readings. A recorded date of 0 is not truthy, so `getDateFromEntry` gives NaN for it |
| two readings are at least 150 seconds apart | choice | If the rounded gap is below 2.5 minutes, `getLastGlucose` averages two readings. Then the status date is not a reading time. With this gap, the status date is the date of the newest reading |
| `smbInterval` is a whole number of minutes, first I = 3 | choice | the conversion in 4.1 is only correct for these values |

Cycles are not restricted. Two steps can be any positive time apart, and a pause can
be as long as the run. There is no `Pmin` and no `Pmax` in the checked model. An
illustration model can add them, and its results are then not checks.

## 4. The abstraction

### 4.1 Time

Clocks are dense. The unit of the constants is one second, and events can happen at
any real time, so the model contains `stale_1204` and the millisecond boundaries.

| quantity | oref0 comparison | condition in R_U | clock constraint |
|---|---|---|---|
| fresh reading (P1) | rounded age in [−5, 12] min | age < 12.05 min (`p1_derived`, integral status date) | `fresh`, defined as `hasReading && age < 723` |
| SMB spacing (P5), whole-minute I | rounded `lastBolusAge` > I | age ≥ I + 0.05 min (derived, lemma in U1b) | `sinceBolus ≥ 60·I + 3` |
| positive temp (P3, P4b) | duration 30 | 30 min | `y ≤ 1800` |
| zero temp (P3, P4b) | duration 30 to 120 | up to 120 min | `y ≤ 7200` |

In R_U the age is never negative, because readings are not in the future. For a
fractional I, the threshold is the next tenth above I, minus 0.05 minutes, not
I + 0.05. Fractional values stay out until the threshold for binary64 arithmetic is
derived. For whole-minute I, the conversion is a derived arithmetic fact, not an
existing theorem. `Time/Examples.lean` checks it only for I = 3. U1b proves it in Lean
for I in 1..10, the range to which `smbInterval` clamps. The exact boundary at 723 seconds is pinned by the T0 boundary runs, not by
this table.

### 4.2 Steps, the start and the end

A `Step` template orders events as T2 does. It has a clock `g` since the last step. A
new step needs `g > 0`, except the first step, which can happen at t0. No time passes
inside a step. A step runs these phases in order, as a chain of committed locations:

1. environment events: readings and user boluses. A positive user bolus resets the
   bolus clocks,
2. output selection: the controller chooses the issued fields,
3. issue observation: every observer of issued values reads the fields and the clocks
   here. If its check fails, it latches an error flag,
4. channel: accepted or lost,
5. pump execution: validation, the new pump state, and the resets of accepted
   actions (a microbolus resets the bolus clocks).

A step without a cycle skips phases 2 to 5. It has no issued output and no channel
outcome, as in T2, where a step has at most one cycle (`CycleLast`). It keeps its time
and can close the run. A non-positive user bolus is a silent event: it is part of the
step and changes nothing, as `applyEvent` does. A step can consist of silent events
only.

If `busy` is false, queries read the latched flags. So an observer never reads a
clock after the reset that its own command causes.

The run starts after a pre-run phase. The pre-run phase has two independent edges,
each optional and each at a time of its own choice: the install of the initial temp,
and the last bolus before the run. They can happen in either order or at the same
time. The start event (time t0) ends the phase at any later time. If the initial temp
ends before t0, the run starts with no temp. So every pair of remaining temp time
and bolus age that `InvTemp` allows is reachable. A flag `noBolus` stands for a
history without a bolus. With `noBolus`, the model treats the spacing guard as true.
This is an abstraction choice, not a restatement of `p5_faithful`. In T2,
`Iob.generate` sets `lastBolusTime` to timestamp 0 for such a history, and
`lastBolusAge` is the time since then. For a cycle time less than `60·I + 3` seconds after the
epoch, that age fails the guard, but `noBolus` lets it pass. So the choice adds
behavior at early times. This enlarges the model, which is safe for `A[]` checks.
Replay checks it on each trace. There are no pre-run readings.

The bolus edge resets the controller clock and the observer clock for boluses, so
they start equal. Two witnesses cover the pre-run phase: a temp that starts at t0
with a bolus 3600 seconds before, and an old temp with a recent bolus.

T2 has no initial readings: `Env.init` sets only the temp, and `PState.readings`
starts empty. So the model has no pre-run readings either. Readings happen only in
steps. A flag `hasReading` is false until the first reading. The freshness guard
needs it, because `getLastGlucose` gives `none` for an empty history and
`p1_faithful` gives a glucose status. In replay, a pre-run bolus becomes a bolus
record in `initHistory`, which is pump history.

`Closed` is a location of `Step`. In it no step of any kind happens again, as on a
closed T2 run. The pump still runs. The run closes at the end of a step, in the same
committed chain, so the close time is the time of the last step. A run with no steps
closes at t0. Witnesses cover both cases. P4b measures time from the close. This bound
is weaker than the one of `p4b_fail_safe`. That theorem measures from the start of
the temp, and the start is at or before the close.

Deadline properties are stated as `A[]` safety properties over observer clocks, not
as liveness. UPPAAL does not exclude Zeno runs (infinitely many steps in bounded
time), so liveness queries need a non-Zeno check first.

### 4.3 Templates

| template | abstracts | content |
|---|---|---|
| `Step` | step order, `Legal`, closed runs | section 4.2 |
| `Controller` | `LeanAID.step` | a nondeterministic choice inside the cycle, limited by the contract of 5. It writes the issued output to shared variables before the channel acts, so observers can see issued values |
| `Channel` | `Outcome` | `accepted` or `lost` per command. `lost` changes nothing |
| `Pump` | `PState.temp`, `applyCmd`, `tempRate`, `rateIn`, `validate` | locations `Sched` and `Temp`, clock `y`, invariant `y ≤ dur`, variables `rateClass` and `dur`. The pump rejects a command in class `rejected`. An accepted temp replaces the running one and resets `y`. Duration 0 cancels. At `y == dur` the pump goes to `Sched` |
| `CGM` | `Reading`, `entries`, `getLastGlucose` in R_U | a reading resets the clock `age`. The next reading needs `age ≥ 150` |
| `User` | `Event.userBolus` | a positive user bolus resets `sinceBolus`. A non-positive user bolus is a silent event (section 4.2) |
| observers | properties | section 6 |

`Pump.Sched` is not literal T2 state: `PState.temp` keeps an expired temp, and
`tempRate` stops using it at the deadline. The model defines the delivered class `eff`. If `Pump.Temp` and `Pump.y < Pump.dur`,
`eff` is the temp class. In all other states, `eff` is the schedule. So the state at `y == dur`, before the expiry
edge, already delivers the schedule, as `tempRate` does at the deadline. The
abstraction relation maps `tempRate s k` to `eff`, not to the location.

A global flag `busy` is true inside the committed chain of a step. If `busy` is false,
observers and queries can read the state. A step can happen at the deadline of a
temp. Then the order of the expiry edge and the step does not change the state after
the step. A witness query covers this collision.

The clock `sinceBolus` resets on a microbolus that the pump accepts, and on a positive
user bolus. These are the bolus actions that T2 writes to the log.

### 4.4 Rate classes

The schedule rate is constant in R_U. Let `pcb` be
`profileCurrentBasal (env.profileAt t)`. T2 sets `current_basal` from the schedule, so
`pcb` is constant, but it can differ from the raw `env.profile.current_basal`. `B` is
the envelope of section 3.

| class | rates | note |
|---|---|---|
| `zero` | r = 0 | |
| `low` | 0 < r ≤ `pcb` | contains F-19: a rate above the unrounded schedule but not above `pcb` |
| `high` | `pcb` < r ≤ B | an increase in the sense of `Increase` |

## 5. The controller contract

The allowed outputs are exactly those that satisfy all of these at once: the field
domains below, the rate bound of `p2_rate_bound`, `TempOk` on the finite fields, the
P1 guard and the P5 guard. The generator implements this conjunction, not the table
rows one by one. If some rate in a class satisfies the
conjunction, the class is allowed. For example, with `pcb` < `rbR(maxSafeBasal)`, the
class `high` is allowed. B can be larger than `rbR(maxSafeBasal)`. Replay compares rate classes, not rates. The tables are examples of outputs that satisfy it, and each guard
names the Lean theorem, finding or assumption behind it.

Temp part:

| temp part | allowed when | source |
|---|---|---|
| none | always | a result without `rate` |
| cancel (duration 0) | always. For a `high` issued rate, the P1 guard applies | `validDuration` |
| `zero`, duration d minutes, d whole in 30..120 | always | `p3_temp_ok`, `validDuration` |
| `low`, duration 30 | always | `p3_temp_ok`, F-19 |
| `high`, duration 30 | `fresh` | `p1_faithful`, `p1_derived`, `p2_rate_bound`, `p3_temp_ok` |
| `high`, duration 0, NaN or absent | `fresh` | `p1_faithful`: `Increase` does not look at the duration. The pump rejects or cancels. A fraction is not allowed, because `TempOk` needs exactly 30 for a positive rate |

Bolus part:

| bolus part | allowed when | source |
|---|---|---|
| none | always | |
| microbolus | `fresh` and `sinceBolus ≥ 60·I + 3` | `p1_faithful` (a microbolus is an `Increase` on its own), `p5_faithful`, BolusSeen. The guard reads the clock before the command executes |

Any temp part can go with any bolus part.

The tables above list the valid outputs. The issued output also has fields for the
invalid cases. P1 and P3 observe these issued values, and the pump applies
`validate` to them:

- rate: absent, NaN, `negative`, or a class of 4.4. Under the contract (U1b) a
  negative finite rate is not possible, because `p2_rate_bound` gives a rate ≥ 0. The
  free command choice of U1a can issue it,
- duration: absent, NaN, 0, whole minutes in 30..120, or a fraction in [30, 120].
  `p3_temp_ok` does not prove that durations are whole numbers,
- bolus: absent, NaN, finite ≤ 0, or a microbolus.

The contract allows the invalid fields with three limits:

- the finite fields satisfy `TempOk`,
- the P1 trigger `rateClass == high || unitsPresent` needs `fresh`. It does not
  depend on the duration, on validation or on the outcome. `Increase` counts every
  issued `units`, NaN included, and every rate above `pcb`,
- every finite `units`, ≤ 0 included, needs `sinceBolus ≥ 60·I + 3`, because
  `p5_faithful` covers every finite issued `units`.
 The pump computes the outcome as `validate` does. It rejects the whole
command in five cases:

- one of rate and duration is present and the other is absent,
- a field is NaN,
- the duration is not valid,
- a finite bolus is ≤ 0,
- a finite rate is negative.
 A rejected
command changes nothing except the log of rejections.

The contract over-approximates `LeanAID.step` on R_U: every output that oref0 can give
there is allowed, and more. If the abstraction is sound (section 7), a safety
property that holds on the model holds on every run in R_U. A trace that UPPAAL finds
can be spurious, because oref0 can fail to give it.

## 6. Properties

Every `A[]` query has a witness query (`E<>`) for its trigger, so that a property
cannot hold because its trigger is unreachable. Each contract check also has a
mutation: the model with the guard removed must fail the query. A mutation changes
only the controller side. Each observer has its own copy of the reference predicate
(for example its own `fresh` and its own `TempOk`), which mutations do not touch.

| ID | kind | observer and query | expected |
|---|---|---|---|
| P1 | contract | on an issued output with `rateClass == high || unitsPresent` and `!fresh`, latch `Err`. `A[] not P1obs.Err`. Issued, so lost, rejected and cancelling outputs count. Mutations: remove the guard for a rejected `high` output, for a NaN or ≤ 0 `units` field, and remove only `hasReading`. Witnesses: a cycle before the first reading, and an issued `Increase` with `fresh` in the intact model | holds. Each mutation fails |
| P5-issued | contract | an observer keeps its own flag `prior` and its own clock since the last bolus. A positive user bolus and an accepted, valid microbolus set `prior` and reset the clock. A lost or rejected command does neither. At the issue observation, an issued finite `units` with `prior` true and the clock below `60·I + 3` latches `Err`. Witnesses in the intact model: a first bolus without history, a finite issued `units` with `prior` true and enough spacing, and a cycle too early that issues no `units`. In the mutation without the user-bolus reset: a bolus too soon after a user bolus. Steps can be closer than the spacing. Mutation: the controller clock is not reset on a user bolus | holds. The mutation fails |
| P5-clock | contract | the controller clock equals the observer clock: `A[] (!busy imply Controller.sinceBolus - P5obs.c == 0)`. Mutation: the controller clock is also reset on a lost or rejected command. This mutation only delays microboluses, so P5-issued cannot catch it | holds. The mutation fails |
| P5-witness | witness | an accepted valid microbolus with no `Err`, and a user bolus followed by a cycle in the same step | reachable |
| P5-pair | contract | derived check: two accepted microboluses less than `60·I + 3` seconds apart. Witness: two accepted microboluses | holds |
| P3 | contract | on every issued output, accepted, lost or rejected, check `TempOk` on its finite fields. Rejection is a separate flag and does not decide P3 | holds. Mutation fails |
| P4a | pump | on an accepted temp, an observer records its class and starts its own clock `o4`. While `o4` is below the duration, `eff` equals that class. From `o4 == dur` on, `eff` is the schedule. A later accepted temp starts a new obligation. An accepted cancel starts the obligation `eff == sched` until the next accepted temp. Mutation: the pump ignores a cancel. A microbolus does not end it. The pump clock `y` is not used, so a wrong reset of `y` fails the query | holds |
| P4b-120 | pump | at the close of the run, a clock `obs` resets. `A[] (Step.Closed && obs ≥ 7200 && !busy imply eff == sched)` | holds with any accepted command |
| P4b-30 | contract | `A[] (Step.Closed && obs ≥ 1800 && !busy imply eff is not a positive temp)`. Depends on the duration rule of `p3_temp_ok` | holds. Fails without the contract (U1a) |
| F-20 | witness | an observer flag marks a zero temp of 120 minutes accepted from a cycle. `E<> Step.Closed && flag && eff == zero && obs ≥ 7199`. A long initial temp does not set the flag | reachable |
| collision | witness | a step at the deadline of a temp that sets a new temp | reachable, and P4a holds |
| deadlock | pump | `A[] not deadlock` | holds |

P6 (window sums) and P7 (IOB) stay out. Accumulating insulin needs stopwatches or a
discrete counter, and IOB is arithmetic that the contract hides. `p6_basal` proves the
basal part in Lean. A discrete-tick variant for one small instance is optional (U5).

F-11 is outside R_U. The existing T2 run `undated_flat`
(`LeanAID/Conformance/TimeRuns.lean`) gives no increase, because flat-data handling
blocks it. So no T2 run with an F-11 increase is known. Whether one exists is an open
question. An optional variant model with undated readings can show the per-call
F-11 behavior, labelled as possibly spurious.

## 7. Soundness of the abstraction

The link between T2 and the model is the weakest point. Three levels, in order:

1. Written mapping (U1): a table from every template edge to the Lean definition and
   theorem, and from every query to its timing-plan property and its kind. Reviewed,
   not checked.
2. Trace replay (U3): every witness and counterexample trace of the U1 queries is
   turned into a T2 run with `build`. `build_legal` (`LeanAID/Time/Build.lean`) makes
   the run legal, but the controller outputs come from `build`, not from the trace.
   So a projection function in Lean maps the run to an abstract trace: event times,
   issued fields, validation outcomes and accepted actions. It also gives `rateAt` at
   the end of each step, at each temp deadline, and at the final time of the trace.
   `rateAt env r t` includes all events of the step at t, so the projection erases
   the committed transitions inside a step. If a trace needs the pump state inside a
   step, the projection folds the event prefix with `applyEvent` and reads it with
   `rateIn`. The final
   time includes the last delay, for example the time `obs ≥ 7199` of F-20. The check
   states that this projection equals the UPPAAL trace. It also states that the
   predicate of the query holds on the T2 run at that final time. It also states that
   `ValidRun` and BolusSeen hold and that the run is in R_U. The concrete check goes into
   `LeanAID/Conformance/`, because `scripts/check.sh` allows `native_decide` only there
   (F-22).

   T2 times are whole milliseconds. A UPPAAL trace is symbolic: each state has a zone
   of clock values. The replay picks one assignment of whole-millisecond times for the
   whole symbolic path, final delay included. It does not round a concrete trace, because rounding can break a
   strict guard. If the search proves that the whole path has no whole-millisecond
   assignment, the trace is shown spurious, because T2 step times are `Int`
   milliseconds. If the search fails for another reason (timeout, incomplete search,
   unsupported constraint), the trace is unresolved.

   Each trace gets one of three results: realized, shown spurious (with the reason),
   or unresolved. Not finding inputs is "unresolved", not "spurious".

   Each query has a replay category:

   | category | queries | replay |
   |---|---|---|
   | semantic | P1, P3, P4a, P4b-120, P4b-30, P5-issued, P5-pair, F-20, collision, P5-witness | the query has a T2 predicate (an `Increase` with a stale reading, a result without `TempOk`, a value of `rateAt`, and so on). If the T2 run satisfies that predicate, the trace is realized. Otherwise it is not |
   | instrumentation | P5-clock | the observable part (issued fields, accepted actions, `rateAt`) is replayed in T2. The clock check itself has no T2 counterpart. A counterexample is a fault of the model. The realized observable part does not change this |
   | transition system | deadlock | not replayed. Deadlock is a property of the automata: a finite T2 run cannot show whether the model has an enabled transition or delay at the end |

   U1a traces have free commands that no legal controller run gives. They are
   replayed on the pump alone: the accepted commands go through `applyEvent`, and
   `rateAt` is compared at the same times, as the pump examples in
   `Time/Examples.lean` do.
3. Proved simulation (later, not in this plan): a timed simulation from R_U to the
   model. Its obligations:

   - initial states: every initial T2 state in R_U maps to a reachable model state
     after the pre-run phase,
   - steps: every legal T2 step maps to a sequence of model transitions, because one
     T2 step is a committed chain of several transitions,
   - time: every delay between steps, and every delay after the close, maps to a
     model delay with the same length. Expiry happens here, without a step, so this
     obligation carries P4a and P4b,
   - observations: each observation predicate is kept, for example `eff` against
     `rateAt`, and each error flag against its T2 predicate.

   This needs the model semantics in Lean or the T2 model in Isabelle
   (`docs/ideas.md` section 1). On the Isabelle route, the proof is about the
   translated model. Its link to the Lean T2 model needs its own proof. Without that
   proof, the translation stays a stated trust assumption of the result.
   Differential tests or a shared generator do not replace the proof.

Only level 3 lets the documents say that a property holds on R_U runs because the
model satisfies it. Until then they say that the model satisfies it.

## 8. Munta

Munta (Simon Wimmer, TU Munich) is a timed-automata model checker that is verified in
Isabelle/HOL and extracted to executable code. It reads a JSON description of a
network of automata with bounded integer variables. This plan does not assume its
features. U0b tests them first.

One source describes the model: a Python script (standard library) writes both the
UPPAAL XML and the Munta JSON. The model uses only the features that U0b finds.
Translation obligations for each encoding (urgency, committed chains, observers) are
listed in `uppaal/README.md`. A verified checker makes a result certain for the model
it reads. It gives no guarantee about the generator, so the generator stays a reviewed part
without proof.

If Munta lacks a feature, a variant model is allowed only with a stated relation to
the main model, and with the same observation predicates. Only two kinds of result
transfer to the main model:

| variant | result that transfers | result that does not |
|---|---|---|
| more behaviors than the main model | an `A[]` query on state predicates holds | an `A[]` counterexample (can be spurious), and any deadlock result |
| fewer behaviors than the main model | an `E<>` query is reachable | an `E<>` query is unreachable |

Deadlock does not transfer by behavior inclusion, because it depends on the
transitions and delays that a state allows. A variant with an extra self-loop has more
behaviors and can be free of deadlock while the main model is not. If the relation also keeps
deadlocks and delays, a deadlock result of a variant transfers. Otherwise it does not.

`results.json` records the relation and the transfer status of each result. When U4
compares Munta and UPPAAL, a difference on a result that does not transfer is
expected and recorded, not a fault.

## 9. Work items

Each item ends with a local commit. Results go to `docs/LOG.md`, findings to
`docs/FINDINGS.md`.

U0. Tool rule. The maintainer changes `AGENTS.md` (section 2) and installs UPPAAL.

U0b. Munta compatibility. Build Munta from source against the Isabelle and AFP
versions it needs, installed apart from the local development Isabelle. Check a small
network with one synchronization, a bounded integer update, a deadline edge, a
committed chain and each query form that section 6 uses. Include a model with a
deadlock and a model with a loop that takes no time, and record what Munta reports for
each. Record the supported features and the versions.

U1a. Pump first. The `Step`, `Channel` and `Pump` templates with a free command
choice: any issued fields of section 5, the `negative` rate included, and also
durations that `validDuration` rejects (−1, 1 and 121 minutes). Queries: P4a, P4b-120, the collision witness and the
deadlock check. A witness shows that P4b-30 fails without the contract: the pump
accepts a positive temp of 120 minutes. This shows that P4b-30 rests on `p3_temp_ok`,
not on validation. A witness shows that a command with an invalid duration and a
positive bolus executes neither part. A mutation that removes the upper bound of
`validDuration` must fail P4b-120.

U1b. Contract. Prove the SMB conversion of 4.1 in Lean. The lemma is about whole
milliseconds and the binary64 operations of `lastBolusAge`. Let I be in 1..10 and e
be the elapsed time in whole milliseconds. The lemma states: the guard passes exactly
for e ≥ 60000·I + 3000. The proof checks e = 60000·I + 3000 and the millisecond before it
for each I, and uses monotonicity for the rest. It makes no claim for fractional
ages. A second lemma relates the age that `lastBolusAge` reports to the time since the
real prior bolus, under BolusSeen. Add the `Controller`, `CGM` and `User` templates
and the contract of section 5 in `uppaal/`. Add the P1, P3, P5-issued, P5-clock, P5-pair, P5-witness and P4b-30 queries with their witnesses and
mutations, and the F-20 witness. A script
`scripts/uppaal.sh` runs every query. It writes `uppaal/results.json`. The file
holds the repository revision and a dirty-tree flag. It also holds hashes of the model
and query files, the parameters, the tool version and the command line. Each result is one of: holds,
fails, reachable, unreachable, parse error, timeout, unsupported. If a result is not the expected one, the script exits non-zero.

U2. Traces for illustration. Witness traces from `verifyta -t`. A Python script
(standard library) renders each as an SVG timeline under `uppaal/traces/`.

U3. Replay of every trace of U1 and U2, as in section 7 level 2.

U4. Munta run. Generate the Munta model, run the supported queries, compare with
`uppaal/results.json`, and record every difference.

U5. Extensions. Before any query, write the semantics of each extension:

- delayed execution: the decision state (a snapshot of the inputs) is separate from
  the pump state at execution. Commands wait in a queue,
- lost acknowledgement: execution and acknowledgement are separate events. A retry
  sends the same command again (same identity), not a new decision,
- two loops: each takes its own snapshot, so both can decide on the same old history.
  The guard on `sinceBolus` reads the snapshot, not the current clock.

Then check P4b and P5. These traces cannot be T2 runs, because T2 excludes these
behaviors. They are reported as candidate findings that wait for an extended T2 in
Lean. Optional: a discrete-tick P6 instance.

U5b. A smaller pump for Munta. In U4, Munta timed out on every query that needs the
U1a pump (122 locations, about 11,500 edges after lowering). Build a pump with fewer
durations, in the way U4 reduced the durations of `nopump`, and state its relation to
the U1a pump: which answers transfer, and why. Then run the pump queries in Munta and
compare with `uppaal/results.json`. This item does not depend on U5. It uses the U1a
pump, not the U5 extensions.

U6. Documents:

- the layout table in `docs/DESIGN.md`,
- `docs/TRACEABILITY.md`: a column for model-checked results with the kind of check,
  kept apart from proved results,
- `site/index.html`: only results that `scripts/uppaal.sh` produces, marked as
  model-checked.

## 10. Review history

Round 1 (Codex, 2026-11-19) found three critical problems. They are fixed as follows:

- The microbolus guard depended on the temp guard, so a microbolus with a zero temp
  passed a stale reading. The bolus part now has its own freshness guard.
- The model claimed to cover every T2 run, but `Pmin`, `Pmax` and `Gmin` excluded legal
  runs. Section 3 now defines the run class R_U, and cycles are unrestricted.
- The SMB conversion was wrong for fractional intervals (I = 3.01). R_U now has
  whole-minute intervals only.

Other changes:

- dense clocks,
- the effective status date and the 150-second gap between readings,
- independent temp and bolus parts, and the `rejected` class,
- defined rate classes and a constant schedule,
- the abstraction relation for expired temps,
- the pre-run phase for the initial state,
- closed runs without any later step,
- issued values for P1, and real observers for P3, P4a and P4b,
- witnesses and mutations against vacuous results,
- F-11 as an open question, not an existing T0 run,
- replay in `Conformance` with three results,
- Munta tested before U1, and one model source for both tools,
- explicit semantics for the U5 extensions,
- full reproducibility data in `results.json`.

Round 2 (Codex) found one critical problem. `InvTemp` allowed an initial temp that
starts after the run starts, so R_U contained runs that the model excludes. R_U now
requires a start at or before t0 and a rate ≥ 0. Other changes:

- `rejected` is not outside `TempOk`. P3 now checks `TempOk` on the finite issued
  fields, and rejection is a separate flag computed as `validate` does,
- P3 and P4b-30 are contract checks. The pump alone accepts a positive temp of 120
  minutes, and U1a shows this,
- the delivered class `eff`, the `busy` flag, a collision witness, a deadlock check
  and an independent clock for P4a,
- replay checks that the projection of the T2 run equals the trace, and picks
  whole-millisecond times from the zones,
- the F-20 witness needs a zero temp accepted from a cycle,
- a table of which variant results transfer,
- a recorded date of 0 is excluded, and the status date is the newest reading date,
- the envelope needs `env.sched k ≤ B`, and `pcb` uses `env.profileAt t`.
- a present bolus field of any value needs a fresh reading, as `Increase` requires.

Round 3 (Codex) found no critical problem. Changes:

- the P1 trigger is `rateClass == high || unitsPresent` for every issued output, with
  any duration field, and has two more mutations,
- R_U requires a positive schedule rate and `ValidProfile` at every time, so `pcb` is
  finite on runs without cycles. Every run has an origin t0,
- deadlock results do not transfer by behavior inclusion, and U0b tests a deadlock and
  a loop that takes no time,
- P5-issued checks issued values against an independent bolus clock, with mutations
  for the user-bolus reset and for lost or rejected commands,
- the spacing guard covers every finite `units`, as `p5_faithful` does,
- the SMB conversion is a derived fact that U1b proves in Lean for I in 1..10,
- BolusSeen includes positive user boluses earlier in the same step.

Round 4 (Codex) found no critical problem. Changes:

- the mutation "reset on a lost or rejected command" cannot fail P5-issued, because
  it only delays microboluses. A new query P5-clock catches it,
- a step has five phases, and issued values are observed in phase 3, before the
  channel and the pump. Errors are latched,
- replay compares `rateAt` at deadlines and at the final time, and checks the query
  predicate on the T2 run. U1a traces are replayed on the pump alone,
- U1a can issue a negative rate, which the pump rejects,
- the first step can happen at t0, and the run closes at the end of its last step.

Round 5 (Codex) found no critical problem. Changes:

- level 3 is a timed simulation, with obligations for initial states, steps, delays
  (expiry included) and observations,
- each query has a replay category: semantic, instrumentation or transition system,
- pre-run readings and boluses have a replay mapping, and `hasReading` guards
  freshness,
- the contract is the conjunction of its constraints. The tables are examples, and
  the row for a `high` rate no longer allows a fractional duration.

Round 6 (Codex) found no critical problem. Changes:

- the P1 observer and contract need `hasReading`, with a mutation and a witness,
- a step without a cycle skips phases 2 to 5, and a non-positive user bolus is a
  silent event,
- the model has no pre-run readings, so replay keeps the close time,
- admission of a rate class: some rate in it satisfies the contract,
- on the Isabelle route, the link to the Lean model needs its own proof or stays a
  trust assumption.

Round 7 (Codex) found no critical problem. Changes:

- the pre-run phase installs the initial temp and the last bolus by independent
  edges, so every allowed pair is reachable, with `noBolus` and two witnesses,
- `fresh` is one predicate, used in every guard and observer,
- U1a issues durations that `validDuration` rejects, with a witness and a mutation,
- replay reads `rateAt` at step ends and erases the transitions inside a step.

Round 8 (Codex) found no critical problem. Changes:

- P5-issued checks spacing only after a real prior bolus (`prior`), and `noBolus` is
  a stated abstraction choice, checked on replay against `lastBolusTime` = 0,
- mutations change only the controller side, and observers keep their own reference
  predicates,
- a proof that no whole-millisecond assignment exists makes a trace shown spurious,
  and only a failed search leaves it unresolved.

Round 9 (Codex) found no critical or major problem and ended with "no further review
needed". Its minor points are applied:

- an accepted cancel starts the obligation `eff == sched`, with a mutation,
- the P5 witnesses name their model, intact or mutated,
- `noBolus` adds behavior at early times, which is safe for `A[]` checks,
- the SMB lemma is stated for whole milliseconds and binary64 operations.
