# UPPAAL abstraction of the T2 model

This directory holds the timed-automata model of `docs/uppaal-plan.md`. The model
describes the T2 run model of `LeanAID/Time/System.lean` at the level of rate
classes and whole-minute durations. UPPAAL checks queries on the model. A result
is about the model. Section 7 of the plan describes how a result can carry over to
T2 runs. That link is not built yet (see "Status").

Research artifact. Nothing here is fit for dosing insulin.

## Status

| work item | content | status |
|---|---|---|
| U0b | Munta compatibility (`u0b/README.md`) | done |
| U1a | `Step`, `Channel` and `Pump` with a free command choice | done: every query gives its expected result |
| U1b | contract, `Controller`, `CGM`, `User`, Lean SMB lemma | done: every query gives its expected result |
| U2 | SVG timelines of the witness traces and counterexamples (`traces/`) | done |
| U3a | replay of the U1a traces on the T2 pump (`replay.py`, `../LeanAID/Conformance/UppaalReplay.lean`) | done |
| U3b | replay of the U1b traces on legal T2 runs (`../LeanAID/Conformance/UppaalReplayU1b.lean`) | done, see "Replay on T2 (U3b)" |
| U4 | Munta run (`u4/`) | done: Munta confirms 21 data-only queries, times out on the pump networks. See "Munta run (U4)" |
| U5 | extensions: delayed execution, lost acknowledgement, two loops (`extensions.md`) | done: P4b and P5 on each extension. The failures are candidate findings, not T2 results. See "Extensions (U5)" |

## How to run

```bash
scripts/uppaal.sh
```

The script runs `uppaal/check.py` with `verifyta` from `/opt/uppaal`. The
environment variable `VERIFYTA` names another binary. `--only ID ...` runs some
queries and does not write `results.json`. The script writes the models and query
files to `out/`, which git ignores, and the results to `results.json`. If a result
is not the expected one, the script exits with 1.

`results.json` holds the run data: the repository revision, the tool version, the
command line, the timeout and the parameters of the main model. It also
holds a flag for uncommitted changes. The flag is set by a change to a tracked file
anywhere in the repository, or by an untracked file under `uppaal/`. It
also holds the SHA-256 sums of `model.py` and `check.py`. For each query, it holds
the query text, the expected and actual status, the time, and the SHA-256 sums of
the model and query files. It also holds the relation of the model to the main
model, and what the result says about the main model. A mutation result is about
the mutant only. An `A[]` query `holds` or `fails`. An `E<>` query is
`reachable` or `unreachable`. The status `parse error` means that UPPAAL rejected
the model or the query. The status `error` means any other run without exactly one
answer. The status `unsupported` is used only by the Munta run of U4. The status `timeout` means 1800 s passed.

## Files

| file | content |
|---|---|
| `model.py` | the model as Python data, and a writer for UPPAAL XML |
| `munta.py` | U4: the lowering for Munta, its reductions, and the Munta JSON writer |
| `munta_order.sh` | U4: builds a diagnostic copy of Munta that prints its variable order |
| `u4/` | work item U4: `run_u4.py`, `results.json`, `test_lower.py`, and the networks of the two Munta findings |
| `check.py` | the queries with their expected status, the runner and the `results.json` writer |
| `results.json` | the results of the last full run |
| `traces.py` | U2: writes a shortest trace and an SVG timeline for each witness and counterexample |
| `traces/` | the traces, the timelines and `index.md` |
| `extensions.md` | U5: the semantics of the extensions and their relation to the U1b model |
| `traces/u5/` | U5: the traces of the extensions (`traces.py --u5`), not replayed in U3 |
| `replay.py` | U3a: writes the Lean replay of the U1a traces, and `replay.json` |
| `replay.json` | the replay result of each trace |
| `u0b/` | work item U0b |
| `../LeanAID/Time/SmbSpacing.lean` | the SMB lemmas of U1b, checked by `lake build` |

## The U1a model

One model time unit is one second. T2 times are milliseconds. Durations are whole
minutes. The model has two processes.

`Step` runs the steps of a run. A step is a chain of committed locations. No time
passes inside a step. No other process moves inside a step, except the pump on a
synchronization. The variable `busy` is 1 inside the chain. The pump queries
P4a, P4b-120 and P4b-30-free look only at states with `busy == 0`, which are the
states between steps. The queries `bolus` and `deadlock` look at states inside a
step.

1. Pre-run (`Pre`, `PreC`): an optional initial temp, sent on `initTemp`. Its class
   (`zero`, `low` or `high`) is a free choice.
2. Start (`Pre` to `Idle`) at t0, or close at t0 with no steps (`Pre` to
   `Closed`).
3. A step (`Idle` to `S1`): the first step can be at t0, later steps need time
   to pass (`g > 0`).
4. Phase 1 (readings and user boluses) is empty in U1a. A step can end here,
   which is a step without a cycle.
5. Phase 2 (`S1` to `Iss`): a free choice of the issued fields `rc`, `dk`, `dv`,
   `uk` (encodings below).
6. Phase 3 (`Iss` to `Ch`): the issue observation. Observers come in U1b.
7. Phase 4, the channel (`Ch`): the command is lost (to `End`) or accepted (to
   `Ex`). On the accepted edge, the observer sets the expected effect (see
   "Observers").
8. Phase 5, execution (`Ex` to `End`): one edge for each reason to reject, and
   edges for a valid command without a temp part, a valid cancel and a valid temp,
   each with and without a bolus. A valid cancel sends `cancel`, a valid temp sends
   `setTemp`. A valid bolus sets `bolusDone`.
9. End of step (`End`): the issued fields and the bolus flags are cleared. The run continues (to
   `Idle`) or closes (to `Closed`) in the same chain, so the close time is the time
   of the last step. `Closed` has a self-loop that changes nothing.

`Pump` has the locations `Sched` (the schedule runs) and `Temp` (a temp is
stored). Its clock `y` is the time since the stored temp started. The variables
`dur` and `tcls` hold the duration in minutes and the rate class. The invariant
`y <= dur * 60` of `Temp` and the edge to `Sched` at `y >= dur * 60` give expiry
at the deadline. A new temp resets `y`. A cancel goes to `Sched`.

The delivered class is `eff`. If `Pump.Temp && Pump.y < dur * 60`, `eff` is the
temp of class `tcls`. Otherwise `eff` is the schedule. At `y == dur * 60` the
schedule runs. This agrees with `tempRate`, where the temp runs only for
`k < deadline`.

### Observers

The observers keep the expected behavior apart from the pump edges, so a fault in
the pump edges cannot also change what is expected.

The observer starts with the obligation `eff == sched`. The pre-run edge that sends
`initTemp` gives it the obligation of the initial temp, with its own copy of the
duration of each class.

The accepted edge of the channel has one edge for each outcome of the observer's
own copy of `validate`. This copy uses the bound 120, which no mutation changes.

- A valid temp starts a P4a obligation: `oCls` and `oDur` get the class and the
  duration, and the observer clock `o4` is reset.
- A valid cancel starts the obligation `eff == sched` (`oCls == 9`).
- A valid command with a positive bolus sets `expB`.
- A rejected command or a command without a temp part leaves the obligation as it
  was.

A lost command passes no observer edge. The query `bolus` compares `expB` with
`bolusDone` at the end of each step.

### Encodings of the issued fields

| variable | values |
|---|---|
| `rc` (rate) | 0 absent, 1 NaN, 2 negative, 3 `zero`, 4 `low`, 5 `high` |
| `dk` (duration kind) | 0 absent, 1 NaN, 2 not whole and in [30, 120], 3 whole, 4 not whole and outside [30, 120] |
| `dv` (duration value) | if `dk == 3`, whole minutes in −1..121. Otherwise 0 |
| `uk` (units) | 0 absent, 1 NaN, 2 finite and ≤ 0, 3 positive (a microbolus) |

The value −1 stands for every negative whole duration, and 121 for every whole
duration above 120, because `validDuration` treats them alike. 1..29 are the
rejected durations between 0 and 30. A non-whole duration is always rejected, so
its value matters only for `TempOk` (U1b): `dk` 2 and 4 tell a fraction inside
[30, 120] from one outside it.

### Mapping to T2

This is level 1 of section 7 of the plan: a written mapping, reviewed, not
checked.

| model | T2 (`LeanAID/Time/System.lean`) |
|---|---|
| reject reason `presence`: one of `rc`, `dk` is 0 and the other is not | `validateTemp`: the case `_, _ => none` for one field present |
| reject reason `nan`: `rc`, `dk` or `uk` is NaN | `validateTemp`, `validateBolus`: NaN gives `none` |
| reject reason `duration`: not whole, below 0, 1..29 or above 120 | `validDuration` |
| reject reason `bolus`: `uk == 2` | `validateBolus`: `0 < u` fails |
| reject reason `negative`: `rc == 2` with a duration | `validateTemp`: `0 ≤ r` fails |
| reject edges change no pump variable and no bolus flag | `applyEvent`: a rejected command only adds to `rejected` |
| valid without temp part: `rc == 0 && dk == 0` | `validateTemp`: `none, none => some none` |
| valid cancel: `dv == 0`, sends `cancel` | `applyCmd`: `d = 0` sets `temp := none` |
| valid temp: `dv` in 30..120, sends `setTemp`, pump sets `y = 0`, `dur`, `tcls` | `applyCmd`: `start := t`, `deadline := t + d * 60000` |
| a valid bolus sets `bolusDone` and changes no pump variable | `applyCmd`: a bolus only adds to `log` |
| lost command (`Ch` to `End`) | `applyEvent`: `.lost => s` |
| expiry edge, invariant of `Temp`, `eff` | `tempRate`: temp rate for `k < deadline`, else the schedule |
| initial temp | `Env.initTemp` under `InvTemp`, with a rate ≥ 0 and a start at or before t0 (R_U, section 3 of the plan) |
| start (`Pre` to `Idle`) at t0, first step at t0 or later, later steps strictly later (`g > 0`) | the run is increasing in time, from the origin t0 |
| step without a cycle (`S1` to `End`) | a step with no `cycle` event. Readings and user boluses come in U1b |
| close (`End` to `Closed`, or `Pre` to `Closed`) and clock `obs` | the final time of a run, measured from its last step |
| self-loop on `Closed` | no T2 counterpart. It only removes the deadlock at the end of a run |

The initial temp gets the longest duration of its class: 120 minutes for `zero`
and 30 minutes for `low` and `high`. It is installed at any time at or before t0,
so at t0 it has any remaining time in its range, or it is expired. This covers
every initial temp that `InvTemp` allows with a rate ≥ 0 and a start at or before
t0. `InvTemp` alone does not require the rate to be ≥ 0. R_U does.

### Abstraction choices

- The rate is a class, not a number. The schedule is one class, `sched`.
- `low` and `high` differ only in U1b, where the P1 trigger looks at them.
- The free command choice issues any combination of fields, also the ones that
  `LeanAID.step` cannot give. So a U1a result says what the pump does with any
  command, not what the controller issues.
- The issued fields are cleared at the end of each step, and the witness flags
  exist only in the witness model. Neither changes the behavior of the other
  variables. Both keep the state space small. In one earlier run, with the fields
  kept and the flags in every model, P4a, P4b-120 and the deadlock query did not
  finish in 1800 s. That run is not archived.

### Queries

The queries are in `check.py`. `RUNNING` says that the P4a observer holds a temp
obligation and its clock `o4` is below the obligation duration. `EXPIRED` says
that `o4` is at or above that duration.

| ID | kind | query | expected |
|---|---|---|---|
| P4a | pump | between steps: a running obligation gives `eff` of its class, an expired one gives the schedule, a cancel obligation gives the schedule | holds |
| P4a-w-running, P4a-w-expired, P4a-w-cancel | witness | each trigger of P4a is reachable. The cancel witness needs a cancel while the temp still runs (`y < dur * 60`) | reachable |
| collision | witness | a step at the deadline of a temp sets a new temp | reachable |
| P4b-120 | pump | 7200 s after the close, between steps, `eff` is the schedule | holds |
| P4b-120-w | witness | a temp still runs 7199 s after the close | reachable |
| P4b-30-free | pump | 1800 s after the close, `eff` is not a positive temp | fails |
| P4b-30-free-w | witness | a positive temp of 120 minutes runs 1800 s after the close | reachable |
| bolus | pump | at the end of each step, `bolusDone == expB` | holds |
| bolus-w | witness | a valid bolus executes | reachable |
| reject-bolus-w | witness | in one step, a command with an invalid duration and a positive bolus is rejected, and no bolus executes | reachable |
| close-no-steps-w | witness | a run closes at t0 with no steps | reachable |
| deadlock | pump | `A[] (!deadlock)` | holds |
| M-no-upper-bound | mutation | P4b-120 with `validDuration` accepting 121 minutes | fails |
| M-ignore-cancel | mutation | P4a with a pump that keeps its temp on a cancel | fails |
| M-missing-reject | mutation | the deadlock query with no edge for the reject reason `bolus` | fails |
| M-reject-initial | mutation | P4a with a pump that ends the initial temp on a command rejected for its duration | fails |
| M-drop-temp | mutation | P4a with a pump that drops an accepted valid temp of 30 minutes | fails |
| M-reject-bolus | mutation | `bolus` with a pump that executes the bolus of a command rejected for its duration | fails |
| M-no-y-reset | mutation | P4a. If a new temp replaces a running one, the pump does not reset `y` | fails |

P4b-30-free fails as the plan expects: the pump alone accepts a positive temp of
120 minutes. P4b-30 rests on the duration rule of `p3_temp_ok`, which U1b adds as
the contract.

The P4a observer uses its own clock `o4`, not the pump clock `y`, so a wrong reset
of `y` fails P4a (M-no-y-reset). The obligation comes from the channel edge, not
from the pump edge, so a pump that drops a valid temp fails P4a (M-drop-temp). A
command with an invalid duration and a positive bolus executes neither part: the
query `bolus` covers the bolus, and P4a covers the temp, because the obligation
stays as it was. An obligation exists in every state, also before the first
accepted command, so P4a also covers the initial temp (M-reject-initial). The deadlock query also checks that phase 5 has an
edge for every issued command. `Ex` is committed, so a command without an edge
blocks time (M-missing-reject).

## The U1b model

U1b adds the controller side to the U1a model (`build(contract=True)`). The
section numbers below are those of `docs/uppaal-plan.md`.

- `CGM`: the first reading sets `hasReading`. A later reading needs
  `hasReading == 1` and `age >= 150`. Each reading resets the clock `age`. A reading
  observer on the step edge checks this with its own flag and clock (query `cgm`).
- `User`: a positive user bolus resets the controller clock `sinceBolus`. A
  non-positive user bolus is a silent event and has no edge.
- Pre-run: an optional bolus before the run, at a time of its own, resets
  `sinceBolus`. Without it, the flag `noBolus` stays 1 and the spacing guard counts
  as true (section 4.2).
- Phase 1 of a step: an optional reading, then an optional positive user bolus.
- Phase 2: `Controller` chooses the issued fields under the contract of section 5.
- Phase 3: the observers of P1, P3 and P5 read the issued fields and latch `err1`,
  `err3` or `err5`.
- An accepted valid microbolus resets `sinceBolus`. The observers of P5 and P5-pair
  reset their own clocks `p5c` and `pb` on the accepted edge of the channel.

### The contract

The controller can issue any field values that satisfy all of these:

- rate: absent, NaN, `zero`, `low` or `high`, never negative (`p2_rate_bound`),
- duration: absent, NaN, 0, whole in 30..120, or a fraction in [30, 120],
- `TempOk` on the finite fields (`p3_temp_ok`): with a finite rate, the duration is
  0, any allowed value for `zero`, or exactly 30 for `low` and `high`,
- P1: a `high` rate or any units field (NaN included) needs `fresh`, which is
  `hasReading == 1 && age < 723` (`p1_faithful`, `p1_derived`),
- P5: finite units (≤ 0 included) need `noBolus == 1` or `sinceBolus >= 183`
  (`p5_faithful`, `smb_spacing` for I = 3, BolusSeen).

`model.py` writes the contract as one `Controller` edge for each block of field
values and each case of the P1 and P5 guards. A `select` ranges only over the
duration values of the block. One edge with a `select` over all fields and a long
guard made UPPAAL evaluate the guard 14,760 times in every state.

### The SMB lemmas

`LeanAID/Time/SmbSpacing.lean` proves the conversion of section 4.1, checked by
`lake build`:

- `smb_guard_iff`: for a whole-minute interval I in 1..10 and an elapsed time e in
  whole milliseconds, `lastBolusAge` exceeds I exactly when e ≥ 60000·I + 3000. The
  kernel checks both boundary values for each I. Monotonicity of the binary64
  operations gives the rest.
- `lastBolusAge_guard_iff`: the same for the guard of a context, with no bound on
  the times. The subtraction `now - lastBolusTime` is rounded to binary64, and the
  rounding is monotone and exact at the two boundary values.
- `smb_spacing`: if the guard passes and `lastBolusTime` is a whole millisecond at or
  after a real prior bolus, at least 60000·I + 3000 ms passed since that bolus.
  BolusSeen is a hypothesis of this theorem, not a proved fact (F-22).

So for I = 3 and whole milliseconds, the guard of oref0 is exactly "at least
183,000 ms since `lastBolusTime`". The model clock `sinceBolus` measures the time
since the last real bolus. Under BolusSeen, `lastBolusTime` is at or after that
bolus, so the oref0 guard implies `sinceBolus >= 183`. The converse can fail when
`lastBolusTime` is later than the real bolus. So the clock constraint is a sound
relaxation of the oref0 guard, which is what an over-approximating contract needs.
It is exact when `lastBolusTime` is the time of the real bolus.

### Model variants

The full contract model is too large: P1 did not finish in 1800 s. The cause is
the 91 duration values together with 8 clocks. So each U1b query runs on the
smallest model that answers it. `results.json` records the variant and its
relation to the main model for each result.

| variant | content | relation to the main U1b model |
|---|---|---|
| `contract` | the main U1b model | itself |
| `nopump` | the main model without `Pump` and the P4a observer | same runs on its variables. `Pump` never blocks `Step`: it has a receiving edge for every value of its guards, and its expiry edge releases its invariant. This is an argument, not a check |
| `nobolus` | the main model without user boluses, the pre-run bolus and outputs with units | fewer behaviors: a reachable result transfers. Used for R-F-20 (U3b) |
| `relaxed` | the U1a model, with the command choice limited to the field domains and `TempOk` of the contract | more behaviors on the pump, the P4a observer and the close: it has no freshness or spacing guard, and readings, user boluses and observers change no pump variable. An `A[]` result that holds transfers |

The witnesses F-20, `prerun-w-t0` and `prerun-w-old` run on the full contract
model. Breadth-first search finds the pre-run witnesses at once. Depth-first
search finds F-20.

### U1b queries

`fresh` is `hasReading == 1 && age < 723`. `SPACING` is 183 s.

| ID | kind | variant | query | expected |
|---|---|---|---|---|
| P1 | contract | nopump | `A[] (err1 == 0)`: an issued `high` rate or units field comes with `fresh` | holds |
| P1-w-noread, P1-w-inc | witness | nopump | a cycle before the first reading; an issued Increase with `fresh` | reachable |
| M-P1-rejected-high, M-P1-nan-units, M-P1-no-hasreading | mutation | nopump | P1 when the controller drops the guard for a rejected `high` rate, for NaN or ≤ 0 units, or drops only `hasReading` | fails |
| P3 | contract | nopump | `A[] (err3 == 0)`: every issued output satisfies `TempOk` | holds |
| M-P3-positive-120 | mutation | nopump | P3 when the controller issues a positive temp of 120 minutes | fails |
| P5-issued | contract | nopump | `A[] (err5 == 0)`: issued finite units after a real prior bolus come at least `SPACING` after it, by the observer's own clock | holds |
| P5-w-first, P5-w-spaced, P5-w-early | witness | nopump | finite units with no prior bolus; with enough spacing; a cycle too early issues no units | reachable |
| M-P5-user, M-P5-user-w | mutation, witness | nopump | without the reset of `sinceBolus` on a user bolus, P5-issued fails, and finite units are issued too soon after a user bolus | fails, reachable |
| P5-clock | contract | nopump | between steps, `sinceBolus - p5c == 0` | holds |
| M-P5-clock | mutation | nopump | P5-clock when `sinceBolus` is also reset on a lost or rejected command | fails |
| P5-pair, P5-pair-w | contract, witness | nopump | two accepted microboluses are at least `SPACING` apart; two of them happen | holds, reachable |
| P5-w-bolus, P5-w-user-cycle | witness | nopump | an accepted valid microbolus with no error; a user bolus and a cycle in one step | reachable |
| cgm | pump | nopump | every reading sets `hasReading`, and readings are at least 150 s apart by the observer's clock | holds |
| cgm-w | witness | nopump | a reading in a step | reachable |
| M-cgm-first | mutation | nopump | `cgm` when CGM can take the first reading without setting `hasReading` | fails |
| deadlock-contract | pump | nopump | `A[] (!deadlock)` | holds |
| P4b-30 | contract | relaxed | 1800 s after the close, no positive temp runs | holds |
| M-P4b-30 | mutation | relaxed | P4b-30 when the controller issues a positive temp of 120 minutes | fails |
| F-20 | witness | contract | a zero temp of 120 minutes from a cycle still runs 7199 s after the close | reachable |
| prerun-w-t0, prerun-w-old | witness | contract | at t0 a temp starts and the pre-run bolus was 3600 s before; at t0 an old temp runs and the last bolus was recent | reachable |

## Traces (U2)

```bash
python3 -I uppaal/traces.py --verifyta /opt/uppaal/lib/app/bin/verifyta.sh
```

For every query whose expected status is `reachable` or `fails`, the script asks
`verifyta -t1` for a shortest concrete trace. It writes the trace as verifyta prints
it (`traces/ID.trace`) and a timeline (`traces/ID.svg`). `traces/index.md` lists the
38 traces with the model and the SHA-256 sums of the model and query files.
`--only ID ...` renders some traces and does not write the index.

The script checks that verifyta ends with exit code 0 and gives the expected answer.
Its parser accepts only the trace grammar of verifyta and stops at any other line,
with the line number.

A timeline has one column for each time at which transitions happen, and the delays
between the columns. Times are model seconds relative to the start t0, so pre-run
events have negative times. A trace that ends before t0 (`P4a-w-running`,
`P4a-w-expired`) shows elapsed model time instead. Each action comes from the edges
that the trace takes and the states around them, so a mutation trace shows what the
mutant does. Next to the execution, the label `validate: ...` gives what `validate`
expects for the issued fields. The lanes show the run (start, steps, close), CGM and
user events, the issued output, the channel and pump execution, pump events (a new
temp, a cancel, an expiry), and errors that observers latch. A band shows the
delivered class `eff` during each delay. The last column is the end of the trace,
which can be inside a step: for example, `P5-pair-w` ends on the accepted edge of
the second microbolus.

The traces show the model and its variants, not T2 runs. A mutation trace shows the
mutant. U3 replays the traces on T2. In the 38 traces, every delay is a whole
number of seconds.

## Replay on T2 (U3a)

```bash
python3 -I uppaal/replay.py
lake build LeanAID.Conformance.UppaalReplay
```

U1a traces have free commands, which no legal controller run gives. So each U1a
trace is replayed on the T2 pump alone (section 7, level 2 of the plan).
`replay.py` reads the trace and writes `LeanAID/Conformance/UppaalReplay.lean`:

- a T2 environment with the initial temp that the trace installs before t0,
- a T2 run with one step for each cycle of the trace, at the same time, with the
  issued fields as the result and the channel outcome of the trace,
- the projection that the trace shows: for each cycle, its outcome, the pump action
  and whether a bolus is delivered; and the delivered rate at the end of each group
  of transitions between steps (and at the end of the trace after a completed
  execution), and 1 ms before and at each deadline inside a delay,
- a theorem that `traceMatch` of the run and the projection is `true` (realized) or
  `false` (not realized), and a theorem that the schedule is 1 U/h at every
  checkpoint.

`LeanAID/Time/Replay.lean` defines the projection on the T2 side: `obsOf` executes a
cycle as `applyEvent` does, and `rateObs` is `rateAt`, the temp or the schedule. The
environment has a schedule of 1 U/h. Classes are rates: the schedule 1, `zero` 0,
`low` 1/2, `high` 2. `rateAt` reads the schedule with `basalLookup`, which the kernel
does not reduce (F-22), so the theorems use `native_decide`, which
`scripts/check.sh` allows in `LeanAID/Conformance/` only. Model time s is T2
time T0 + 1000·(s − t0) ms. A trace that ends before t0 takes its end as t0.

| trace | result |
|---|---|
| the 9 U1a witnesses, P4b-30-free | realized |
| the 6 U1a mutations other than M-missing-reject | not realized, as expected |
| M-missing-reject | not replayed: deadlock is a property of the automata |

For each mutation, the T2 projection differs from the trace exactly at the fault:
T2 rejects the 121-minute temp (M-no-upper-bound), ends the temp on a cancel
(M-ignore-cancel), keeps the initial temp on a rejection (M-reject-initial), sets the
valid temp (M-drop-temp), gives no bolus on a rejection (M-reject-bolus), and runs the
new temp from its own start (M-no-y-reset).

The runs are not legal runs: their results are given, not computed by
`LeanAID.step`. The U1b traces are replayed in U3b, where the controller output must
come from `LeanAID.step`.

## Replay on T2 (U3b)

U1b traces come from the contract model, so their T2 runs must be legal: `build`
makes each run from a script at the times of the trace, and `LeanAID.step` computes
every issued output. `replay.py` chooses the script: readings that rise from
150 mg/dL by 20 (profile `profS`, microboluses on) or, if the trace issues a zero
temp, fall from 80 mg/dL by 10 (profile `prof`); a user bolus of 1 U; the channel
outcome of the trace. The profiles and free inputs are those of
`LeanAID/Conformance/TimeRuns.lean`. For each trace,
`LeanAID/Conformance/UppaalReplayU1b.lean` checks:

- `legal_*`: the run is legal (`build_legal`),
- `replay_*`: the projection of the run equals the trace. Per step: a reading, a
  positive user bolus, the issued classes (`Issued`: rate class against
  `profileCurrentBasal`, as `Increase` counts it; duration kind and value; units
  class), and the execution with the temp rate as its class. When the model has a
  pump, also the delivered rate at the checkpoints. If a trace ends inside a cycle,
  only its issued classes are compared,
- `ru_*`: the conditions of R_U (section 3) as the proposition `RU`: `ValidRun`, a
  valid profile and a positive constant schedule at every time, the rate cap
  (`RateCap`, B = 3 U/h, and the schedule at most B), `InvTemp` and `InvRate` of the
  initial state, an initial temp that starts at or before t0 with a rate ≥ 0, and
  steps at or after t0. A one-entry schedule makes `profileAt` the same at every time
  (`profileAt_single`, proved), so one check covers every time,
- `inRU_*`: the Boolean check behind `ru_*`, which also checks BolusSeen (with the
  boluses of the initial history), dated readings at positive times at least 150 s
  apart with values above 38, and an SMB interval of 3 minutes,
- `pred_*`: the T2 predicate of the trace's query, for example an issued Increase with
  a non-stale glucose status (P1-w-inc), finite units at least 183 s after the newest
  earlier bolus (P5-w-spaced), two accepted microboluses (P5-pair-w), a zero temp of
  120 minutes still delivered 7199 s after the close (F-20), or the last bolus that
  `Iob.generate` finds 3600 s before t0 (prerun-w-t0).

The checks use `native_decide`, because `Iob.generate` and `basalLookup` do not reduce
in the kernel (F-22). `replay.py` first evaluates every obligation of each candidate
with Lean, writes theorems only for a candidate that meets all of them, and stops if
Lean fails or the generated file does not build.

Most shortest U1b witnesses issue outputs that oref0 does not give in these runs, for
example NaN units or a microbolus after one reading. So `check.py` has strengthened
witnesses `R-*` (work item U3b). Each needs three readings and keeps the controller to
the outputs that the T2 runs give, by the witness flag `wOdd`: no output; and after
three readings a high temp of 30 minutes with a microbolus, a low temp of 30 minutes,
a zero temp of 120 minutes, or a microbolus alone after an earlier one.

R-F-20 needs the pump, so it cannot run on `nopump`. A shortest trace on the full
contract model did not finish in 1800 s. So it runs on the variant `nobolus`: the
contract model without user boluses, without the pre-run bolus and without
controller outputs that carry units. It only removes edges, so it has fewer
behaviors than the main model, and a reachable witness transfers to the main model.

| U1b trace | result |
|---|---|
| P1-w-noread, P5-w-early, P5-w-user-cycle, cgm-w, prerun-w-t0, prerun-w-old | realized as found |
| R-P1-w-inc, R-P5-w-first, R-P5-w-spaced, R-P5-w-early, R-P5-pair-w, R-P5-w-bolus, R-P5-w-user-cycle, R-F-20 | realized |
| P1-w-inc, P5-w-first, P5-w-spaced, P5-pair-w, P5-w-bolus, F-20 | unresolved as found: with the replay inputs, T2 issues other outputs. The `R-` witness of the same name is realized |
| M-P1-rejected-high, M-P1-nan-units, M-P1-no-hasreading | not realizable: `p1_faithful` |
| M-P3-positive-120, M-P4b-30 | not realizable: `p3_temp_ok` |
| M-P5-user, M-P5-user-w | not realizable: `p5_faithful` with `smb_spacing`, under BolusSeen |
| M-P5-clock | observable part realized (a cycle with no issued fields, lost); the clock fault has no T2 counterpart |
| M-cgm-first | not replayed: a fault of the model's CGM bookkeeping |

"Unresolved" follows section 7 of the plan: other inputs could realize these traces,
so they are not shown spurious. "Not realizable" rests on a Lean theorem about every
legal run with `ValidRun` (BolusSeen as a hypothesis for P5), not on a search.

A pre-run checkpoint before the initial temp starts is not compared: T2 has no pre-run
phase, and `tempRate` applies an initial temp also before its start.

## Munta run (U4)

U4 checks the queries of `check.py` a second time with Munta, a model checker whose
algorithm is verified in Isabelle (`u0b/README.md`). Run it after
`u0b/setup_munta.sh` and `munta_order.sh`:

```bash
python3 -I uppaal/u4/run_u4.py --verifyta /opt/uppaal/lib/app/bin/verifyta.sh \
  --munta vendor/munta-build/munta.sh --order vendor/munta-order/munta.sh
```

The script writes the networks to `u4/out/`, which git ignores, and the results to
`u4/results.json`. Every checker run has the memory cap `MemoryMax=16G` and a
timeout of 1800 s. If a status is not the expected one, the script exits with 1.

### Which queries Munta can check

Munta crashes on a clock in a formula (U0b, input limit 1) and has no clock
differences. So a query that reads a clock is `unsupported`. That includes P4a,
P4b and F-20, which read the pump clock `y` or the close clock `obs`, and P1-w-inc,
which reads `age`. The other queries read only integers and locations.

### From the UPPAAL model to a Munta network

`munta.lower` writes a network with only the features that Munta accepts. Each step
is meant to keep every answer, the deadlock answer included. The docstrings argue
this under conditions that the code checks: if a condition fails, `lower` raises an
error and writes no network. The argument is not proved.

First, `check_language` refuses any input outside the language of the U4 networks:
guards and invariants with `&&`, `||`, parentheses, `true`, `false` and comparisons
of names, integers and `(name * integer)`; updates `x = k`, `x = y`, `x = x + k`, a
clock reset and `x = (expression) ? x : k`; formulas with `!( … )`,
`Template.Location` and `imply` in addition. All 58 query models are inside it.
`u4/test_lower.py` keeps the counterexamples of the Codex review rounds, each
of which `lower` must refuse or now handle. The other checked conditions
include: the updates of an edge are independent (no assignment reads or writes a
variable that an earlier one writes), the sender and the receiver of a
synchronization do not write the same variable or read what the other writes, only
the Pump edges into `Temp` write `dur`, and a value class uses only atoms `x op c`
that stand alone. The steps:

- each `select` becomes one edge for each value, and a copy `x = y` one edge for each
  value of y,
- the pump location `Temp` becomes one location `Temp_d` for each duration d, so
  that each clock bound is a constant,
- a guard that is a disjunction with a clock atom becomes one edge for each
  disjunct, and two edges that differ only in `(c < k)` and `(c >= k)` become one,
- integers with a start value other than 0 get it on a first committed edge from
  `Step.Init`. No other process may start in a committed location (checked). So a
  query `A[] p` becomes `A[] (Step.Init || p)` on the lowered
  network, and `E<> p` becomes `E<> (!(Step.Init) && p)`,
- every committed location is also urgent (finding F-23 in `../docs/FINDINGS.md`),
- every location with an edge gets a self-loop that never fires and carries the largest
  constant of each clock (finding F-24).

The first lowered `nopump` network had 826,237 states in UPPAAL, and Munta ran out
of memory on P1 after 225 s (`u4/p1_lowered_nopump.muntax`). Three reductions make
the networks small. Each is a bisimulation, so it keeps every answer:

- value classes (`munta.value_classes`): if a variable occurs only in atoms `x op c`
  and gets only constants or select values, two values that all atoms treat alike
  are equivalent. A select then takes one value per class. In `nopump`, the
  controller issues the whole durations 0, 30 and 31 instead of 0 and 30 to 120,
  because every guard and query treats 31 to 120 alike,
- observer removal (`munta.drop_names`): `run_u4.py` removes the observer variables
  and clocks that the query does not read (`BUNDLES`). The function checks that no
  other name depends on them, and that in each group of edges that differ only in
  the observer, the observer guards together cover every value. For P1 this removes
  5 of the 8 clocks, and the network has 14,379 states in UPPAAL,
- channel splitting (`munta.split_channels`): the pump receives the duration as a
  copy `dur = dv`. The channel `setTemp` becomes one channel for each duration value
  that a sender can send, so the receivers no longer copy.

The reductions are argued in the docstrings and not proved. Two checks test them on
every query: UPPAAL on the lowered network must give the status of `check.py`, and
the gates below must pass.

### Gates

A Munta answer counts only if three checks pass on the same lowered network (U0b):
the UPPAAL deadlock check, the Munta deadlock check, and UPPAAL `E<> false` without
an error. `results.json` records each gate for each query.

### U4 results

Run of 2026-11-20, UPPAAL 5.1.0-beta5, Munta at commit 62cb1a4. Of the 58 queries,
Munta gives an answer for 21, times out on 3, is not run on 6, and cannot check 28.
Every Munta answer equals the UPPAAL answer, and all three gates pass for each.

| query | network | Munta | gates | Munta time, memory, explored states |
|---|---|---|---|---|
| P1 | `nopump` | holds | pass | 4 s, 74 MB, 15,217 |
| P3, P5-issued, cgm, deadlock-contract | `nopump` | holds | pass | 4 to 5 s, up to 328 MB, 15,217 each |
| P5-pair | `nopump` | holds | pass | 7 s, 444 MB, 48,385 |
| M-P1-rejected-high, M-P1-nan-units, M-P1-no-hasreading, M-P3-positive-120, M-P5-user, M-cgm-first | `nopump` | fails | pass | 3 s each, under 83 MB |
| P1-w-noread, P5-w-first, P5-pair-w, P5-w-bolus, P5-w-user-cycle | `nopump` | reachable | pass | 3 to 7 s, up to 570 MB |
| R-P5-w-first, R-P5-pair-w, R-P5-w-bolus, R-P5-w-user-cycle | `nopump` | reachable | pass | 29 to 126 s, up to 2.8 GB |
| P4a-w-cancel, deadlock, M-missing-reject | `free` | timeout | Munta deadlock check timed out | 1800 s |
| collision, bolus, bolus-w, reject-bolus-w, close-no-steps-w, M-reject-bolus | `free` | not run | | |
| the other 28 | | unsupported | | |

The 28 unsupported queries read a clock: P4a and its other witnesses and mutations,
all P4b queries with M-no-upper-bound, F-20, P5-clock and M-P5-clock (a clock difference), P1-w-inc,
P5-w-spaced, P5-w-early, M-P5-user-w, cgm-w, the two pre-run witnesses, and the
`R-` witnesses of the same kind.

On the three `free` networks that Munta ran, the Pump template has 122 locations and
about 11,500 edges, because each duration has its own `Temp_d` location. Munta reaches its model
checker on these networks and does not finish in 1800 s. `EXPECT_MUNTA` in
`run_u4.py` records these three timeouts. After the first timeout, the script does
not run the other pump queries, to save time. Their Pump templates also have one
`Temp_d` location per duration (11,469 to 22,480 edges, more where an observer keeps
complementary edges apart), but they differ. That these runs would also time out is
an assumption, not a measurement. The script still runs the deadlock queries. For M-missing-reject, the UPPAAL deadlock gate
fails as it should: the mutation removes an edge so that the network deadlocks.

So the Munta run confirms the data-only queries of the `nopump` variant: P1, P3, P5,
P5-pair, `cgm` and the deadlock contract, their mutations and their witnesses. It gives
no result for the pump queries. Those rest on UPPAAL alone.

`run_u4.py --rescore` applies a changed `EXPECT_MUNTA` to `results.json` without a
new run.

## Extensions (U5)

`extensions.md` states the semantics of the three extensions and their relation
to the U1b contract model. `build_ext` in `model.py` builds a pump part (for P4b)
and a bolus part (for P5) of each extension, and of `u5-base`, the same parts
without an extension. `QUERIES_U5` in `check.py` holds 46 queries with their
expected status. `scripts/uppaal.sh` runs them after the 58 queries of U1a to
U3b. `check.ALL`, which U3 and U4 use, does not contain them. Each U5 query takes
less than 2 s, except P4b-120 and P4b-30 on the `lostack` pump part, which take
27 s.

| extension | P4b-120, P4b-30 | P5-issued | P5-pair |
|---|---|---|---|
| `u5-base` | hold | holds | holds |
| `delayed` (queue of 2, delay ≤ 300 s) | fail. They hold with 7500 s and 2100 s | holds | fails |
| `lostack` (retries, no deduplication) | hold | holds | fails |
| `lostack-dedup` (the pump ignores a copy) | not checked | holds | holds |
| `twoloops` | hold | fails | fails |

Each result that holds has a witness for its trigger, and each extension has a
witness that its new behavior is reachable. A trace of an extension is not a T2
run, because T2 excludes these behaviors, so U3 does not replay it.
`traces.py --u5` writes the traces to `traces/u5/`. The failures are candidate
findings in `docs/FINDINGS.md` (F-25 to F-27). They wait for an extended T2 in
Lean, and they can be spurious, because the contract allows more outputs than
oref0 gives.

## Results

With UPPAAL 5.1.0-beta5 (rev. C7C01B0740E14075), all 104 queries give their
expected status: 21 of U1a, 29 of U1b, 8 of U3b and 46 of U5. On U1a, P4a, P4b-120, `bolus` and
the deadlock query take 47 to 127 s. On U1b, P1, P3, P5-issued, P5-clock, P5-pair,
`cgm` and the deadlock query take 25 to 76 s on the `nopump` variant, and P4b-30
takes 4 s on the `relaxed` variant. The U3b witnesses take up to 52 s. Every other
query takes less than 2 s. `results.json` has
the full record.

These are results about the model and its variants. The `nopump` relation is an
argument, not a check. Replay against T2 (U3) is done. The Munta run (U4) checks 21
data-only queries a second time (section Munta run (U4)).
