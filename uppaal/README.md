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
| U1b | contract, `Controller`, `CGM`, `User`, Lean SMB lemma | planned |
| U2 to U5 | traces, replay, Munta run, extensions | planned |

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
`reachable` or `unreachable`. The status `error` means that UPPAAL reported an
error or gave no single answer. The status `timeout` means 1800 s passed.

## Files

| file | content |
|---|---|
| `model.py` | the model as Python data, and a writer for UPPAAL XML. U4 adds a Munta writer |
| `check.py` | the queries with their expected status, the runner and the `results.json` writer |
| `results.json` | the results of the last full run |
| `u0b/` | work item U0b |

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
| `dk` (duration kind) | 0 absent, 1 NaN, 2 not whole, 3 whole |
| `dv` (duration value) | if `dk == 3`, whole minutes in −1..121. Otherwise 0 |
| `uk` (units) | 0 absent, 1 NaN, 2 finite and ≤ 0, 3 positive (a microbolus) |

The value −1 stands for every negative whole duration, and 121 for every whole
duration above 120, because `validDuration` treats them alike. 1..29 are the
rejected durations between 0 and 30. A non-whole duration is always rejected, so
its value does not matter.

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

## Notes for Munta (U4)

The model uses three features that Munta lacks, found in U0b: `select`, a clock
bound that depends on a variable (`y <= dur * 60`), and clocks in queries. U4 must
encode them. `select` becomes one edge for each value. The clock bound becomes one
`Temp` location for each duration. A clock in a query becomes an observer
location, set by an edge at the clock bound.

U0b found more limits that apply to this model:

- the guard `(first == 1) || (g > 0)` mixes data and clocks in a disjunction, so it
  becomes two edges,
- Munta rejects unused variables and accepts only one order of the variable
  declarations,
- Munta proves a result only for a model without deadlock. The `Closed` self-loop
  removes the deadlock at the end of a run. The deadlock result is about the model
  with the self-loop,
- Munta starts every integer variable at 0. The observer starts with `oCls = 9`
  (the obligation `eff == sched`), so U4 must encode this start, for example as a
  first committed edge. Without it, P4a checks nothing before the first obligation,
- each translated model needs the deadlock check in both tools and an UPPAAL run of
  `E<> false` without a range error.

`results.json` records the relation of each result to the main model.

## Results

With UPPAAL 5.1.0-beta5 (rev. C7C01B0740E14075), all 21 queries give their
expected status. The four exhaustive queries take the longest: P4a 68 s, P4b-120
42 s, `bolus` 42 s, the deadlock query 102 s. Every other query takes less than
1 s.
`results.json` has the full record.

These are results about the model. Replay against T2 (U3) and the Munta run (U4)
are planned.
