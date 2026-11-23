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
`reachable` or `unreachable`. The status `parse error` means that UPPAAL rejected
the model or the query. The status `error` means any other run without exactly one
answer. The plan's status `unsupported` is for the Munta run of U4. The status `timeout` means 1800 s passed.

## Files

| file | content |
|---|---|
| `model.py` | the model as Python data, and a writer for UPPAAL XML. U4 adds a Munta writer |
| `check.py` | the queries with their expected status, the runner and the `results.json` writer |
| `results.json` | the results of the last full run |
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
- U1b adds a `select` on a receiving edge (`Controller`), a clock difference in a
  query (P5-clock, which needs its own encoding or an "unsupported" result), and
  clock guards in observer edges,
- each translated model needs the deadlock check in both tools and an UPPAAL run of
  `E<> false` without a range error.

`results.json` records the relation of each result to the main model.

## Results

With UPPAAL 5.1.0-beta5 (rev. C7C01B0740E14075), all 50 queries give their
expected status: 21 of U1a and 29 of U1b. On U1a, P4a, P4b-120, `bolus` and the
deadlock query take 43 to 107 s. On U1b, P1, P3, P5-issued, P5-clock, P5-pair,
`cgm` and the deadlock query take 24 to 83 s on the `nopump` variant, and P4b-30
takes 5 s on the `relaxed` variant. Every other query takes less than 2 s. `results.json` has
the full record.

These are results about the model and its variants. The `nopump` relation is an
argument, not a check. Replay against T2 (U3) and the Munta run (U4) are planned.
