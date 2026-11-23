# U0b: Munta compatibility

This directory holds work item U0b of `docs/uppaal-plan.md`. It finds out which
features of the UPPAAL model Munta can check, and whether Munta and UPPAAL give the
same answers on small networks.

Status: done. The checker is built from SML code that is identical to the code
Isabelle generates from the Munta proofs (section "Regeneration").

## Versions

| part | version | source |
|---|---|---|
| UPPAAL | 5.1.0-beta5, rev. C7C01B0740E14075, December 2023 | installed by the maintainer in `/opt/uppaal` |
| Munta | commit `62cb1a4a4dbcfcf62c365e90faba15b0012d5a12` (2021-01-07), the head of the default branch `master` | github.com/wimmers/munta |
| Isabelle | Isabelle2020, `Isabelle2020_linux.tar.gz`, SHA-256 `633aff86…1522bae` | isabelle.in.tum.de |
| AFP | `afp-2021-02-01.tar.gz`, SHA-256 `501bc33b…2087b277d` | isa-afp.org |
| SML compiler | Poly/ML 5.8.1 (2020-02-28), from Isabelle2020 | Isabelle2020 `contrib/` |

Munta moved to Isabelle2020 in April 2020 (commit `d8c3f94`). Its later commits do
not change the Isabelle version. `afp-2021-02-01` is the newest AFP release before
Isabelle2021. The full SHA-256 sums are in `setup_munta.sh`.

## How to run

```bash
uppaal/u0b/setup_munta.sh
python3 -I uppaal/u0b/run_u0b.py --verifyta /opt/uppaal/lib/app/bin/verifyta.sh --munta vendor/munta-build/munta.sh
```

`setup_munta.sh` downloads into `vendor/`, which git ignores, and checks the sums.
`run_u0b.py` writes the models to `models/` and the outcomes to `results.json`. Each
query has an expected outcome for each tool: an answer, an UPPAAL error, a Munta
rejection, or a Munta crash. If one outcome differs from its expected outcome, the
script exits with 1. With `--munta /bin/false` it exits with 1.

The Munta README builds the checker with MLton. MLton is not in the tool rule, so
`munta_poly_build.sml` builds it with Poly/ML. It compiles the same files in the
order of `ML/muntax.mlb`, without `ML/Mlton_Main.sml`, which only calls `main` under
MLton. The model arithmetic of the checker uses `IntInf` in both builds
(`datatype int = Int_of_integer of IntInf.int`). The builds differ in the native
`int`: 64 bits under MLton with `-default-type int64`, any size under Poly/ML. The
checker uses the native `int` for indices, counters and `IntInf.toInt` conversions.
No run showed a difference, but MLton was not run, so the two builds are not shown
to be equal.

## Results

`results.json` has 102 queries on 51 networks. Every outcome is the expected
outcome. On 57 queries both tools answer, with the same answer. On 15 queries both tools
answer, with different answers. The differences come from items 1, 2, 4, 5 and 6 of
"Semantic differences". Each network with a Munta answer also has a deadlock query
for both tools. If one is missing, the script fails.

The script also runs `E<> false` in UPPAAL on every network and records in
`results.json` whether it completes without an error. 21 networks pass both
deadlock checks and this check. On them, 40 answers to queries other than the
deadlock query remain. Eight of them differ, and these eight come from items 2, 4, 5
and 6 only.

The networks that test answers get self-loops on their final locations, so that
they have no deadlock (see item 1 of "Semantic differences").

| network | what it tests | queries |
|---|---|---|
| `sync_bounded` | one binary synchronization, independent bounded updates | `E<>`, `A[]` (one true, one false), `-->`, `A<>`, `E[]`, deadlock |
| `deadline` | invariant `x <= 5` with guard `x >= 5` | `E<>`, `A<>`, `A[]`, deadlock |
| `clock_reset`, `clock_reset_too_late` | a reset to 0 whose effect a second clock shows | `E<>` true and false, deadlock |
| `committed_chain` | two committed locations block another process (no delay, see item 7 of "Semantic differences") | `E<>`, `A[]`, deadlock |
| `broadcast` | a clock-guarded sender, two receivers | `E<>`, deadlock |
| `broadcast_data_guard` | receivers with data guards, one enabled and one not | `E<>`, deadlock |
| `zero_time_loop` | a self-loop under `x <= 0`, so time cannot pass | `E<>`, `A<>`, `E[]`, deadlock |

On the zero-time loop, both tools report no deadlock, and `A<> P.L1` fails in both,
because the loop can run forever without time passing.

## Semantic differences

1. Deadlock. Munta proves its answer to a formula only for a network without
   deadlock. The theorem `model_check_rename` in
   `Model_Checking/Simple_Network_Language_Export_Code.thy` has the hypothesis
   `¬ has_deadlock`. The two tools also mean different things by "deadlock". In
   both, a deadlock is a state where no action is possible after any delay. But a
   Munta step is a delay followed by an action
   (`Simple_Networks/Simple_Network_Language_Model_Checking.thy`). For Munta, a
   state that only a last delay reaches is not reachable. In network `late_deadlock`,
   the only edge of `L0` needs `x <= 1` and `L0` has no invariant. UPPAAL reports a
   deadlock after a delay past 1, and Munta reports none. On that network and on
   `deadlock_liveness`, Munta answers `A<> P.L1`, `E[] P.L0` and `P.L0 --> P.L1`
   differently from UPPAAL. If one of the two tools reports a deadlock on the
   network, a Munta answer does not count. A final location without an outgoing edge is a
   deadlock in both tools.
2. Updates. UPPAAL applies the assignments of an edge in order. Munta evaluates every
   right side in the state before the edge (`mk_updsi` in
   `Simple_Networks/Simple_Network_Language_Impl_Refine.thy`). In a binary
   synchronization, UPPAAL applies the sender's updates first, and Munta the
   receiver's. In a broadcast, both tools apply the sender's updates first (network
   `update_broadcast_order`). Network `update_sequence` has `v := v + 1, w := v` on one edge.
   Network `update_sync_order` has `v := v + 1` on the sender and `w := v` on the
   receiver. On both, `A[] w == 0` is false in UPPAAL and true in Munta, and both
   networks have no deadlock. So the generator must write only independent updates.
   A variable that one assignment writes must not occur in another assignment of
   the same edge or of the synchronized partner edge.
3. Out-of-range updates. If an update leaves the declared range, UPPAAL stops with
   an error (network `out_of_range`). Munta treats the transition as not enabled and
   answers. So a Munta `A[]` answer can hold only because such transitions were
   dropped. A query without an UPPAAL error does not show that no range error is
   reachable: `E<> P.L0` holds at the initial state and UPPAAL stops there. The
   query `E<> false` makes UPPAAL explore every reachable state, and it reports the
   error. If UPPAAL does not complete `E<> false` on the same model
   without an error, a Munta answer does not count.
4. Precedence. In UPPAAL, `imply` binds weaker than `||`. Munta parses `->` and `||`
   at the same level. So `A[] (P.L0 || P.L1 imply P.L1)` is false in UPPAAL, and the
   same text with `->` is true in Munta (network `imply_precedence`). With full
   grouping, both are false (`imply_arrow`). Munta also needs parentheses after `!`
   (`not_bang_bare`). So the generator writes every compound expression in full
   parentheses.
5. Division. UPPAAL rounds a negative quotient toward zero, and Munta rounds it
   down. After `v := (-3 / 2)`, `v` is -1 in UPPAAL and -2 in Munta
   (`negative_division`, `negative_division_floor`). Both networks pass the deadlock
   checks. So the generator writes no division.
6. Overflow. UPPAAL integers have a fixed width, and `65536 * 65536` wraps to 0.
   Munta computes with integers of any size. After `v := (65536 * 65536)` with `v`
   in `[0, 1]`, UPPAAL takes the edge and Munta disables it
   (`multiplication_overflow`). The network passes both deadlock checks, and UPPAAL
   completes `E<> false` without an error. So these checks do not find an overflow.
   The generator writes only these updates: `v := c` and `v := v + c` or
   `v := v - c`, with a constant `c` below 1000 and ranges inside -32768 to 32767.
   Each value of such an update stays far from the fixed width, and the UPPAAL
   range check then covers it.
7. Committed locations (found in U4, not by this suite). In UPPAAL, time cannot pass
   while a process is in a committed location. In Munta, "committed" only limits
   which process moves next, and time can pass. The U4 network
   `../u4/committed_delay.muntax` (UPPAAL: `../u4/committed_delay.xml`) enters a
   committed location with `x = 0`, and its only edge out needs `x >= 5`. UPPAAL
   finds `E<> P.L2` unreachable, and Munta finds it reachable. If the location is
   also urgent, Munta finds it unreachable. The network `committed_chain` tests only
   which process moves, with no delay, so this suite did not find the difference.
   So the Munta writer marks every committed location also as urgent.

## Input limits

Munta rejects these inputs, and UPPAAL accepts each of them. The network that shows
each limit is in brackets. "Rejects" means that Munta prints errors and no result.
"Crashes" means that Munta exits with code 1 and no result.

1. A clock in a query: crashes (`clock_in_formula`).
2. A clock compared with a variable, `x <= v`: rejects (`clock_vs_variable`).
3. A clock difference, `x - y <= 1`: rejects (`clock_difference`).
4. A negative constant in a clock constraint, `x > -1`: rejects
   (`negative_clock_constant`).
5. A variable in a location invariant: rejects (`variable_in_invariant`).
6. A clock reset to a value other than 0: rejects (`clock_reset_nonzero`).
7. A comparison of two variables, in a guard or in a query: rejects
   (`variable_vs_variable_guard`, `variable_vs_variable_query`). An atom compares a
   variable with an integer constant.
8. Arithmetic in a query, `v + 1 <= 2`: rejects (`arithmetic_in_query`). A query
   also rejects `true`, `false`, `!=` and a variable used as a Boolean
   (`query_true`, `query_false`, `query_not_equal`, `query_bare_flag`). A flag `f`
   becomes `f == 1`, and `v != 2` becomes `!(v == 2)`
   (`query_negated_comparison`).
9. The keywords `not` and `imply` in a query: rejects (`not_keyword`,
   `imply_keyword`). Munta accepts `!` and `->` (`not_bang`, `imply_arrow`), with
   the rules of item 4 of "Semantic differences".
10. A declared variable that no edge uses: rejects (`unused_variable`).
11. A location that no edge touches: crashes (`isolated_location`).
12. A clock guard on a broadcast receiver: rejects (`broadcast_clock_guard`). Data
    guards on receivers work (`broadcast_data_guard`). The precondition in the source
    requires the clock-constraint list `g` of a receiver to be empty.
13. A network without clocks: rejects (`no_clock`).
14. With `-deadlock`, Munta ignores the truth of the formula, but the formula must
    parse and name only known processes and locations (`deadlock_flag_bad_formula`,
    `deadlock_flag_unknown_process`, `deadlock_flag_unknown_location`).
15. Guards accept less than queries. A negated data guard `!(v == 1)` and `v != 1`
    are rejected (`guard_negation`, `guard_not_equal`). A disjunction of data atoms
    works (`guard_data_disjunction`), so `v != 1` can be written as
    `(v < 1) || (v > 1)` (`guard_negation_as_disjunction`). A disjunction of a data
    atom and a clock atom is rejected (`guard_mixed_disjunction`). The parser splits
    clock atoms from data atoms only across conjunctions. Such a guard becomes two
    edges, one for each side of the disjunction.
16. An initial location without an outgoing edge: rejects with "Initial state has
    outgoing transitions" (`initial_terminal`). UPPAAL reports a deadlock.
17. Found in U4: on some graphs, Munta computes a local clock ceiling of 0 at a
    location from which a larger constant is reachable without a reset. Its
    precondition "Ceiling resets" then fails, and Munta rejects the network
    (`../u4/ceiling_minimal.muntax`: 12 locations and one clock guard `x < 183`).
    The U4 writer adds a self-loop that never fires to every location (see
    `../munta.py`).

Two more limits follow from the input format. All integer variables start at 0, and
one file holds one formula.

Munta also accepts only one order of the variable declarations. For any other order,
the precondition "Bounds first index" fails and Munta gives no answer. The order
comes from how the generated code turns sets into lists. The probes did not give a
simple rule. `run_u0b.py` tries the declared order, then up to 5040 other orders.
It uses the order it finds for all queries on the same network.
`results.json` records the order and the number of tries. For U4, the generator
needs the rule from the source, because a search does not scale to many variables.

## Effect on the plan

Each Munta result in U4 needs three checks on the same network: the UPPAAL deadlock
check, the Munta deadlock check, and an UPPAAL run of `E<> false` without a range
error. The generator follows four rules. Updates are independent and have the forms
of item 6, with no division. Every compound expression is in full parentheses.
Guards are conjunctions whose disjunctions hold data atoms only. Under these
conditions, the suite shows no difference between the tools, but this is a test
result, not a proof. U4 found a fifth rule that the suite missed: every committed
location must also be urgent in Munta (item 7 of "Semantic differences").

The plan's model ends a run in `Step.Closed`. When the temp expires, the pump
stops. A final location without an outgoing edge is a deadlock in both tools. So
U1a must decide how the closed run continues: a self-loop changes the transition
system, and the plan's deadlock check `A[] not deadlock` then needs the treatment
of section 8 of the plan.

The guard rule matters for P1. The guard `!fresh` with
`fresh = hasReading && age < 723` gives `!hasReading || age >= 723`, a disjunction
of a data atom and a clock atom. In the Munta model it becomes two edges.

U1a and U4 need these tests of the encodings, with both deadlock checks and
`E<> false` on each encoded variant:

- P4a and collisions: just before expiry, at `y == dur` before the expiry edge,
  and after expiry. Replacement and cancel at the deadline. A microbolus that keeps
  the obligation. The mutations "wrong reset of `y`" and "the pump ignores a
  cancel" must fail.
- P4b and F-20: the observer at 1800, 7199 and 7200 seconds, the last delay after
  the close, a close with no steps, and an initial temp that does not set the F-20
  flag.
- P1, P3 and P5: strict bounds, observation before the resets of a command, lost
  and rejected commands, a user bolus in the same step, and witnesses paired with
  mutations that fail.
- Committed phases together with synchronized updates and observers. The network
  `committed_chain` tests only that a committed chain blocks another process. It
  does not test a delay in a committed location (item 7 of "Semantic differences").
- No deadlock result of the original model transfers through an added self-loop.

Section 6 of `docs/uppaal-plan.md` uses features that Munta does not accept:

- clocks in queries: P4b-120, P4b-30 and F-20 use `obs ≥ 7200` and similar,
- a clock difference in a query: P5-clock uses `Controller.sinceBolus - P5obs.c == 0`,
- an invariant bounded by a variable: the pump uses `y ≤ dur`,
- comparisons of two variables or of a variable with a duration: P4a compares the
  delivered class `eff` with the recorded class, and the observer clock `o4` with the
  duration.

A query on a clock bound can become an observer location that an edge with guard
`obs >= 7200` enters. For a variable duration, the Munta model can use one location
for each duration value. Another choice is one location for each duration class,
with a stated relation to the main model. A comparison of two variables with small
ranges can become a disjunction over their values. P5-clock has no direct encoding,
because Munta has no clock differences. These choices affect the generator of U1a,
not only U4, so U1a writes its queries in forms that have a Munta encoding where it
can. The encodings follow the transfer table of section 8 of the plan, and U0b does
not test them.

## Regeneration

The verification of Munta covers the code that Isabelle writes from the proofs.
`setup_munta.sh --regenerate` builds the session `TA_Code` with Isabelle2020 and
`afp-2021-02-01`, which writes `ML/Simple_Model_Checker.sml` again. The build took
14 minutes for the last two sessions, after the earlier sessions were built.

Result: the regenerated file is identical to the file at the pinned commit, with
SHA-256 `1a26846cba1c01e8edb61d35e43b8c8c5d3c1384105a5ec275a266ae699cf4ff`. The
checker in `vendor/munta-build` is built from this file. Isabelle reports the
session as failed, but all its 40 error lines come from ten `ML_val` test commands
at the end of `Model_Checking/Simple_Network_Language_Export_Code.thy`. These
commands read benchmark files from the author's machine (`/Users/wimmers/...`), and
they come after the code export. The log has no other error. The script accepts
only these errors.

So the SML code of the checker is the code that Isabelle generates from the Munta
proofs at the pinned versions. The proof does not cover three parts, so they stay
trusted. The first is the Isabelle code generator. The second is the driver files,
which read the input file and print the result: `Muntax.sml`, `Util.sml`,
`basics.ML`, `library.ML`, `Unsynchronized.sml` and `Writeln.sml`. The third is the
Poly/ML compiler.
