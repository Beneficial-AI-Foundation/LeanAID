"""U0b: Munta compatibility checks against UPPAAL.

Each case is one small network, written once in a neutral form. The script writes
one UPPAAL XML file per network and one query file per query, and one Munta JSON
file per query. It runs `verifyta` and `munta`, compares each outcome with the
expected outcome for that tool, writes `uppaal/munta/compat/results.json` and prints a table.
If one outcome differs from its expected outcome, the script exits with 1.

Outcomes:
  True, False  the tool answered
  "error"      UPPAAL reported an error for the query or the model
  "reject"     Munta printed errors and no result (parse error, failed precondition)
  "crash"      Munta exited with a non-zero code and no result

Munta proves its answer to a formula only for a network without deadlock (theorem
`model_check_rename` in Model_Checking/Simple_Network_Language_Export_Code.thy).
So the script also runs the Munta deadlock check on every network and records it.

Usage: python3 -I uppaal/munta/compat/run_compat.py --verifyta PATH --munta PATH
"""

import argparse
import hashlib
import itertools
import json
import pathlib
import subprocess
import sys
from xml.sax.saxutils import escape

HERE = pathlib.Path(__file__).resolve().parent
OUT = HERE / "models"
MAX_ORDERS = 5040  # 7 variables; a larger network needs the order rule, not a search

MUNTA_RESULTS = {
    "Property is satisfied!": True,
    "Property is not satisfied!": False,
    "Model has no deadlock!": True,   # as for `A[] not deadlock`
    "Model has a deadlock!": False,
}


def loc(name, inv="", kind=""):
    return {"name": name, "inv": inv, "kind": kind}


def edge(src, dst, guard="", label="", update=""):
    return {"src": src, "dst": dst, "guard": guard, "label": label, "update": update}


def q(formula, uppaal, munta=None, munta_formula=None):
    """A query with the expected outcome for each tool.

    munta=None means the same outcome as UPPAAL. munta_formula is the Munta spelling
    when it differs. The formula "deadlock" means `A[] not deadlock` for UPPAAL and
    the -deadlock flag for Munta."""
    return {"formula": formula, "uppaal": uppaal,
            "munta": uppaal if munta is None else munta,
            "munta_formula": munta_formula or formula}


def network(name, about, automata, clocks=("x",), vars=(), chans=(), broadcast=(),
            queries=()):
    return {"name": name, "about": about, "clocks": list(clocks), "vars": list(vars),
            "chans": list(chans), "broadcast": list(broadcast), "automata": automata,
            "queries": list(queries)}


def single(name, about, formula, uppaal, munta=None, *, clocks=("x",), vars=(), guard="",
           inv="", update="", extra_locs=(), munta_formula=None, deadlock=None):
    """A one-process network L0 -> L1 with a self-loop on L1."""
    return network(
        name, about, clocks=clocks, vars=vars,
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0", inv), loc("L1")] + list(extra_locs),
                   "edges": [edge("L0", "L1", guard, "", update), edge("L1", "L1")]}],
        queries=[q(formula, uppaal, munta, munta_formula)]
        + ([q("deadlock", deadlock)] if deadlock is not None else []))


# In UPPAAL and Munta, a state is a deadlock if no action is possible after any
# delay. A final location without an outgoing edge is one. The networks below that
# test answers get self-loops on their final locations, so that they have no
# deadlock and Munta's answers are covered by its proof.
CASES = [
    network(
        "sync_bounded",
        "one binary synchronization with independent bounded updates, all five query forms",
        vars=[("v", 0, 3), ("w", 0, 2)], chans=["a"],
        automata=[
            {"name": "P", "init": "L0",
             "locs": [loc("L0", "x <= 4"), loc("L1")],
             "edges": [edge("L0", "L1", "x >= 2", "a!", "v := v + 1"), edge("L1", "L1")]},
            {"name": "Q", "init": "M0",
             "locs": [loc("M0"), loc("M1")],
             "edges": [edge("M0", "M1", "", "a?", "w := 2")]},
        ],
        queries=[
            q("E<> P.L1 && Q.M1 && v == 1 && w == 2", True),
            q("A[] v <= 1", True),
            q("A[] v <= 0", False),
            q("E<> w == 1", False),
            q("P.L0 --> P.L1", True),
            q("A<> P.L1", True),
            q("E[] P.L0", False),
            q("deadlock", True),
        ]),
    network(
        "deadline",
        "a deadline edge: invariant x <= 5 and guard x >= 5",
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0", "x <= 5"), loc("L1")],
                   "edges": [edge("L0", "L1", "x >= 5"), edge("L1", "L1")]}],
        queries=[q("E<> P.L1", True), q("A<> P.L1", True), q("A[] P.L0 || P.L1", True),
                 q("deadlock", True)]),
    network(
        "clock_reset",
        "a reset to 0 with a visible effect: L2 needs x >= 3 after the reset at x >= 2",
        clocks=["x", "z"],
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0"), loc("L1"), loc("L2")],
                   "edges": [edge("L0", "L1", "x >= 2", "", "x := 0"),
                             edge("L1", "L2", "x >= 3 && z <= 5"), edge("L2", "L2"),
                             edge("L1", "L1")]}],
        queries=[q("E<> P.L2", True), q("deadlock", True)]),
    network(
        "clock_reset_too_late",
        "as clock_reset, but L2 needs z <= 4, which the reset makes impossible",
        clocks=["x", "z"],
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0"), loc("L1"), loc("L2")],
                   "edges": [edge("L0", "L1", "x >= 2", "", "x := 0"),
                             edge("L1", "L2", "x >= 3 && z <= 4"), edge("L2", "L2"),
                             edge("L1", "L1")]}],
        queries=[q("E<> P.L2", False), q("deadlock", True)]),
    network(
        "committed_chain",
        "a chain of two committed locations blocks the other process",
        vars=[("f", 0, 1), ("w", 0, 1)],
        automata=[
            {"name": "P", "init": "L0",
             "locs": [loc("L0"), loc("C1", kind="committed"), loc("C2", kind="committed"),
                      loc("L3")],
             "edges": [edge("L0", "C1", "x >= 1", "", "f := 1"),
                       edge("C1", "C2"),
                       edge("C2", "L3", "", "", "f := 0"),
                       edge("L3", "L3")]},
            {"name": "Q", "init": "K0",
             "locs": [loc("K0"), loc("K1")],
             "edges": [edge("K0", "K1", "f == 1", "", "w := 1")]},
        ],
        queries=[q("E<> P.C2", True), q("E<> P.L3", True), q("E<> Q.K1", False),
                 q("A[] w == 0", True), q("deadlock", True)]),
    network(
        "broadcast",
        "a broadcast channel with one clock-guarded sender and two receivers",
        vars=[("n", 0, 2)], broadcast=["b"],
        automata=[
            {"name": "S", "init": "A0",
             "locs": [loc("A0", "x <= 3"), loc("A1")],
             "edges": [edge("A0", "A1", "x >= 3", "b!"), edge("A1", "A1")]},
            {"name": "R1", "init": "B0",
             "locs": [loc("B0"), loc("B1")],
             "edges": [edge("B0", "B1", "", "b?", "n := n + 1")]},
            {"name": "R2", "init": "B0",
             "locs": [loc("B0"), loc("B1")],
             "edges": [edge("B0", "B1", "", "b?", "n := n + 1")]},
        ],
        queries=[q("E<> S.A1 && n == 2", True), q("E<> S.A1 && n == 1", False),
                 q("deadlock", True)]),
    network(
        "broadcast_data_guard",
        "broadcast receivers with data guards: R1 (n == 0) takes part, R2 (n == 1) does not",
        vars=[("n", 0, 2), ("m", 0, 1)], broadcast=["b"],
        automata=[
            {"name": "S", "init": "A0",
             "locs": [loc("A0"), loc("A1")],
             "edges": [edge("A0", "A1", "", "b!"), edge("A1", "A1")]},
            {"name": "R1", "init": "B0",
             "locs": [loc("B0"), loc("B1")],
             "edges": [edge("B0", "B1", "n == 0", "b?", "n := 1")]},
            {"name": "R2", "init": "B0",
             "locs": [loc("B0"), loc("B1")],
             "edges": [edge("B0", "B1", "n == 1", "b?", "m := 1")]},
        ],
        queries=[q("E<> R1.B1", True), q("E<> R2.B1", False), q("E<> S.A1", True),
                 q("deadlock", True)]),
    network(
        "zero_time_loop",
        "a self-loop under invariant x <= 0: time cannot pass, the loop can run forever",
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0", "x <= 0"), loc("L1")],
                   "edges": [edge("L0", "L0"), edge("L0", "L1"), edge("L1", "L1")]}],
        queries=[q("E<> P.L1", True), q("A<> P.L1", False), q("E[] P.L0", True),
                 q("deadlock", True)]),
    network(
        "update_sequence",
        "one edge with `v := v + 1, w := v`: UPPAAL applies the updates in order, "
        "Munta evaluates every right side in the state before the edge",
        vars=[("v", 0, 1), ("w", 0, 1)],
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0"), loc("L1")],
                   "edges": [edge("L0", "L1", "", "", "v := v + 1, w := v"),
                             edge("L1", "L1")]}],
        queries=[q("A[] w == 0", False, True), q("E<> P.L1 && w == 1", True, False),
                 q("deadlock", True)]),
    network(
        "update_sync_order",
        "sender `v := v + 1`, receiver `w := v`: UPPAAL applies the sender's update "
        "first, Munta the receiver's",
        vars=[("v", 0, 1), ("w", 0, 1)], chans=["a"],
        automata=[
            {"name": "P", "init": "L0",
             "locs": [loc("L0"), loc("L1")],
             "edges": [edge("L0", "L1", "", "a!", "v := v + 1"), edge("L1", "L1")]},
            {"name": "Q", "init": "M0",
             "locs": [loc("M0"), loc("M1")],
             "edges": [edge("M0", "M1", "", "a?", "w := v")]},
        ],
        queries=[q("A[] w == 0", False, True), q("deadlock", True)]),
    network(
        "deadlock_liveness",
        "an urgent location whose only edge needs time: a deadlock. Munta's answers to "
        "liveness queries then differ from UPPAAL's, and its proof does not cover them",
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0", kind="urgent"), loc("L1")],
                   "edges": [edge("L0", "L1", "x >= 1"), edge("L1", "L1")]}],
        queries=[q("E<> P.L1", False), q("deadlock", False),
                 q("A<> P.L1", False, True), q("E[] P.L0", True, False),
                 q("P.L0 --> P.L1", False, True)]),
    network(
        "late_deadlock",
        "L0 has no invariant and its edge needs x <= 1: after a delay past 1 no action "
        "is possible. UPPAAL reports a deadlock. Munta does not, because its step is a "
        "delay followed by an action, so the state after the last delay is not reached",
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0"), loc("L1")],
                   "edges": [edge("L0", "L1", "x <= 1"), edge("L1", "L1")]}],
        queries=[q("deadlock", False, True), q("A<> P.L1", False, True),
                 q("E[] P.L0", True, False), q("P.L0 --> P.L1", False, True),
                 q("E<> P.L1", True)]),
    network(
        "update_broadcast_order",
        "as update_sync_order, but over a broadcast channel: both tools apply the "
        "sender's update first",
        vars=[("v", 0, 1), ("w", 0, 1)], broadcast=["b"],
        automata=[
            {"name": "P", "init": "L0",
             "locs": [loc("L0"), loc("L1")],
             "edges": [edge("L0", "L1", "", "b!", "v := v + 1"), edge("L1", "L1")]},
            {"name": "Q", "init": "M0",
             "locs": [loc("M0"), loc("M1")],
             "edges": [edge("M0", "M1", "", "b?", "w := v")]},
        ],
        queries=[q("A[] w == 0", False), q("deadlock", True)]),
    network(
        "out_of_range",
        "an update that leaves the declared range of v",
        vars=[("v", 0, 1)],
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0"), loc("L1"), loc("L2")],
                   "edges": [edge("L0", "L1", "", "", "v := v + 1"),
                             edge("L1", "L2", "", "", "v := v + 1"),
                             edge("L1", "L1"), edge("L2", "L2")]}],
        # `E<> P.L0` holds at the initial state and stops there without an error.
        # `E<> false` explores every state and so finds the range error.
        queries=[q("E<> P.L2", "error", False), q("deadlock", "error", True),
                 q("E<> P.L0", True), q("E<> false", "error", False,
                                         munta_formula="E<> (P.L0 && !(P.L0))")]),
    # Inputs that UPPAAL accepts and Munta rejects.
    single("clock_in_formula", "a clock in the query", "E<> x >= 3", True, "crash"),
    single("clock_vs_variable", "a clock compared with a variable in a guard",
           "E<> P.L1", True, "reject", vars=[("v", 0, 3)], guard="x <= v",
           update="v := 0"),
    single("clock_difference", "a clock difference in a guard", "E<> P.L1", True,
           "reject", clocks=("x", "y"), guard="x - y <= 1"),
    single("variable_in_invariant", "a variable in a location invariant", "E<> P.L1",
           True, "reject", vars=[("v", 0, 3)], inv="v <= 2", update="v := 0"),
    single("clock_reset_nonzero", "a clock reset to 1", "E<> P.L1", True, "reject",
           update="x := 1"),
    single("negative_clock_constant", "a clock compared with -1", "E<> P.L1", True,
           "reject", guard="x > -1"),
    single("variable_vs_variable_guard", "a guard comparing two variables", "E<> P.L1",
           True, "reject", vars=[("v", 0, 1), ("w", 0, 1)], guard="v == w",
           update="v := 1, w := 1"),
    single("variable_vs_variable_query", "a query comparing two variables",
           "A[] v == w", True, "reject", vars=[("v", 0, 1), ("w", 0, 1)],
           update="v := 1, w := 1"),
    single("arithmetic_in_query", "a query with arithmetic", "A[] v + 1 <= 2", True,
           "reject", vars=[("v", 0, 1)], update="v := 1"),
    single("not_keyword", "`not` in a query (Munta accepts `!`)", "A[] not P.L1", False,
           "reject"),
    single("not_bang", "`!` with parentheses in a query", "E<> !(P.L1)", True,
           deadlock=True),
    single("not_bang_bare", "`!` without parentheses: Munta needs them",
           "A[] !P.L1", False, "reject"),
    single("imply_keyword", "`imply` in a query (Munta spells it `->`)",
           "A[] (P.L1 imply P.L1)", True, "reject"),
    single("imply_arrow", "`->` in the Munta query, `imply` in the UPPAAL query",
           "A[] ((P.L0 || P.L1) imply P.L1)", False,
           munta_formula="A[] ((P.L0 || P.L1) -> P.L1)", deadlock=True),
    single("imply_precedence",
           "without grouping, `imply` binds weaker than `||` in UPPAAL, but Munta parses "
           "`->` and `||` at the same level",
           "A[] (P.L0 || P.L1 imply P.L1)", False, True,
           munta_formula="A[] (P.L0 || P.L1 -> P.L1)", deadlock=True),
    single("imply_true", "a true implication with grouping", "A[] ((P.L1) imply (P.L1))",
           True, munta_formula="A[] ((P.L1) -> (P.L1))", deadlock=True),
    single("unused_variable", "a declared variable that no edge uses", "E<> P.L1", True,
           "reject", vars=[("v", 0, 1)]),
    single("isolated_location", "a location that no edge touches", "E<> P.L1", True,
           "crash", extra_locs=[loc("L9")]),
    network(
        "broadcast_clock_guard",
        "a broadcast receiver with a clock guard",
        broadcast=["b"],
        automata=[
            {"name": "S", "init": "A0",
             "locs": [loc("A0"), loc("A1")],
             "edges": [edge("A0", "A1", "", "b!"), edge("A1", "A1")]},
            {"name": "R1", "init": "B0",
             "locs": [loc("B0"), loc("B1")],
             "edges": [edge("B0", "B1", "x <= 5", "b?")]},
        ],
        queries=[q("E<> R1.B1", True, "reject")]),
    network(
        "no_clock",
        "a network without clocks",
        clocks=[], vars=[("v", 0, 1)],
        automata=[{"name": "P", "init": "L0",
                   "locs": [loc("L0"), loc("L1")],
                   "edges": [edge("L0", "L1", "", "", "v := 1"), edge("L1", "L1")]}],
        queries=[q("E<> P.L1", True, "reject")]),
    single("negative_division", "`v := (-3 / 2)`: UPPAAL rounds toward zero, Munta down",
           "E<> v == -1", True, False, vars=[("v", -2, 2)], update="v := (-3 / 2)",
           deadlock=True),
    single("negative_division_floor", "as negative_division, the other value",
           "E<> v == -2", False, True, vars=[("v", -2, 2)], update="v := (-3 / 2)",
           deadlock=True),
    network(
        "multiplication_overflow",
        "`v := (65536 * 65536)`: UPPAAL wraps the product to 0, which is in range; Munta "
        "computes the exact product and disables the edge",
        vars=[("v", 0, 1)],
        automata=[{"name": "P", "init": "L0", "locs": [loc("L0"), loc("L1")],
                   "edges": [edge("L0", "L1", "", "", "v := (65536 * 65536)"),
                             edge("L0", "L0"), edge("L1", "L1")]}],
        queries=[q("E<> P.L1", True, False), q("A[] !(P.L1)", False, True),
                 q("deadlock", True), q("E<> false", False,
                                         munta_formula="E<> (P.L0 && !(P.L0))")]),
    single("deadlock_flag_unknown_location",
           "the -deadlock flag with a formula that names an unknown location", "deadlock",
           True, "reject", munta_formula="E<> P.NoSuchLocation"),
    single("query_true", "`true` in a query", "A[] true", True, "reject"),
    single("query_false", "`false` in a query", "E<> false", False, "reject"),
    single("query_not_equal", "`!=` in a query", "A[] v != 2", True, "reject",
           vars=[("v", 0, 1)], update="v := 1"),
    single("query_bare_flag", "a variable used as a Boolean in a query", "A[] v", False,
           "reject", vars=[("v", 0, 1)], update="v := 1"),
    single("query_negated_comparison", "`!(v == 2)` in a query", "A[] !(v == 2)", True,
           vars=[("v", 0, 1)], update="v := 1", deadlock=True),
    single("guard_negation", "a negated data guard", "E<> P.L1", True, "reject",
           vars=[("v", 0, 1)], guard="!(v == 1)", update="v := 1"),
    single("guard_not_equal", "`!=` in a guard", "E<> P.L1", True, "reject",
           vars=[("v", 0, 1)], guard="v != 1", update="v := 1"),
    single("guard_mixed_disjunction", "a disjunction of a data atom and a clock atom",
           "E<> P.L1", True, "reject", vars=[("v", 0, 1)], guard="(v == 0) || (x > 2)",
           update="v := 1"),
    single("guard_data_disjunction", "a disjunction of data atoms only", "E<> P.L1", True,
           vars=[("v", 0, 1)], guard="(v == 0) || (v == 1)", update="v := 1",
           deadlock=True),
    single("guard_negation_as_disjunction", "`v != 1` written as `(v < 1) || (v > 1)`",
           "E<> P.L1", True, vars=[("v", 0, 1)], guard="(v < 1) || (v > 1)",
           update="v := 1", deadlock=True),
    single("deadlock_flag_unknown_process",
           "the -deadlock flag with a formula that names an unknown process", "deadlock",
           True, "reject", munta_formula="E<> Unknown.L0"),
    network(
        "initial_terminal",
        "the initial location has an incoming edge but no outgoing edge",
        vars=[("v", 0, 1)],
        automata=[{"name": "P", "init": "L0", "locs": [loc("L0"), loc("L1")],
                   "edges": [edge("L1", "L0", "", "", "v := 1")]}],
        queries=[q("deadlock", False, "reject")]),
    single("deadlock_flag_bad_formula",
           "the -deadlock flag with a formula that does not parse", "deadlock", True,
           "reject", munta_formula="nonsense"),
]


# ---------------------------------------------------------------- writers


def uppaal_formula(f):
    return "A[] not deadlock" if f == "deadlock" else f


def write_uppaal(case, path):
    decl = []
    if case["clocks"]:
        decl.append("clock " + ", ".join(case["clocks"]) + ";")
    for (v, lo, hi) in case["vars"]:
        decl.append(f"int[{lo},{hi}] {v};")
    if case["chans"]:
        decl.append("chan " + ", ".join(case["chans"]) + ";")
    if case["broadcast"]:
        decl.append("broadcast chan " + ", ".join(case["broadcast"]) + ";")
    out = ['<?xml version="1.0" encoding="utf-8"?>',
           "<!DOCTYPE nta PUBLIC '-//Uppaal Team//DTD Flat System 1.6//EN' "
           "'http://www.it.uu.se/research/group/darts/uppaal/flat-1_6.dtd'>",
           "<nta>", f"<declaration>{escape(chr(10).join(decl))}</declaration>"]
    for a in case["automata"]:
        ids = {l["name"]: f"{a['name']}_{i}" for i, l in enumerate(a["locs"])}
        out.append(f"<template><name>{a['name']}T</name>")
        for l in a["locs"]:
            out.append(f'<location id="{ids[l["name"]]}"><name>{l["name"]}</name>')
            if l["inv"]:
                out.append(f'<label kind="invariant">{escape(l["inv"])}</label>')
            if l["kind"]:
                out.append(f"<{l['kind']}/>")
            out.append("</location>")
        out.append(f'<init ref="{ids[a["init"]]}"/>')
        for e in a["edges"]:
            out.append(f'<transition><source ref="{ids[e["src"]]}"/>'
                       f'<target ref="{ids[e["dst"]]}"/>')
            if e["guard"]:
                out.append(f'<label kind="guard">{escape(e["guard"])}</label>')
            if e["label"]:
                out.append(f'<label kind="synchronisation">{escape(e["label"])}</label>')
            if e["update"]:
                out.append('<label kind="assignment">'
                           f'{escape(e["update"].replace(":=", "="))}</label>')
            out.append("</transition>")
        out.append("</template>")
    insts = "\n".join(f"{a['name']} = {a['name']}T();" for a in case["automata"])
    names = ", ".join(a["name"] for a in case["automata"])
    out.append(f"<system>{escape(insts)}\nsystem {names};</system>")
    out.append("</nta>")
    path.write_text("\n".join(out) + "\n")


def munta_json(case, formula, var_order):
    autos = []
    for a in case["automata"]:
        ids = {l["name"]: i for i, l in enumerate(a["locs"])}
        autos.append({
            "name": a["name"],
            "initial": ids[a["init"]],
            "committed": [ids[l["name"]] for l in a["locs"] if l["kind"] == "committed"],
            "urgent": [ids[l["name"]] for l in a["locs"] if l["kind"] == "urgent"],
            "nodes": [{"id": ids[l["name"]], "name": l["name"], "invariant": l["inv"]}
                      for l in a["locs"]],
            "edges": [{"source": ids[e["src"]], "target": ids[e["dst"]],
                       "guard": e["guard"], "label": e["label"], "update": e["update"]}
                      for e in a["edges"]],
        })
    return {
        "automata": autos,
        "clocks": ", ".join(case["clocks"]),
        "vars": ", ".join(f"{v}[{lo}:{hi}]" for (v, lo, hi) in var_order),
        "broadcast": case["broadcast"],
        "formula": formula,
    }


# ---------------------------------------------------------------- runners


def run(cmd, timeout=120):
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout, p.stderr


def uppaal_outcome(verifyta, xml, qfile):
    code, out, err = run([verifyta, "-q", str(xml), str(qfile)])
    sat = out.count("Formula is satisfied.")
    unsat = out.count("Formula is NOT satisfied.")
    if code == 0 and sat + unsat == 1 and "[error]" not in out + err:
        return (sat == 1), out + err
    return "error", out + err


def munta_outcome(munta, path, deadlock):
    code, out, err = run([munta, "-m", str(path)] + (["-deadlock"] if deadlock else []))
    lines = [l.strip() for l in out.splitlines() if l.strip()]
    last = lines[-1] if lines else ""
    if code != 0:
        return "crash", last, out + err
    results = [l for l in lines if l in MUNTA_RESULTS]
    # Exactly one result line, as the last line, of the requested kind, and no
    # failure report.
    if (len(results) == 1 and results[0] == last and "Failure:" not in lines
            and deadlock == ("deadlock" in last)):
        return MUNTA_RESULTS[last], last, out + err
    return "reject", last, out + err


def var_orders(vars_):
    """The declared order first, then the other orders, lazily."""
    yield list(vars_)
    for i, o in enumerate(itertools.permutations(vars_)):
        if i >= MAX_ORDERS:
            return
        if list(o) != list(vars_):
            yield list(o)


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verifyta", required=True)
    ap.add_argument("--munta", required=True)
    args = ap.parse_args()
    OUT.mkdir(exist_ok=True)
    for old in OUT.iterdir():
        old.unlink()
    results = []
    exhaustive = {}
    for case in CASES:
        xml = OUT / f"{case['name']}.xml"
        write_uppaal(case, xml)
        # `E<> false` makes UPPAAL explore every reachable state. False without an
        # error means that no reachable update leaves its range.
        efile = OUT / f"{case['name']}.exhaustive.q"
        efile.write_text("E<> false\n")
        exhaustive[case["name"]] = uppaal_outcome(args.verifyta, xml, efile)[0] is False
        # Munta accepts one order of the variable declarations only; otherwise the
        # precondition "Bounds first index" fails and Munta gives no answer. The
        # order found for the first query of a network is used for the others.
        order = None
        for i, query in enumerate(case["queries"]):
            f = query["formula"]
            deadlock = f == "deadlock"
            qfile = OUT / f"{case['name']}.{i}.q"
            qfile.write_text(uppaal_formula(f) + "\n")
            u, uout = uppaal_outcome(args.verifyta, xml, qfile)
            mformula = query["munta_formula"]
            if deadlock and mformula == "deadlock":
                # The -deadlock flag ignores the formula, but it must parse.
                a = case["automata"][0]
                mformula = f"E<> {a['name']}.{a['init']}"
            mpath = OUT / f"{case['name']}.{i}.muntax"
            tried = 0
            for cand in ([order] if order else var_orders(case["vars"])):
                tried += 1
                mpath.write_text(json.dumps(munta_json(case, mformula, cand), indent=1)
                                 + "\n")
                m, mlast, mout = munta_outcome(args.munta, mpath, deadlock)
                if "Bounds first index" not in mout:
                    # Keep the order for later queries only if Munta answered, so
                    # that it passed all preconditions.
                    if m in (True, False):
                        order = cand
                    break
            else:
                m, mlast = "reject", "no accepted variable order found"
            results.append({
                "network": case["name"], "about": case["about"], "query": f,
                "munta_query": ("(-deadlock flag) " if deadlock else "") + mformula,
                "expected_uppaal": query["uppaal"], "uppaal": u,
                "expected_munta": query["munta"], "munta": m,
                "munta_last_line": mlast[:300],
                "uppaal_message": "" if u in (True, False) else
                    uout.strip().replace(str(OUT), "models")[-300:],
                "munta_var_order": [v for (v, _, _) in order] if order else None,
                "munta_orders_tried": tried,
                "xml_sha256": sha256(xml), "muntax_sha256": sha256(mpath),
            })
    # The deadlock checks of both tools on each network. Munta's answers to formulas
    # are proved only for a network without deadlock in Munta's sense, and that sense
    # differs from UPPAAL's (network late_deadlock).
    mgate = {r["network"]: r["munta"] for r in results if r["query"] == "deadlock"}
    ugate = {r["network"]: r["uppaal"] for r in results if r["query"] == "deadlock"}
    missing = sorted({r["network"] for r in results
                      if r["munta"] in (True, False) and r["network"] not in mgate})
    for r in results:
        r["munta_network_deadlock_free"] = mgate.get(r["network"])
        r["uppaal_network_deadlock_free"] = ugate.get(r["network"])
        r["uppaal_exhaustive_no_error"] = exhaustive[r["network"]]
    (HERE / "results.json").write_text(json.dumps(results, indent=1) + "\n")
    bad = []
    for r in results:
        ok = r["uppaal"] == r["expected_uppaal"] and r["munta"] == r["expected_munta"]
        if not ok:
            bad.append(r)
        print(f"{'ok ' if ok else 'BAD'} {r['network']:27} {r['query'][:38]:38} "
              f"uppaal={str(r['uppaal']):6} munta={str(r['munta']):6} | "
              f"{r['munta_last_line'][:50]}")
    agree = sum(1 for r in results if r["uppaal"] in (True, False)
                and r["uppaal"] == r["munta"])
    differ = sum(1 for r in results if r["uppaal"] in (True, False)
                 and r["munta"] in (True, False) and r["uppaal"] != r["munta"])
    print(f"{len(results)} queries on {len(CASES)} networks; both tools answer the same: "
          f"{agree}; both answer differently: {differ}; outcomes not as expected: {len(bad)}")
    if missing:
        print(f"networks with Munta answers but no deadlock check: {missing}")
    return 1 if bad or missing else 0


if __name__ == "__main__":
    sys.exit(main())
