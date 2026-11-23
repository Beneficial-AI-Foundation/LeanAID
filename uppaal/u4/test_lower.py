"""Regression tests for munta.lower: the counterexamples of the Codex review rounds
1 to 15 of U4. Each input must be refused with ValueError, or lowered so that the
point of the review is fixed. Runs no model checker.

Usage: python3 -I uppaal/u4/test_lower.py
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

import model as M          # noqa: E402
import munta as MU         # noqa: E402
import run_u4 as R         # noqa: E402

L, E, T = M.Loc, M.Edge, M.Template


def net(decl, *templates):
    return M.Model(decl=list(decl), templates=list(templates))


def pump(dur, kind, guard):
    return net(["clock z;", "int[0,2] dur;", "int[0,1] hit;"],
               T("Step", "Pre", [L("Pre")], [E("Pre", "Pre", guard="z >= 0")]),
               T("Pump", "Sched", [L("Sched"), L("Temp", inv="y <= (dur * 60)", kind=kind), L("Done")],
                 [E("Sched", "Temp", update=f"y = 0, dur = {dur}"),
                  E("Temp", "Done", guard=guard, update="hit = 1"),
                  E("Temp", "Sched", guard="y >= (dur * 60)"), E("Done", "Done", guard="z >= 0")],
                 decl="clock y;"))


REFUSED = {
    "r1 clock on the right of a dropped atom": (
        net(["clock x, z;", "int[0,1] flag;"],
            T("Step", "Pre", [L("Pre")], [E("Pre", "Pre", guard="((2 >= x) && (z >= 0))")])),
        "A[] (!deadlock)", ["x"]),
    "r1 second process starts committed": (
        net(["clock z;", "int[0,1] v = 1;", "int[0,1] hit;"],
            T("Step", "Pre", [L("Pre")], [E("Pre", "Pre", guard="z >= 0")]),
            T("P", "C", [L("C", kind="committed"), L("Done")],
              [E("C", "Done", guard="v == 0", update="hit = 1"), E("C", "Done", guard="v == 1"),
               E("Done", "Done")])),
        "E<> (hit == 1)", []),
    "r2 sender and receiver write the same variable": (
        net(["clock z;", "int[0,1] v;", "int[0,1] hit;", "chan c;"],
            T("Step", "Pre", [L("Pre"), L("Done")],
              [E("Pre", "Done", sync="c!", update="hit = 1"), E("Done", "Done", guard="z >= 0")]),
            T("P", "Pre", [L("Pre"), L("Done")],
              [E("Pre", "Done", sync="c?", update="hit = v"), E("Done", "Done", guard="z >= 0")])),
        "E<> (hit == 1)", []),
    "r2 dependent copy": (
        net(["clock z;", "int[0,1] v;", "int[0,1] hit;"],
            T("Step", "Pre", [L("Pre"), L("Done")],
              [E("Pre", "Done", update="v = 1, hit = v"), E("Done", "Done", guard="z >= 0")])),
        "E<> (hit == 1)", []),
    "r2 dependent conditional": (
        net(["clock z;", "int[0,1] v;", "int[0,1] hit;"],
            T("Step", "Pre", [L("Pre"), L("Done")],
              [E("Pre", "Done", update="v = 1, hit = (v == 1) ? hit : 1"),
               E("Done", "Done", guard="z >= 0")])),
        "E<> (hit == 1)", []),
    "r2 dur written outside the pump": (
        net(["clock z;", "int[0,2] dur;", "int[0,1] hit;"],
            T("Step", "Pre", [L("Pre")], [E("Pre", "Pre", guard="z >= 0", update="dur = 2")]),
            T("Pump", "Sched", [L("Sched"), L("Temp", inv="y <= (dur * 60)")],
              [E("Sched", "Temp", update="y = 0, dur = 1"),
               E("Temp", "Sched", guard="y >= 90", update="hit = 1"),
               E("Temp", "Sched", guard="y >= (dur * 60)")], decl="clock y;")),
        "E<> (hit == 1)", []),
    "r2 arithmetic in a guard": (
        net(["clock z;", "int[0,3] v;", "int[0,1] hit;"],
            T("Step", "A", [L("A"), L("B"), L("D")],
              [E("A", "B", select="k : int[0,3]", update="v = k"),
               E("B", "D", guard="v == 1 + 1", update="hit = 1"),
               E("B", "B", guard="z >= 0"), E("D", "D", guard="z >= 0")])),
        "E<> (hit == 1)", []),
    "r3 receiver conditional reads the sender write": (
        net(["clock z;", "int[0,1] v;", "int[0,1] hit;", "chan c;"],
            T("Step", "Pre", [L("Pre"), L("Done")],
              [E("Pre", "Done", sync="c!", update="v = 1"), E("Done", "Done", guard="z >= 0")]),
            T("P", "Pre", [L("Pre"), L("Done")],
              [E("Pre", "Done", sync="c?", update="hit = (v == 1) ? hit : 1"),
               E("Done", "Done", guard="z >= 0")])),
        "E<> (hit == 1)", []),
    "r3 negation of a variable in a guard": (
        net(["clock z;", "int[0,2] v = 2;", "int[0,1] hit;"],
            T("Step", "Pre", [L("Pre"), L("Done")],
              [E("Pre", "Done", guard="((!(v) == 1) || (v == 1))", update="hit = 1"),
               E("Pre", "Pre", guard="z >= 0"), E("Done", "Done", guard="z >= 0")])),
        "E<> (hit == 1)", ["v"]),
    "r3 negation of a variable in a conditional": (
        net(["clock z;", "int[0,2] v = 2;", "int[0,1] hit;"],
            T("Step", "Pre", [L("Pre"), L("Done")],
              [E("Pre", "Done", update="hit = ((!(v) == 1)) ? hit : 1"),
               E("Pre", "Pre", guard="z >= 0"), E("Done", "Done", guard="z >= 0")])),
        "E<> (hit == 1)", []),
    "r3 temp of duration 0": (pump(0, "", "y >= 0"), "E<> (hit == 1)", []),
    "r4 bare negation in a select guard": (
        net(["int[0,2] v;", "int[0,1] flag;", "clock c;"],
            T("Step", "Start", [L("Start", kind="committed"), L("Done")],
              [E("Start", "Done", select="n : int[0,2]", guard="!(!n == 1)", update="v = n"),
               E("Done", "Done", guard="c >= 0")])),
        "E<> (Step.Done && !(v == 1))", []),
    "r4 select shadows a global": (
        net(["int[0,1] v;", "int[0,1] x;", "clock z;", "chan c;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0", sync="c!")]),
            T("R", "S", [L("S")], [E("S", "S", select="v : int[0,1]", sync="c?", update="x = v")])),
        "E<> (x == 1)", []),
    "r4 Step has a location Init": (
        net(["int[0,1] v;", "clock z;"],
            T("Step", "Init", [L("Init"), L("Done")],
              [E("Init", "Done", guard="z >= 0", update="v = 1"), E("Done", "Done")])),
        "A[] (v == 1)", []),
    "r5 split channel name not fresh": (
        net(["int[0,1] v;", "int[0,1] x;", "clock z;", "chan c, c_0;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0", sync="c!")]),
            T("R", "S", [L("S")], [E("S", "S", sync="c?", update="x = v")]),
            T("Q", "S", [L("S"), L("Done")],
              [E("S", "Done", sync="c_0?", update="x = v"), E("Done", "Done")])),
        "E<> Q.Done", []),
    "r5 local integer": (
        net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S"), L("Done")],
              [E("S", "Done", guard="z >= 0", update="v = 1"), E("Done", "Done")],
              decl="int[0,1] v;")),
        "E<> (v == 1)", []),
    "r6 imply with a disjunction as operand": (
        net(["int[0,1] f;", "clock z;"],
            T("Step", "S", [L("S"), L("T")], [E("S", "T", guard="z >= 0"), E("T", "T")])),
        "A[] (Step.S || Step.T imply Step.T)", []),
    "r6 range allows overflow": (
        net(["int[-2147483648,2147483647] v = 2147483647;", "int[0,1] f;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="z >= 0", update="v = v + 1"), E("S", "S"), E("D", "D")])),
        "E<> Step.D", []),
    "r6 && and || mixed without parentheses": (
        net(["int[0,1] v;", "int[0,1] x;", "clock z;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="v == 0 || v == 1 && z >= 0")])),
        "E<> (x == 1)", []),
    "r6 initial invariant reads a start value": (
        net(["int[0,1] v = 1;", "clock z;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")]),
            T("Q", "S", [L("S", inv="v == 1")], [E("S", "S")])),
        "E<> (v == 1)", []),
    "r6 formula names Pump.Temp": (
        net(["clock z;", "int[0,1] dur;", "int[0,1] flag;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")]),
            T("Pump", "S", [L("S"), L("Temp", inv="y <= (dur * 60)")],
              [E("S", "Temp", update="y = 0, dur = 1"), E("Temp", "S", guard="y >= (dur * 60)")],
              decl="clock y;")),
        "E<> Pump.Temp", []),
    "r7 receiver writes the copied variable": (
        net(["int[0,1] v;", "int[0,1] x;", "clock z;", "chan c;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0", sync="c!")]),
            T("R", "S", [L("S")], [E("S", "S", sync="c?", update="x = v, v = 1")])),
        "E<> (x == 1)", []),
    "r7 clock disjunction nested by a copy": (
        net(["int[0,1] v;", "int[0,1] x;", "clock z;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="v == 0 || z >= 1", update="x = v")])),
        "E<> (x == 1)", []),
    "r7 range without 0": (
        net(["int[1,2] v = 1;", "int[0,1] f;", "clock z;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")])),
        "E<> (v == 1)", []),
    "r7 pump already has Temp_1": (
        net(["int[0,1] dur;", "int[0,1] hit;", "clock z;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")]),
            T("Pump", "S", [L("S"), L("Temp", inv="y <= (dur * 60)"), L("Temp_1"), L("Done")],
              [E("S", "Temp", update="y = 0, dur = 1"), E("Temp", "S", guard="y >= (dur * 60)"),
               E("Temp_1", "Done", update="hit = 1"), E("Done", "Done")], decl="clock y;")),
        "E<> (hit == 1)", []),
    "r7 arithmetic in a formula": (
        net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0", update="v = 1")])),
        "E<> ((v * 2) == 2)", []),
    "r8 product that overflows": (
        net(["int[0,4] dur;", "int[0,1] hit;", "clock z;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")]),
            T("Pump", "S", [L("S"), L("Temp", kind="urgent"), L("D")],
              [E("S", "Temp", update="dur = 4, y = 0"),
               E("Temp", "D", guard="y >= (dur * 1073741824)", update="hit = 1"), E("D", "D")],
              decl="clock y;")),
        "E<> (hit == 1)", []),
    "r8 dropped update leaves the range": (
        net(["int[0,1] v;", "int[0,1] f;", "clock z;"],
            T("Step", "S", [L("S"), L("D")], [E("S", "D", update="v = 2"), E("D", "D", guard="z >= 0")])),
        "E<> Step.D", ["v"]),
    "r8 true in a formula": (
        net(["int[0,1] v;", "int[0,1] w;", "clock z;"], T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")])),
        "E<> true", []),
    "r8 two names compared in a formula": (
        net(["int[0,1] v;", "int[0,1] w;", "clock z;"], T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")])),
        "E<> (v == w)", []),
    "r8 data invariant": (
        net(["int[0,1] v;", "int[0,1] w;", "clock z;"],
            T("Step", "S", [L("S", inv="v == 0")], [E("S", "S", guard="z >= 0")])),
        "E<> (v == 0)", []),
    "r8 no 0/1 integer for the ceiling loops": (
        net(["int[0,0] v;", "clock z;"], T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")])),
        "E<> (v == 0)", []),
    "r9 select shadows another template's local clock": (
        net(["int[0,1] flag;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", select="n : int[-1,-1]", guard="n >= 0"), E("D", "D", guard="z >= 0")]),
            T("Observer", "O", [L("O")], [E("O", "O", guard="((n >= 0) && (flag == 1))")],
              decl="clock n;")),
        "E<> Step.D", ["n"]),
    "r9 guard compares two variables": (net(["int[0,1] v;", "int[0,1] w;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="v == w", update="v = 1"), E("D", "D", guard="z >= 0")])), "E<> Step.D", []),
    "r9 guard compares a clock with a variable": (net(["int[0,1] v;", "int[0,1] w;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="z <= v", update="v = 1"), E("D", "D", guard="z >= 0")])), "E<> Step.D", []),
    "r9 guard compares a clock with a negative constant": (net(["int[0,1] v;", "int[0,1] w;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="z > -1", update="v = 1"), E("D", "D", guard="z >= 0")])), "E<> Step.D", []),
    "r9 no Step template": (
        net(["int[0,1] v = 1;", "clock z;"], T("P", "S", [L("S")], [E("S", "S", guard="z >= 0")])),
        "E<> (v == 1)", []),
    "r9 Pump without Temp": (
        net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")]),
            T("Pump", "S", [L("S")], [E("S", "S", guard="z >= 0")])),
        "E<> (v == 0)", []),
    "r10 integer named True": (
        net(["int[0,1] True;", "int[0,1] flag;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", select="n : int[1,1]", guard="True == 0", update="flag = n"),
               E("S", "S", guard="z >= 0"), E("D", "D", guard="z >= 0")])),
        "E<> Step.D", []),
    "r10 product in a guard after lowering": (net(["int[0,1] v;", "int[0,1] w;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="(v * 2) == 0", update="v = 1"), E("D", "D", guard="z >= 0")])), "E<> Step.D", []),
    "r10 clock compared with a product of a variable": (net(["int[0,1] v;", "int[0,1] w;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="z <= (v * 2)", update="v = 1"), E("D", "D", guard="z >= 0")])), "E<> Step.D", []),
    "r10 invariant with a negative clock constant": (
        net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S"), L("D", inv="z > -1")], [E("S", "D", update="v = 1"), E("D", "D", guard="z >= 0")])),
        "E<> Step.D", []),
    "r10 Pump without dur": (
        net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")]),
            T("Pump", "S", [L("S"), L("Temp")], [E("S", "S", guard="z >= 0"), E("Temp", "Temp", guard="z >= 0")])),
        "E<> (v == 0)", []),
    "r11 local integer after a comment": (
        net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="z >= 0", update="v = 1"), E("S", "S", guard="y >= 0"),
               E("D", "D", guard="y >= 0")], decl="clock y; // local state follows\nint[0,1] v;")),
        "E<> (v == 1)", []),
    "r11 reversed atom": (net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="0 == v", update="v = 1"), E("S", "S", guard="z >= 0"),
               E("D", "D", guard="z >= 0")])), "E<> Step.D", []),
    "r11 invariant with a reversed atom": (
        net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S"), L("D", inv="1 >= z")],
              [E("S", "D", update="v = 1"), E("S", "S", guard="z >= 0"), E("D", "D", guard="z >= 0")])),
        "E<> Step.D", []),
    "r11 leading zero": (net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", select="n : int[0,0]", guard="v == 01", update="v = 1"), E("S", "S", guard="z >= 0"),
               E("D", "D", guard="z >= 0")])), "E<> Step.D", []),
    "r12 split channel name equals an integer": (
        net(["int[0,1] v;", "int[0,1] x;", "int[0,1] c_0;", "clock z;", "chan c;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0", sync="c!", update="c_0 = 1")]),
            T("R", "S", [L("S")], [E("S", "S", sync="c?", update="x = v")])),
        "E<> (c_0 == 1)", []),
    "r12 reversed atom in a formula": (net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="z >= 0", update="v = 1"), E("S", "S", guard="z >= 0"),
               E("D", "D", guard="z >= 0")])), "E<> (0 == v)", []),
    "r12 constant atom in a formula": (net(["int[0,1] v;", "clock z;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="z >= 0", update="v = 1"), E("S", "S", guard="z >= 0"),
               E("D", "D", guard="z >= 0")])), "E<> (0 == 0)", []),
    "r13 split channel name equals a process name": (
        net(["int[0,1] v;", "int[0,1] x;", "clock z;", "chan c;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0", sync="c!")]),
            T("c_0", "S", [L("S")], [E("S", "S", sync="c?", update="x = v")])),
        "E<> (x == 0)", []),
    "r13 local clock named like a channel": (
        net(["int[0,1] v;", "clock z;", "chan c;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0", sync="c!")]),
            T("Q", "S", [L("S")], [E("S", "S", guard="c >= 0", update="v = 1")], decl="clock c;"),
            T("R", "S", [L("S")], [E("S", "S", sync="c?")])),
        "E<> (v == 1)", []),
    "r13 dropping the last clock": (
        net(["clock z;", "int[0,1] v;"],
            T("Step", "S", [L("S"), L("D")],
              [E("S", "D", guard="z >= 0", update="v = 1"), E("S", "S", guard="z >= 0"),
               E("D", "D", guard="z >= 0")])),
        "E<> (v == 1)", ["z"]),
    "r14 dropping a select variable": (
        net(["clock z;", "int[0,1] v;"],
            T("Step", "S", [L("S", kind="committed"), L("D")],
              [E("S", "D", select="n : int[-1,-1]", guard="n >= 0", update="v = 1"),
               E("D", "D", guard="z >= 0")])),
        "E<> (v == 1)", ["n"]),
    "r14 variable read only by the query": (
        net(["clock z;", "int[0,1] f;", "int[0,1] v;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0", update="f = 1")])),
        "A[] (v == 0)", []),
    "r14 query names a location without edges": (
        net(["clock z;", "int[0,1] v;"],
            T("Step", "S", [L("S"), L("D")], [E("S", "S", guard="z >= 0", update="v = 1")])),
        "E<> Step.D", []),
    "r14 network without a clock": (
        net(["int[0,1] v;"], T("Step", "S", [L("S")], [E("S", "S", update="v = 1")])),
        "E<> (v == 1)", []),
    "r15 initial location without edges": (
        net(["clock z;", "int[0,1] v;"],
            T("Step", "S", [L("S"), L("D")], [E("D", "D", guard="z >= 0", update="v = 1")])),
        "E<> (v == 1)", []),
}


def main():
    bad = 0
    for name, (m, f, drop) in REFUSED.items():
        try:
            MU.lower(m, f, drop)
            print(f"FAIL {name}: accepted")
            bad += 1
        except ValueError as e:
            print(f"ok   {name}: {str(e)[:90]}")
    # r1: a covered split of a dropped clock is still accepted
    MU.lower(net(["clock x, z;", "int[0,1] flag;"],
                 T("Step", "Pre", [L("Pre")], [E("Pre", "Pre", guard="((2 >= x) && (z >= 0))"),
                                               E("Pre", "Pre", guard="((x > 2) && (z >= 0))")])),
             "A[] (!deadlock)", ["x"])
    print("ok   r1 covered split of a dropped clock is accepted")
    # r2: the Init rewrite puts parentheses around a compound body
    low = MU.lower(net(["clock z;", "int[0,1] v = 1;", "int[0,1] hit = 1;"],
                       T("Step", "Pre", [L("Pre")], [E("Pre", "Pre", guard="z >= 0")])),
                   "E<> (v == 0) || (hit == 0)")
    f = R.lowered_formula("E<> (v == 0) || (hit == 0)", low)
    ok = f == "E<> (!(Step.Init) && ((v == 0) || (hit == 0)))"
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r2 formula rewrite: {f}")
    # r2: Killed in a file name is not out of memory
    ok = not R.killed(0, "* Model: /tmp/Killed.muntax\nProperty is not satisfied!") and R.killed(137, "")
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r2 out-of-memory test")
    # r3: Temp_d keeps the kind of Temp
    low = MU.lower(pump(1, "urgent", "y >= 1"), "E<> (hit == 1)")
    kinds = {l.kind for t in low.templates for l in t.locs if l.name.startswith("Temp_")}
    bad += kinds != {"urgent"}
    print(f"{'ok  ' if kinds == {'urgent'} else 'FAIL'} r3 Temp_d kinds: {kinds}")
    # r3: ceiling constants from x == k
    low = MU.lower(net(["clock x;", "int[0,1] f;"],
                       T("Step", "A", [L("A"), L("B")],
                         [E("A", "B", guard="x == 183"), E("B", "B", guard="x >= 0")])), "E<> Step.B")
    ok = any("(x <= 183)" in e.guard for t in low.templates for e in t.edges if "f == 0" in e.guard)
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r3 ceiling from x == 183")
    # r6: a disjunctive guard keeps its grouping when a copy adds a conjunct
    low = MU.lower(net(["int[0,1] v;", "int[0,1] x;", "clock z;"],
                       T("Step", "S", [L("S")], [E("S", "S", guard="v == 0 || v == 1", update="x = v"),
                                                 E("S", "S", guard="z >= 0")])), "E<> (x == 1)")
    gs = [e.guard for t in low.templates for e in t.edges if e.update == "x = 1"]
    ok = gs == ["((v == 0 || v == 1) && (v == 1))"]
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r6 grouping after copy expansion: {gs}")
    # r7: two conditionals on one edge are both expanded
    low = MU.lower(net(["int[0,1] x;", "int[0,1] y;", "clock z;"],
                       T("Step", "S", [L("S")],
                         [E("S", "S", guard="z >= 0",
                            update="x = (x == 1) ? x : 1, y = (y == 1) ? y : 1")])), "E<> (y == 1)")
    ok = not any("?" in e.update for t in low.templates for e in t.edges)
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r7 all conditionals expanded")
    # r8: a reduced select keeps an out-of-range value, so UPPAAL still reports it
    low = MU.lower(net(["int[0,1] v;", "int[0,1] f;", "clock z;"],
                       T("Step", "S", [L("S"), L("D")],
                         [E("S", "D", select="n : int[0,2]", update="v = n"),
                          E("D", "D", guard="z >= 0")])), "A[] (v >= 0)")
    ups = sorted(e.update for t in low.templates for e in t.edges if e.src == "S" and e.dst == "D")
    ok = "v = 2" in ups
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r8 select keeps the out-of-range value: {ups}")
    # r11: constant atoms and true are folded away before Munta sees them
    for G in ("0 == 0", "true"):
        low = MU.lower(net(["int[0,1] v;", "clock z;"],
                           T("Step", "S", [L("S"), L("D")],
                             [E("S", "D", guard=G, update="v = 1"), E("S", "S", guard="z >= 0"),
                              E("D", "D", guard="z >= 0")])), "E<> Step.D")
        gs = [e.guard for t in low.templates for e in t.edges if e.src == "S" and e.dst == "D"]
        ok = gs == [""]
        bad += not ok
        print(f"{'ok  ' if ok else 'FAIL'} r11 guard {G!r} folded: {gs}")
    # r12: whitespace in a guard does not break the Python parser
    for G in (" v == 0", "v == 0\n&& z >= 0"):
        try:
            MU.lower(net(["int[0,1] v;", "clock z;"],
                         T("Step", "S", [L("S"), L("D")],
                           [E("S", "D", select="n : int[0,0]", guard=G, update="v = 1"),
                            E("S", "S", guard="z >= 0"), E("D", "D", guard="z >= 0")])), "E<> Step.D")
            print(f"ok   r12 guard {G!r} lowers")
        except Exception as e:      # noqa: BLE001
            bad += 1
            print(f"FAIL r12 guard {G!r}: {type(e).__name__} {e}")
    # r13: extra spaces in a duration update still give the right Temp_d
    m = net(["clock z;", "int[0,2] dur;", "int[0,1] hit;", "int[0,1] changed;"],
            T("Step", "S", [L("S")], [E("S", "S", guard="z >= 0")]),
            T("Pump", "S", [L("S"), L("Temp", inv="y <= (dur * 60)"), L("D")],
              [E("S", "Temp", update="y = 0, dur = 1"),
               E("Temp", "Temp", guard="changed == 0", update="dur =  2, changed = 1"),
               E("Temp", "D", guard="y >= (dur * 60)"), E("D", "D")], decl="clock y;"))
    low = MU.lower(m, "E<> (changed == 1)")
    tt = sorted((e.src, e.dst) for t in low.templates for e in t.edges
                if e.src.startswith("Temp_") and e.dst.startswith("Temp_") and "changed" in e.update)
    ok = tt == [("Temp_1", "Temp_2"), ("Temp_2", "Temp_2")]
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r13 dur update with extra spaces: {tt}")
    # r13: extra spaces in a conditional update; a tab around imply
    low = MU.lower(net(["int[0,1] v;", "int[0,1] x;", "clock z;"],
                       T("Step", "S", [L("S"), L("D")],
                         [E("S", "D", guard="z >= 0", update="x =  (v == 1) ? x : 1"),
                          E("S", "S"), E("D", "D")])), "E<> (x == 1)")
    ok = not any("?" in e.update for t in low.templates for e in t.edges)
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r13 conditional with extra spaces expanded")
    f = MU.munta_formula("A[] ((v == 0)\timply\t(x == 0))")
    ok = "imply" not in f and "->" in f
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r13 imply with tabs: {f!r}")
    f = MU.munta_formula("A[] ((v == 0)imply(v == 0))")
    ok = "imply" not in f
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r14 imply without spaces: {f!r}")
    # r15: `- 1` becomes `-1` in guards and formulas
    low = MU.lower(net(["clock z;", "int[-1,1] v;"],
                       T("Step", "S", [L("S"), L("D")],
                         [E("S", "D", guard="v == - 1", update="v = 1"), E("S", "S", guard="z >= 0"),
                          E("D", "D", guard="z >= 0")])), "E<> Step.D")
    gs = [e.guard for t in low.templates for e in t.edges if e.src == "S" and e.dst == "D"]
    f = MU.munta_formula("A[] (v >= - 1)")
    ok = gs == ["v == -1"] and f == "A[] (v >= -1)"
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} r15 minus sign: {gs} {f!r}")
    print(f"{bad} failed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
