"""The UPPAAL abstraction of the T2 model (docs/uppaal-plan.md), as a generator.

The model is described once, as Python data (templates with locations and edges),
and `write_uppaal` writes it as UPPAAL XML. U4 adds a Munta writer for the same data.
The description follows the rules found in U0b (uppaal/u0b/README.md) where UPPAAL
allows it: flags are integers compared with 1, updates on one transition are
independent, and comparisons of two variables are written as disjunctions over
their values. It uses three features that Munta lacks and that U4 must encode:
`select`, clock bounds that depend on a variable (`y <= dur * 60`), and clocks in
queries.

Units: one model time unit is one second. Durations are whole minutes.

Work item U1a builds the `Step`, `Channel` and `Pump` parts with a free command
choice. The channel is part of the `Step` chain.

Encodings of the issued fields (section 5 of the plan):
  rc  rate:      0 absent, 1 NaN, 2 negative, 3 zero, 4 low, 5 high
  dk  duration:  0 absent, 1 NaN, 2 fraction, 3 whole (value in dv)
  dv  duration value in whole minutes, -1..121 (0 when dk is not 3)
  uk  units:     0 absent, 1 NaN, 2 finite <= 0, 3 positive (a microbolus)
"""

from dataclasses import dataclass, field
from xml.sax.saxutils import escape

# rate classes of section 4.4, also used for the running temp `tcls`
ZERO, LOW, HIGH = 3, 4, 5
SCHED_OBLIGATION = 9   # P4a: an accepted cancel obliges the schedule

MUTATIONS = {
    "no_duration_upper_bound": "validDuration has no upper bound of 120 minutes",
    "pump_ignores_cancel": "the pump keeps a running temp on an accepted cancel",
    "pump_no_reset_on_replace": "the pump does not reset its clock y when a new temp "
                                "replaces a running one",
    "missing_reject_bolus": "the pump has no edge for the reject reason `bolus`, so a "
                            "command can get stuck in the committed location Ex",
    "pump_drops_valid_temp": "the pump silently drops an accepted valid temp of 30 minutes",
    "reject_cancels_initial": "the pump ends the initial temp on a command that it "
                              "rejects for its duration",
    "reject_executes_bolus": "the pump executes the bolus of a command that it rejects "
                             "for its duration",
}


@dataclass
class Loc:
    name: str
    inv: str = ""
    kind: str = ""          # "", "committed" or "urgent"


@dataclass
class Edge:
    src: str
    dst: str
    guard: str = ""
    sync: str = ""
    update: str = ""
    select: str = ""


@dataclass
class Template:
    name: str
    init: str
    locs: list
    edges: list
    decl: str = ""


@dataclass
class Model:
    decl: list = field(default_factory=list)
    templates: list = field(default_factory=list)


def any_of(var, values):
    """`var` equals one of `values`, as a disjunction of atoms."""
    return "(" + " || ".join(f"({var} == {v})" for v in values) + ")"


def same_class(a, b):
    """`a == b` for two rate-class variables, as a disjunction over the classes."""
    return "(" + " || ".join(f"(({a} == {c}) && ({b} == {c}))" for c in (ZERO, LOW, HIGH)) + ")"


CLEAR = "rc = 0, dk = 0, dv = 0, uk = 0, expB = 0, bolusDone = 0"
EFF_TEMP = "(Pump.Temp && (Pump.y < (dur * 60)))"   # the pump delivers the temp class


def build(mutations=(), witnesses=False):
    """The U1a model: Step (with channel and pump execution) and Pump.

    With `witnesses`, edges also set the witness flags `w...`. The flags multiply
    the state space, so only the witness queries use them.
    """
    for m in mutations:
        if m not in MUTATIONS:
            raise ValueError(f"unknown mutation {m}")
    upper = 121 if "no_duration_upper_bound" in mutations else 120

    def w(flag, rest=""):
        """`rest` plus `flag = 1` in the witness model."""
        parts = [x for x in (rest, f"{flag} = 1" if witnesses else "") if x]
        return ", ".join(parts)

    # the witness flag of a rejection holds for one step only
    clear = CLEAR + (", wRejBolus = 0" if witnesses else "")

    m = Model()
    m.decl += [
        "// issued fields of the last cycle (encodings in uppaal/model.py)",
        "int[0,5] rc; int[0,3] dk; int[-1,121] dv; int[0,3] uk;",
        "// running temp of the pump: class and duration in minutes",
        "int[0,5] tcls; int[0,121] dur;",
        "// class of an initial temp (pre-run)",
        "int[0,5] ic;",
        "int[0,1] busy;        // inside the committed chain of a step",
        "int[0,1] first;       // the next step is the first one, allowed at t0",
        "int[0,1] initDone;    // the initial temp is installed",
        "clock g;              // time since the start or the last step",
        "clock obs;            // time since the close of the run",
        "// P4a observer: obligation class, duration, own clock",
        "// It starts with the obligation `eff == sched` (no initial temp).",
        f"int[0,9] oCls = {SCHED_OBLIGATION}; int[0,121] oDur; clock o4;",
        "// bolus observer: the expected and the executed bolus of this step",
        "int[0,1] expB; int[0,1] bolusDone;",
        "chan initTemp, setTemp, cancel;",
    ]
    if witnesses:
        m.decl += [
            "// witness flags",
            "int[0,1] wColl;       // a new temp at the deadline of the running one",
            "int[0,1] wRejBolus;   // rejected: invalid duration with a positive bolus",
            "int[0,1] wNoSteps;    // the run closed at t0 without steps",
            "int[0,1] wCancel;     // an accepted cancel of a running temp",
        ]

    # The five reasons of validate to reject a command (section 5 of the plan).
    # They can overlap; each is a separate edge with the same effect.
    reject = {
        "presence": "(((rc == 0) && (dk >= 1)) || ((rc >= 1) && (dk == 0)))",
        "nan": "((rc == 1) || (dk == 1) || (uk == 1))",
        "duration": f"((dk == 2) || ((dk == 3) && ((dv < 0) || ((dv >= 1) && (dv <= 29)) "
                    f"|| (dv > {upper}))))",
        "bolus": "(uk == 2)",
        "negative": "((rc == 2) && (dk >= 1))",
    }
    temp_ok_rate = "(rc >= 3)"

    step = Template(
        "Step", "Pre",
        locs=[Loc("Pre"), Loc("PreC", kind="committed"), Loc("Idle"),
              Loc("S1", kind="committed"), Loc("Iss", kind="committed"),
              Loc("Ch", kind="committed"), Loc("Ex", kind="committed"),
              Loc("End", kind="committed"), Loc("Closed")],
        edges=[
            # pre-run: an optional initial temp of rate >= 0, at a time of its own
            Edge("Pre", "PreC", guard="(initDone == 0)", select="c : int[3,5]",
                 update="ic = c, initDone = 1"),
            # the observer takes the initial temp as an obligation, with its own
            # copy of the duration of each class
            Edge("PreC", "Pre", guard="(ic == 3)", sync="initTemp!",
                 update="oCls = ic, oDur = 120, o4 = 0"),
            Edge("PreC", "Pre", guard="(ic >= 4)", sync="initTemp!",
                 update="oCls = ic, oDur = 30, o4 = 0"),
            # start at t0; or close at t0 without steps
            Edge("Pre", "Idle", update="g = 0, first = 1, ic = 0"),
            Edge("Pre", "Closed", update=w("wNoSteps", "obs = 0, ic = 0")),
            # a step: the first one can be at t0, later ones need g > 0
            Edge("Idle", "S1", guard="((first == 1) || (g > 0))",
                 update="busy = 1, first = 0, g = 0"),
            # phase 1 (readings, user boluses) is empty in U1a
            Edge("S1", "End"),                              # a step without a cycle
            # phase 2: free choice of the issued fields
            Edge("S1", "Iss", select="r : int[0,5], d : int[0,3], v : int[-1,121], u : int[0,3]",
                 guard="((d == 3) || (v == 0))",
                 update="rc = r, dk = d, dv = v, uk = u"),
            # phase 3: issue observation (observers come in U1b)
            Edge("Iss", "Ch"),
            # phase 4: channel
            Edge("Ch", "End"),                              # lost
            # accepted: see the observer edges below
        ],
    )
    # The observer of an accepted command. It has its own copy of `validate`
    # (with the bound 120, which no mutation changes) and sets the expected effect
    # before the pump executes the command: the P4a obligation and `expB`.
    o_notemp = "((rc == 0) && (dk == 0))"
    o_cancel = "((rc >= 3) && (dk == 3) && (dv == 0))"
    o_temp = "((rc >= 3) && (dk == 3) && (dv >= 30) && (dv <= 120))"
    o_bad_temp = ("(((rc == 0) && (dk >= 1)) || (rc == 1) || (rc == 2) || ((rc >= 3) && (dk <= 2)) "
                  "|| ((rc >= 3) && (dk == 3) && ((dv < 0) || ((dv >= 1) && (dv <= 29)) "
                  "|| (dv > 120))))")
    o_bad_bolus = "((uk == 1) || (uk == 2))"
    for tg, eff in ((o_notemp, ""), (o_cancel, f"oCls = {SCHED_OBLIGATION}, oDur = 0, o4 = 0"),
                    (o_temp, "oCls = rc, oDur = dv, o4 = 0")):
        step.edges.append(Edge("Ch", "Ex", guard=f"({tg} && (uk == 0))", update=eff))
        step.edges.append(Edge("Ch", "Ex", guard=f"({tg} && (uk == 3))",
                               update=", ".join(x for x in (eff, "expB = 1") if x)))
    step.edges.append(Edge("Ch", "Ex", guard=o_bad_temp))      # rejected: no effect
    step.edges.append(Edge("Ch", "Ex", guard=o_bad_bolus))
    # phase 5: pump execution
    for why, g in reject.items():
        if why == "bolus" and "missing_reject_bolus" in mutations:
            continue
        if why == "duration":
            bad = "bolusDone = 1" if "reject_executes_bolus" in mutations else ""
            rc_sync = "rejCancel!" if "reject_cancels_initial" in mutations else ""
            step.edges.append(Edge("Ex", "End", guard=f"({g} && (uk == 3))", sync=rc_sync,
                                   update=w("wRejBolus", bad)))
            step.edges.append(Edge("Ex", "End", guard=f"({g} && (uk <= 2))", sync=rc_sync))
        else:
            step.edges.append(Edge("Ex", "End", guard=g))
    # valid commands: no temp part, cancel, temp; each with or without a bolus
    valid_temp = f"({temp_ok_rate} && (dk == 3) && (dv >= 30) && (dv <= {upper}))"
    valid = [(f"((rc == 0) && (dk == 0))", ""),
             (f"({temp_ok_rate} && (dk == 3) && (dv == 0))", "cancel!")]
    if "pump_drops_valid_temp" in mutations:
        valid += [(f"({valid_temp} && (dv >= 31))", "setTemp!"), (f"({valid_temp} && (dv == 30))", "")]
    else:
        valid += [(valid_temp, "setTemp!")]
    for vg, sync in valid:
        step.edges.append(Edge("Ex", "End", guard=f"({vg} && (uk == 0))", sync=sync))
        step.edges.append(Edge("Ex", "End", guard=f"({vg} && (uk == 3))", sync=sync,
                               update="bolusDone = 1"))
    step.edges += [
        # the end of a step: continue, or close the run in the same chain
        # The issued fields are dead after execution; clearing them keeps the
        # state space small.
        Edge("End", "Idle", update=f"busy = 0, {clear}"),
        Edge("End", "Closed", update=f"busy = 0, obs = 0, {clear}"),
        # A closed run lets time pass forever. The self-loop changes no variable;
        # it keeps the end of a run from counting as a deadlock, which Munta
        # needs (uppaal/u0b/README.md).
        Edge("Closed", "Closed"),
    ]

    y_replace = "" if "pump_no_reset_on_replace" in mutations else "y = 0, "
    pump = Template(
        "Pump", "Sched", decl="clock y;",
        locs=[Loc("Sched"), Loc("Temp", inv="y <= (dur * 60)")],
        edges=[
            # initial temp: the longest duration its class allows (InvTemp). Installed
            # at any time at or before t0, it gives every remaining time.
            Edge("Sched", "Temp", guard="(ic == 3)", sync="initTemp?",
                 update="y = 0, dur = 120, tcls = ic"),
            Edge("Sched", "Temp", guard="(ic >= 4)", sync="initTemp?",
                 update="y = 0, dur = 30, tcls = ic"),
            Edge("Sched", "Temp", sync="setTemp?", update="y = 0, dur = dv, tcls = rc"),
            Edge("Temp", "Temp", guard="(y < (dur * 60))", sync="setTemp?",
                 update=f"{y_replace}dur = dv, tcls = rc"),
            Edge("Temp", "Temp", guard="(y >= (dur * 60))", sync="setTemp?",
                 update=w("wColl", f"{y_replace}dur = dv, tcls = rc")),
            Edge("Sched", "Sched", sync="cancel?"),
            # expiry at the deadline
            Edge("Temp", "Sched", guard="(y >= (dur * 60))"),
        ],
    )
    if "pump_ignores_cancel" in mutations:
        pump.edges.append(Edge("Temp", "Temp", sync="cancel?"))
    elif witnesses:
        # the witness model marks a cancel of a temp that still runs
        pump.edges.append(Edge("Temp", "Sched", guard="(y < (dur * 60))", sync="cancel?",
                               update="wCancel = 1"))
        pump.edges.append(Edge("Temp", "Sched", guard="(y >= (dur * 60))", sync="cancel?"))
    else:
        pump.edges.append(Edge("Temp", "Sched", sync="cancel?"))
    if "reject_cancels_initial" in mutations:
        # the pump remembers whether its temp is the initial one
        m.decl += ["int[0,1] pInit;", "chan rejCancel;"]
        for e in pump.edges:
            if e.sync == "initTemp?":
                e.update += ", pInit = 1"
            elif e.sync == "setTemp?":
                e.update += ", pInit = 0"
        pump.edges += [Edge("Temp", "Sched", guard="(pInit == 1)", sync="rejCancel?"),
                       Edge("Temp", "Temp", guard="(pInit == 0)", sync="rejCancel?"),
                       Edge("Sched", "Sched", sync="rejCancel?")]
    m.templates = [step, pump]
    return m


def write_uppaal(model, path):
    out = ['<?xml version="1.0" encoding="utf-8"?>',
           "<!DOCTYPE nta PUBLIC '-//Uppaal Team//DTD Flat System 1.6//EN' "
           "'http://www.it.uu.se/research/group/darts/uppaal/flat-1_6.dtd'>",
           "<nta>", f"<declaration>{escape(chr(10).join(model.decl))}</declaration>"]
    for t in model.templates:
        ids = {l.name: f"{t.name}_{i}" for i, l in enumerate(t.locs)}
        out.append(f"<template><name>{t.name}T</name>")
        if t.decl:
            out.append(f"<declaration>{escape(t.decl)}</declaration>")
        for l in t.locs:
            out.append(f'<location id="{ids[l.name]}"><name>{l.name}</name>')
            if l.inv:
                out.append(f'<label kind="invariant">{escape(l.inv)}</label>')
            if l.kind:
                out.append(f"<{l.kind}/>")
            out.append("</location>")
        out.append(f'<init ref="{ids[t.init]}"/>')
        for e in t.edges:
            out.append(f'<transition><source ref="{ids[e.src]}"/><target ref="{ids[e.dst]}"/>')
            for kind, text in (("select", e.select), ("guard", e.guard),
                               ("synchronisation", e.sync), ("assignment", e.update)):
                if text:
                    out.append(f'<label kind="{kind}">{escape(text)}</label>')
            out.append("</transition>")
        out.append("</template>")
    insts = "\n".join(f"{t.name} = {t.name}T();" for t in model.templates)
    names = ", ".join(t.name for t in model.templates)
    out.append(f"<system>{escape(insts)}\nsystem {names};</system>")
    out.append("</nta>")
    path.write_text("\n".join(out) + "\n")
