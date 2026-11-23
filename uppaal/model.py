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
choice (`build(contract=False)`). The channel is part of the `Step` chain. Work item
U1b adds the `Controller`, `CGM` and `User` templates, the controller contract of
section 5 and the observers of P1, P3 and P5 (`build(contract=True)`).

Encodings of the issued fields (section 5 of the plan):
  rc  rate:      0 absent, 1 NaN, 2 negative, 3 zero, 4 low, 5 high
  dk  duration:  0 absent, 1 NaN, 2 fraction in [30, 120], 3 whole (value in dv),
                 4 fraction outside [30, 120]
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
    # U1b: mutations of the controller side only
    "p1_rejected_high": "the controller issues a high rate without a fresh reading when "
                        "the command is rejected (absent or NaN duration)",
    "p1_nan_units": "the controller issues NaN or non-positive units without a fresh "
                    "reading",
    "p1_no_hasreading": "the controller's freshness guard drops `hasReading`",
    "p3_positive_120": "the controller issues a positive temp of 120 minutes",
    "p5_no_user_reset": "the controller clock `sinceBolus` is not reset on a user bolus",
    "p5_reset_on_lost": "the controller clock `sinceBolus` is also reset on a lost or "
                        "rejected command",
    "cgm_first_unrecorded": "CGM can take the first reading on its edge for later "
                            "readings, without setting `hasReading`",
}

SPACING = 183      # 60·I + 3 seconds for I = 3 (smb_guard_iff in LeanAID/Time/SmbSpacing.lean)
FRESH_AGE = 723    # a reading is fresh below 723 s (p1_derived, section 4.1 of the plan)
READ_GAP = 150     # readings are at least 150 s apart (R_U)


def ranges_dnf(pred, r, d, v):
    """A disjunction over (rate code, duration kind, duration value) that holds
    exactly where `pred(rate, kind, value)` holds. The value matters only for kind 3;
    for the other kinds it is 0."""
    terms = []
    for rr in range(6):
        for dd in range(5):
            if dd != 3:
                if pred(rr, dd, 0):
                    terms.append(f"(({r} == {rr}) && ({d} == {dd}))")
                continue
            vals = [x for x in range(-1, 122) if pred(rr, 3, x)]
            while vals:
                lo = hi = vals.pop(0)
                while vals and vals[0] == hi + 1:
                    hi = vals.pop(0)
                terms.append(f"(({r} == {rr}) && ({d} == 3) && ({v} >= {lo}) && ({v} <= {hi}))")
    assert terms
    return "(" + " || ".join(terms) + ")"


def ranges(pred):
    """The (rate code, duration kind, lowest value, highest value) blocks where
    `pred` holds, as in `ranges_dnf`."""
    out = []
    for rr in range(6):
        for dd in range(5):
            if dd != 3:
                if pred(rr, dd, 0):
                    out.append((rr, dd, 0, 0))
                continue
            vals = [x for x in range(-1, 122) if pred(rr, 3, x)]
            while vals:
                lo = hi = vals.pop(0)
                while vals and vals[0] == hi + 1:
                    hi = vals.pop(0)
                out.append((rr, 3, lo, hi))
    return out


def contract_temp(r, k, v, positive_120=False):
    """The temp part of the contract (section 5): no negative rate, a duration that is
    absent, NaN, 0, whole in 30..120 or a fraction in [30, 120], and `TempOk` on the
    finite fields. `positive_120` is the mutation p3_positive_120."""
    if r == 2 or k == 4:
        return False
    if k == 3 and not (v == 0 or 30 <= v <= 120):
        return False
    if k in (2, 3) and r in (LOW, HIGH):
        return (k == 3 and v in (0, 30)) or (positive_120 and k == 3 and v == 120)
    return True


def temp_ok_observer(r, k, v):
    """The P3 observer's own copy of `TempOk` (LeanAID/Time/Duration.lean): a finite
    duration d is 0 or in [30, 120]; with a finite rate r as well, d = 0, or
    d in [30, 120] and r = 0, or d = 30 and r >= 0."""
    if k in (0, 1):
        return True
    if k == 3:
        d0, rng, d30 = v == 0, 30 <= v <= 120, v == 30
    elif k == 2:
        d0, rng, d30 = False, True, False
    else:
        d0, rng, d30 = False, False, False
    if not (d0 or rng):
        return False
    if r in (0, 1):
        return True
    return d0 or (rng and r == ZERO) or (d30 and r >= ZERO)


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


def build(mutations=(), witnesses=False, contract=False, relaxed=False):
    """The model: Step (with channel and pump execution) and Pump, and with
    `contract` also Controller, CGM, User and the observers of U1b.

    With `relaxed` (and without `contract`), the free command choice is limited to
    the field domains and `TempOk` of the contract, without the freshness and spacing
    guards. This variant has more behaviors than the contract model on the pump, the
    P4a observer and the close (see `RELATION` in check.py).

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
    clear = CLEAR + (", wRejBolus = 0" if witnesses else "") + \
        (", wUb = 0" if (witnesses and contract) else "")

    m = Model()
    m.decl += [
        "// issued fields of the last cycle (encodings in uppaal/model.py)",
        "int[0,5] rc; int[0,4] dk; int[-1,121] dv; int[0,3] uk;",
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
    if contract:
        m.decl += [
            "// CGM: a reading exists, clock since the last reading",
            "int[0,1] hasReading; clock age;",
            "// controller: clock since the last bolus it sees, no bolus in the history",
            "clock sinceBolus; int[0,1] noBolus = 1;",
            "int[0,1] preB;        // the pre-run bolus happened",
            "// observers: latched errors",
            "int[0,1] err1; int[0,1] err3; int[0,1] err5; int[0,1] errPair;",
            "// P5 observer: a real prior bolus, its own clock since it",
            "int[0,1] prior; clock p5c;",
            "// P5-pair observer: an accepted microbolus happened, clock since it",
            "int[0,1] mb1; clock pb;",
            "// reading observer: a reading happened, clock since it, latched error",
            "int[0,1] rdSeen; clock rdc; int[0,1] errRead;",
            "chan read, ubolus, decide;",
        ]
        if witnesses:
            m.decl += [
                "int[0,1] wUb;         // a user bolus in this step",
                "int[0,1] mb2;         // a second accepted microbolus",
                "int[0,1] f20;         // the obligation is a zero temp of 120 min from a cycle",
                "int[0,3] nRead;       // readings so far, up to 3 (U3b witnesses)",
                "int[0,1] wOdd;        // an issued output that the U3b runs do not give",
            ]

    # The five reasons of validate to reject a command (section 5 of the plan).
    # They can overlap; each is a separate edge with the same effect.
    reject = {
        "presence": "(((rc == 0) && (dk >= 1)) || ((rc >= 1) && (dk == 0)))",
        "nan": "((rc == 1) || (dk == 1) || (uk == 1))",
        "duration": f"((dk == 2) || (dk == 4) || ((dk == 3) && ((dv < 0) || ((dv >= 1) && (dv <= 29)) "
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
            Edge("S1", "Iss", select="r : int[0,5], d : int[0,4], v : int[-1,121], u : int[0,3]",
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
    o_bad_temp = ("(((rc == 0) && (dk >= 1)) || (rc == 1) || (rc == 2) "
                  "|| ((rc >= 3) && ((dk <= 2) || (dk == 4))) "
                  "|| ((rc >= 3) && (dk == 3) && ((dv < 0) || ((dv >= 1) && (dv <= 29)) "
                  "|| (dv > 120))))")
    o_bad_bolus = "((uk == 1) || (uk == 2))"
    def join(*parts):
        return ", ".join(x for x in parts if x)

    # U1b: an accepted valid microbolus sets `prior` and resets the clocks of the P5
    # and P5-pair observers. The pair observer latches `errPair` if the previous one
    # was less than SPACING seconds before.
    pair = [("(mb1 == 0)", ""),
            (f"((mb1 == 1) && (pb >= {SPACING}))", "mb2 = 1" if witnesses else ""),
            (f"((mb1 == 1) && (pb < {SPACING}))", join("errPair = 1", "mb2 = 1" if witnesses else ""))]
    # U1b witness model: `f20` marks an obligation of a zero temp of 120 minutes
    f20 = {o_notemp: [("", "")],
           o_cancel: [("", "f20 = 0")],
           o_temp: [("((rc == 3) && (dv == 120))", "f20 = 1"),
                    ("((rc >= 4) || (dv <= 119))", "f20 = 0")]}
    for tg, eff in ((o_notemp, ""), (o_cancel, f"oCls = {SCHED_OBLIGATION}, oDur = 0, o4 = 0"),
                    (o_temp, "oCls = rc, oDur = dv, o4 = 0")):
        fv = f20[tg] if (contract and witnesses) else [("", "")]
        for fg, fu in fv:
            g0 = f"({tg} && {fg})" if fg else tg
            step.edges.append(Edge("Ch", "Ex", guard=f"({g0} && (uk == 0))", update=join(eff, fu)))
            for pg, pu in (pair if contract else [("", "")]):
                g3 = f"({g0} && (uk == 3) && {pg})" if pg else f"({g0} && (uk == 3))"
                p5 = "p5c = 0, prior = 1, mb1 = 1, pb = 0" if contract else ""
                step.edges.append(Edge("Ch", "Ex", guard=g3, update=join(eff, fu, "expB = 1", p5, pu)))
    step.edges.append(Edge("Ch", "Ex", guard=o_bad_temp))      # rejected: no effect
    step.edges.append(Edge("Ch", "Ex", guard=o_bad_bolus))
    # phase 5: pump execution
    lost_reset = "sinceBolus = 0" if "p5_reset_on_lost" in mutations else ""
    for e in step.edges:
        if e.src == "Ch" and e.dst == "End":
            e.update = join(e.update, lost_reset)
    for why, g in reject.items():
        if why == "bolus" and "missing_reject_bolus" in mutations:
            continue
        if why == "duration":
            bad = "bolusDone = 1" if "reject_executes_bolus" in mutations else ""
            rc_sync = "rejCancel!" if "reject_cancels_initial" in mutations else ""
            step.edges.append(Edge("Ex", "End", guard=f"({g} && (uk == 3))", sync=rc_sync,
                                   update=join(w("wRejBolus", bad), lost_reset)))
            step.edges.append(Edge("Ex", "End", guard=f"({g} && (uk <= 2))", sync=rc_sync,
                                   update=lost_reset))
        else:
            step.edges.append(Edge("Ex", "End", guard=g, update=lost_reset))
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
        # an accepted microbolus is in the history that the controller reads
        step.edges.append(Edge("Ex", "End", guard=f"({vg} && (uk == 3))", sync=sync,
                               update=join("bolusDone = 1",
                                           "sinceBolus = 0, noBolus = 0" if contract else "")))
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
    if relaxed:
        step.edges = [e for e in step.edges if not (e.src == "S1" and e.dst == "Iss")]
        pos120 = "p3_positive_120" in mutations
        for rr, dd, lo, hi in ranges(lambda r, k, v: contract_temp(r, k, v, pos120)):
            sel = ([f"v : int[{lo},{hi}]"] if lo != hi else []) + ["u : int[0,3]"]
            vv = "v" if lo != hi else str(lo)
            step.edges.append(Edge("S1", "Iss", select=", ".join(sel),
                                   update=f"rc = {rr}, dk = {dd}, dv = {vv}, uk = u"))
    m.templates = [step, pump]
    if contract:
        add_contract(m, step, mutations, witnesses)
    return m


def add_contract(m, step, mutations, witnesses):
    """U1b: phases 1 to 3 with CGM, User, Controller and the issue observers."""
    def join(*parts):
        return ", ".join(x for x in parts if x)

    step.edges = [e for e in step.edges
                  if not (e.src == "S1" or (e.src == "Iss" and e.dst == "Ch"))]
    step.locs += [Loc(n, kind="committed") for n in ("R1", "U1", "O1", "O3")]
    step.edges += [
        # pre-run: the last bolus before the run, optional, at a time of its own
        Edge("Pre", "Pre", guard="(preB == 0)",
             update="preB = 1, sinceBolus = 0, noBolus = 0, p5c = 0, prior = 1"),
        # phase 1: an optional reading, then an optional positive user bolus. A
        # non-positive user bolus is a silent event, so it has no edge.
        Edge("S1", "R1"),
        # the reading observer checks the gap of 150 s on its own clock
        Edge("S1", "R1", sync="read!", guard="(rdSeen == 0)", update="rdSeen = 1, rdc = 0"),
        Edge("S1", "R1", sync="read!", guard=f"((rdSeen == 1) && (rdc >= {READ_GAP}))",
             update="rdc = 0"),
        Edge("S1", "R1", sync="read!", guard=f"((rdSeen == 1) && (rdc < {READ_GAP}))",
             update="rdc = 0, errRead = 1"),
        Edge("R1", "U1"),
        Edge("R1", "U1", sync="ubolus!", update=join("p5c = 0, prior = 1",
                                                     "wUb = 1" if witnesses else "")),
        # a step without a cycle
        Edge("U1", "End"),
        # phase 2: the controller chooses the issued fields
        Edge("U1", "Iss", sync="decide!"),
    ]
    # phase 3: the issue observers, each with its own copy of its predicate
    trig = "((rc == 5) || (uk >= 1))"
    ok3 = ranges_dnf(temp_ok_observer, "rc", "dk", "dv")
    bad3 = ranges_dnf(lambda r, k, v: not temp_ok_observer(r, k, v), "rc", "dk", "dv")
    step.edges += [
        # P1: an issued high rate or any units field needs a fresh reading
        Edge("Iss", "O1", guard="((rc <= 4) && (uk == 0))"),
        Edge("Iss", "O1", guard=f"({trig} && (hasReading == 1) && (age < {FRESH_AGE}))"),
        Edge("Iss", "O1", guard=f"({trig} && (hasReading == 0))", update="err1 = 1"),
        Edge("Iss", "O1", guard=f"({trig} && (age >= {FRESH_AGE}))", update="err1 = 1"),
        # P3: TempOk on the finite issued fields
        Edge("O1", "O3", guard=ok3),
        Edge("O1", "O3", guard=bad3, update="err3 = 1"),
        # P5: finite units after a real prior bolus need its own clock >= SPACING
        Edge("O3", "Ch", guard="(uk <= 1)"),
        Edge("O3", "Ch", guard="((uk >= 2) && (prior == 0))"),
        Edge("O3", "Ch", guard=f"((uk >= 2) && (prior == 1) && (p5c >= {SPACING}))"),
        Edge("O3", "Ch", guard=f"((uk >= 2) && (prior == 1) && (p5c < {SPACING}))",
             update="err5 = 1"),
    ]

    if witnesses:
        # count readings up to 3 on the reading edges
        counted = []
        for e in [e for e in step.edges if e.sync == "read!"]:
            step.edges.remove(e)
            counted += [Edge(e.src, e.dst, sync=e.sync, guard=f"({e.guard} && (nRead < 3))",
                             update=join(e.update, "nRead = nRead + 1")),
                        Edge(e.src, e.dst, sync=e.sync, guard=f"({e.guard} && (nRead == 3))",
                             update=e.update)]
        step.edges += counted

    # Controller: the contract of section 5
    blocks = ranges(lambda r, k, v: contract_temp(r, k, v, "p3_positive_120" in mutations))
    fresh = (f"(age < {FRESH_AGE})" if "p1_no_hasreading" in mutations
             else f"((hasReading == 1) && (age < {FRESH_AGE}))")
    # The guards of P1 and P5 by units value, as (rate filter, units values, guard).
    cases = [
        ("nothigh", (0,), ""),
        ("high", (0,), fresh),
        ("any", (1,), fresh),
        ("any", (2, 3), f"({fresh} && (noBolus == 1))"),
        ("any", (2, 3), f"({fresh} && (sinceBolus >= {SPACING}))"),
    ]
    if "p1_rejected_high" in mutations:
        cases.append(("high-rejected", (0,), ""))
    if "p1_nan_units" in mutations:
        cases += [("any", (1,), ""), ("any", (2,), "(noBolus == 1)"),
                  ("any", (2,), f"(sinceBolus >= {SPACING})")]
    # one edge for each block of the contract and each case, with a select over the
    # duration values of the block only
    edges = []
    for rr, dd, lo, hi in blocks:
        for filt, us, g in cases:
            if (filt == "nothigh" and rr == HIGH) or (filt in ("high", "high-rejected") and rr != HIGH):
                continue
            if filt == "high-rejected" and dd > 1:      # absent or NaN duration: rejected
                continue
            sel = [f"v : int[{lo},{hi}]"] if lo != hi else []
            if len(us) > 1:
                sel.append(f"u : int[{us[0]},{us[-1]}]")
            vv = "v" if lo != hi else str(lo)
            uu = "u" if len(us) > 1 else str(us[0])
            upd = f"rc = {rr}, dk = {dd}, dv = {vv}, uk = {uu}"
            if witnesses:
                # U3b: the outputs that oref0 gives in the T2 runs of the replay: none,
                # and after three readings a high temp of 30 min with a microbolus, a
                # low temp of 30 min, a zero temp of 120 min, or a microbolus alone
                # after an earlier accepted microbolus.
                # Any other output sets wOdd.
                shapes = " || ".join(f"(({vv} == {v}) && ({uu} == {u}))"
                                     for (r_, d_, v, u) in ((5, 3, 30, 3), (4, 3, 30, 0), (3, 3, 120, 0),
                                                            (0, 0, 0, 3))
                                     if (r_, d_) == (rr, dd))
                # a microbolus alone only after an earlier accepted one (mb1)
                more = " && (mb1 == 1)" if (rr, dd) == (0, 0) else ""
                ok = "true" if (rr, dd) == (0, 0) and us == (0,) else \
                    (f"((nRead == 3){more} && ({shapes}))" if shapes else "false")
                upd += f", wOdd = ({ok}) ? wOdd : 1"
            edges.append(Edge("C", "C", select=", ".join(sel), guard=g, sync="decide?", update=upd))
    controller = Template("Controller", "C", locs=[Loc("C")], edges=edges)
    cgm = Template("CGM", "G", locs=[Loc("G")], edges=[
        Edge("G", "G", guard="(hasReading == 0)", sync="read?", update="age = 0, hasReading = 1"),
        Edge("G", "G", guard=(f"(age >= {READ_GAP})" if "cgm_first_unrecorded" in mutations
                              else f"((hasReading == 1) && (age >= {READ_GAP}))"),
             sync="read?", update="age = 0"),
    ])
    user_reset = "noBolus = 0" if "p5_no_user_reset" in mutations else "sinceBolus = 0, noBolus = 0"
    user = Template("User", "U", locs=[Loc("U")], edges=[
        Edge("U", "U", sync="ubolus?", update=user_reset)])
    m.templates += [controller, cgm, user]


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


PUMP_SYNCS = ("initTemp!", "setTemp!", "cancel!", "rejCancel!")
P4_VARS = ("oCls", "oDur", "o4", "f20", "tcls", "dur")


def without_pump(m):
    """The variant of a contract model without `Pump` and without the P4a observer.

    The pump never blocks `Step`: it has a receiving edge for every value of its
    guards, and its invariant `y <= dur * 60` is released by the expiry edge, so time
    never stops in `Pump`. The P4a observer only writes its own variables. So the
    variant has the same runs as the main model, projected on the variables that
    remain. The variant drops the sends to the pump and every assignment to a
    variable that only the pump and the P4a observer read.
    """
    m.templates = [t for t in m.templates if t.name != "Pump"]
    for t in m.templates:
        for e in t.edges:
            if e.sync in PUMP_SYNCS:
                e.sync = ""
            parts = [x.strip() for x in e.update.split(",") if x.strip()]
            e.update = ", ".join(x for x in parts if x.split("=")[0].strip() not in P4_VARS)
    return m


def without_boluses(m):
    """The variant of a contract model without user boluses, without the pre-run bolus
    and without controller outputs that carry units. It removes edges only, so it has
    fewer behaviors than the main model: a reachable witness transfers to it."""
    m.templates = [t for t in m.templates if t.name != "User"]
    for t in m.templates:
        if t.name == "Step":
            t.edges = [e for e in t.edges
                       if e.sync != "ubolus!" and not (e.src == "Pre" and e.dst == "Pre")]
        if t.name == "Controller":
            t.edges = [e for e in t.edges if "uk = 0" in e.update]
    return m
