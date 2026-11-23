"""Render UPPAAL witness traces and counterexamples as SVG timelines (work item U2).

For every query of `check.py` whose expected status is `reachable` or `fails`, the
script asks `verifyta` for a shortest concrete trace (`-t1`) and writes it to
`uppaal/traces/`:

  ID.trace   the trace as verifyta prints it, without the progress lines
  ID.svg     a timeline of the trace
  index.md   the list of traces, with the model, the query and the SHA-256 sums

The traces are illustrations of the model, not of T2 runs. U3 replays them on T2.
Times are model seconds, shown relative to the start t0 of the run. A pre-run event
has a negative time.

Usage: python3 -I uppaal/traces.py --verifyta PATH [--only ID ...]
"""

import argparse
import hashlib
import math
import pathlib
import re
import subprocess
import sys
from xml.sax.saxutils import escape

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check as C  # noqa: E402
import model as M  # noqa: E402

OUT = HERE / "traces"
TIMEOUT = 1800

RATE = {0: "absent", 1: "NaN", 2: "negative", 3: "zero", 4: "low", 5: "high"}
UNITS = {0: "absent", 1: "NaN", 2: "≤ 0", 3: "microbolus"}
CLASS_COLOR = {"sched": "#c9c9c9", "zero": "#4a7fc1", "low": "#4caf6a", "high": "#e08a2c"}


# ---------------------------------------------------------------- parsing

class TraceError(ValueError):
    """verifyta output that the parser does not understand."""


# lines that verifyta prints before the trace
PREAMBLE = re.compile(r"^(Verifying formula \d+ at .*|"
                      r" -- Formula is (NOT )?satisfied\.|"
                      r" -- Showing (witness trace|counter example):?)$")


def parse(text):
    """The trace as a list of steps (kind, data, state after). Kinds: "init" (the
    first state), "trans" (data: list of edges), "delay" (data: seconds).

    The grammar is strict: a preamble of known lines, a state, and then any number of
    transitions or delays, each followed by a state. Any other line raises
    TraceError with its line number."""
    lines = text.splitlines()
    n, i = len(lines), 0

    def err(j, why):
        raise TraceError(f"line {j + 1}: {why}: {lines[j]!r}" if j < n else f"end of trace: {why}")

    def skip_blank(j):
        while j < n and lines[j].strip() == "":
            j += 1
        return j

    def state_at(j):
        j = skip_blank(j)
        if j >= n or lines[j] != "State:":
            err(j, "expected 'State:'")
        if j + 2 >= n:
            err(j, "incomplete state")
        loc = lines[j + 1]
        if not (loc.startswith("( ") and loc.endswith(" )")):
            err(j + 1, "expected the locations of a state")
        locs = loc[2:-2].split()
        if not locs or not all(re.fullmatch(r"\w+\.\w+", t) for t in locs):
            err(j + 1, "a location must have the form Process.Location")
        procs = [t.split(".")[0] for t in locs]
        if len(set(procs)) != len(procs):
            err(j + 1, "a process has two locations")
        if steps and procs != [t.split(".")[0] for t in steps[0][2]["locs"]]:
            err(j + 1, "the processes differ from those of the first state")
        vals = {}
        for tok in lines[j + 2].split():
            m = re.fullmatch(r"([\w.]+)=(-?\d+(?:\.\d+)?)", tok)
            if not m:
                err(j + 2, f"bad value {tok!r}")
            if m[1] in vals:
                err(j + 2, f"variable {m[1]} assigned twice")
            vals[m[1]] = number(m[2], j + 2)
        if not vals:
            err(j + 2, "expected the values of a state")
        return {"locs": locs, "vals": vals}, j + 3

    def number(txt, j):
        # values above 10^12 do not occur in the model (its constants are below 10^4)
        x = float(txt) if "." in txt else int(txt)
        if not ((isinstance(x, int) or math.isfinite(x)) and abs(x) <= 10 ** 12):
            err(j, f"number out of range: {txt[:20]}")
        return x

    steps = []
    while i < n and lines[i] != "State:":
        if lines[i].strip() and not PREAMBLE.match(lines[i]):
            err(i, "unknown line before the trace")
        i += 1
    if i >= n:
        raise TraceError("no trace in the output")
    st, i = state_at(i)
    steps.append(("init", None, st))
    while True:
        i = skip_blank(i)
        if i >= n:
            break
        l = lines[i]
        if l == "Transition:":
            edges, i = [], i + 1
            while i < n and lines[i].startswith("  ") and not lines[i].startswith("   "):
                edges.append(parse_edge(lines[i][2:], i))
                i += 1
            if not edges:
                err(i, "empty transition")
            sends = [e["sync"][:-1] for e in edges if e["sync"].endswith("!")]
            recvs = [e["sync"][:-1] for e in edges if e["sync"].endswith("?")]
            if len(sends) > 1 or (sends and sends[0] not in recvs) or \
                    any(r not in sends for r in recvs):
                err(i - 1, "a send without its receive, or a receive without its send")
            st, i = state_at(i)
            steps.append(("trans", edges, st))
        elif l.startswith("Delay: "):
            if not re.fullmatch(r"\d+(?:\.\d+)?", l[7:]):
                err(i, "bad delay: a delay is a finite number >= 0")
            d = number(l[7:], i)
            st, i = state_at(i + 1)
            steps.append(("delay", d, st))
        else:
            err(i, "expected 'Transition:' or 'Delay:'")
    return steps


def parse_edge(s, j=0):
    m = re.fullmatch(r"(\w+)\.(\w+)->(\w+)\.(\w+) \{ (.*) \}", s)
    if not m:
        raise TraceError(f"line {j + 1}: bad edge: {s!r}")
    proc, src, proc2, dst, body = m.groups()
    if proc2 != proc:
        raise TraceError(f"line {j + 1}: edge between two processes: {s!r}")
    parts = body.split(", ")
    if len(parts) < 3:
        raise TraceError(f"line {j + 1}: edge without guard, sync and update: {s!r}")
    if not re.fullmatch(r"tau|\w+[!?]", parts[1]):
        raise TraceError(f"line {j + 1}: bad synchronization {parts[1]!r}: {s!r}")
    for u in parts[2:]:
        if u != "1" and not re.fullmatch(r"[\w.]+ := \S.*", u):
            raise TraceError(f"line {j + 1}: bad update {u!r}: {s!r}")
    return {"proc": proc, "src": src, "dst": dst, "guard": parts[0],
            "sync": parts[1], "updates": parts[2:]}


# ---------------------------------------------------------------- semantics

def duration_text(dk, dv):
    return {0: "absent", 1: "NaN", 2: "fraction in [30, 120]", 4: "fraction outside [30, 120]"}.get(
        dk, f"{dv} min")


def validate_text(v):
    """What `validate` (System.lean) gives for the encoded fields: the expected
    behavior, shown next to the action the model took."""
    rc, dk, dv, uk = v["rc"], v["dk"], v["dv"], v["uk"]
    if uk in (1, 2):
        return "validate: reject"
    bolus = " and microbolus" if uk == 3 else ""
    if rc == 0 and dk == 0:
        return "validate: no temp part" + bolus
    if rc >= 3 and dk == 3 and dv == 0:
        return "validate: cancel" + bolus
    if rc >= 3 and dk == 3 and 30 <= dv <= 120:
        return f"validate: temp {RATE[rc]} {dv} min" + bolus
    return "validate: reject"


def delivered(st):
    """The delivered class `eff` in a state, or None for a model without a pump."""
    if not any(l.startswith("Pump.") for l in st["locs"]):
        return None
    v = st["vals"]
    if "Pump.Temp" in st["locs"] and v["Pump.y"] < v["dur"] * 60:
        return RATE[v["tcls"]]
    return "sched"


def pump_event(e, b, a):
    """The action of one pump edge, from its source, target and the states."""
    s, d, sy = e["src"], e["dst"], e["sync"]
    running = s == "Temp" and b.get("Pump.y", 0) < b.get("dur", 0) * 60
    if sy == "tau":
        return "temp expires at its deadline" if (s, d) == ("Temp", "Sched") else f"{s} to {d}"
    if sy == "initTemp?":
        return f"initial temp starts ({RATE[a['tcls']]}, {a['dur']} min)"
    if sy == "setTemp?":
        what = f"temp {RATE[a['tcls']]} {a['dur']} min"
        if s == "Sched":
            return f"{what} starts"
        return f"{what} replaces the running one" if running else \
            f"{what} starts at the deadline of the old one"
    if sy in ("cancel?", "rejCancel?"):
        cause = "cancel" if sy == "cancel?" else "rejected command"
        if s == "Sched":
            return f"{cause}: no temp running"
        if d == "Sched":
            return f"{cause} ends the running temp" if running else f"{cause} at the deadline"
        return f"{cause} ignored: the temp keeps running"
    return f"{s} to {d} on {sy}"


def events(edges, before, after):
    """Readable events of one transition. Every action comes from the edges taken
    and the states around them, so a mutant shows what it does."""
    out = []
    b, a = before["vals"], after["vals"]
    for e in edges:
        p, s, d, sy = e["proc"], e["src"], e["dst"], e["sync"]
        if p == "Pump":
            out.append(("pump", pump_event(e, b, a)))
            continue
        if p == "Queue":                  # U5 delayed extension
            if sy == "enq?":
                out.append(("exec", "queue full: command dropped" if s == d else "command queued"))
            elif d.startswith("X"):
                out.append(("exec", "queued command executes"))
            continue
        if p != "Step":
            continue
        u5 = u5_event(e, b, a)
        if u5:
            out += u5
            if d != "Iss":       # a decision also shows its issued fields below
                continue
        if s == "PreC" and d == "Pre":
            out.append(("run", "initial temp sent"))
        elif s == "Pre" and d == "Pre":
            out.append(("env", "pre-run bolus"))
        elif s == "Pre" and d == "Idle":
            out.append(("run", "start t0"))
        elif s == "Pre" and d == "Closed":
            out.append(("run", "close at t0, no steps"))
        elif s == "Idle" and d == "S1":
            out.append(("run", "step"))
        elif sy == "read!":
            out.append(("env", "reading"))
        elif sy == "ubolus!":
            out.append(("env", "user bolus"))
        elif d == "Iss":
            out.append(("ctrl", f"rate {RATE[a['rc']]}, duration {duration_text(a['dk'], a['dv'])}, "
                                f"units {UNITS[a['uk']]}"))
        elif d == "End" and s in ("S1", "U1"):
            out.append(("ctrl", "no cycle"))
        elif s == "Ch" and d == "End":
            out.append(("exec", "lost"))
        elif s == "Ch" and d == "Ex":
            out.append(("exec", "accepted"))
        elif s == "Ex" and d == "End":
            sent = {"setTemp!": "temp sent to the pump", "cancel!": "cancel sent to the pump",
                    "rejCancel!": "rejection sent to the pump as a cancel",
                    "tau": "no pump command"}.get(sy, f"sync {sy}")
            out.append(("exec", sent))
            if a.get("bolusDone") == 1 and b.get("bolusDone") == 0:
                out.append(("exec", "microbolus delivered"))
            out.append(("exec", validate_text(b)))
        elif d == "Closed" and s == "End":
            out.append(("run", "run closed"))
    for flag in ("err1", "err3", "err5", "errPair", "errRead"):
        if a.get(flag) == 1 and b.get(flag) == 0:
            out.append(("obs", f"{flag} latched"))
    return out


def u5_event(e, b, a):
    """Events of the Step edges that only the U5 extensions have, or None."""
    s, d, sy = e["src"], e["dst"], e["sync"]
    if s == "Ch" and d == "End" and sy == "enq!":
        return [("exec", "accepted, waits in the queue")]
    if d == "Ch" and s in ("S1", "U1"):
        return [("ctrl", "retry of the pending command (no new decision)")]
    if s == "Ch" and d == "Ack":
        return [("exec", "copy of an executed command: the pump ignores it")]
    if s == "Ack" and d == "End":
        return [("exec", "acknowledgement lost" if a.get("pending") == 1 else "acknowledged")]
    if s == "Ex" and d in ("Ack", "End") and "bolusDone" not in a:
        if b.get("uk") == 3:
            return [("exec", "microbolus executed")]
        if b.get("uk") == 2:
            return [("exec", "units <= 0: rejected")]
        return None
    if s in ("S1", "U1") and d in ("End", "Dec", "Iss"):
        out = []
        for i in (1, 2):
            if a.get(f"snapped{i}", 0) > b.get(f"snapped{i}", 0):
                ok = ", spacing guard true" if a.get(f"snapOk{i}") == 1 else ""
                out.append(("ctrl", f"loop {i} takes a snapshot{ok}"))
            elif d != "End" and b.get(f"snapped{i}") == 1 and a.get(f"snapped{i}") == 0:
                held = f"snapped{i} == 1" in e["guard"]
                out.append(("ctrl", f"loop {i} decides from the snapshot it holds" if held else
                            f"loop {i} takes a new snapshot and decides"))
        if d == "Dec" and not out:
            out.append(("ctrl", "a loop takes a snapshot and decides"))
        return out or None
    return None


def timeline(steps):
    """Columns of events at the same time, the delays between them, and the time
    of the start t0, or None if the trace ends before the run starts."""
    cols, delays = [], []
    t, prev = 0.0, steps[0][2]
    cur = []
    for kind, data, st in steps[1:]:
        if kind == "delay":
            cols.append((t, cur, prev))
            delays.append((data, prev))
            cur, t = [], t + data
        else:
            cur += events(data, prev, st)
        prev = st
    cols.append((t, cur, prev))
    t0 = next((tc for tc, ev, _ in cols for k, x in ev if x in ("start t0", "close at t0, no steps")),
              None)
    return cols, delays, t0


# ---------------------------------------------------------------- SVG

LANES = [("run", "run"), ("env", "CGM and user"), ("ctrl", "issued output"),
         ("exec", "channel and pump"), ("pump", "pump"), ("obs", "observers")]


def wrap(text, n):
    """Split `text` into lines of at most about `n` characters, at spaces."""
    out, cur = [], ""
    for w in text.split(" "):
        if cur and len(cur) + 1 + len(w) > n:
            out.append(cur)
            cur = w
        else:
            cur = f"{cur} {w}" if cur else w
    return out + [cur]


def fmt_t(x):
    return f"{x:g}"


def svg(qid, about, query, variant, steps):
    cols, delays, t0 = timeline(steps)
    colw, left, top = 210, 150, 150
    # each lane is as tall as its longest column, so no label is cut
    lane_lines = [max([3] + [len([w for k, x in ev if k == key for w in wrap(x, 36)])
                             for _, ev, _ in cols]) for key, _ in LANES]
    lane_y = [top]
    for nl in lane_lines:
        lane_y.append(lane_y[-1] + 24 + 13 * nl)
    gaps = [70 + 50 * math.log10(1 + d) for d, _ in delays]
    xs, x = [], left
    for i in range(len(cols)):
        xs.append(x)
        x += colw + (gaps[i] if i < len(gaps) else 0)
    width = max(x + 20, 760)
    band_y = lane_y[-1] + 10
    height = band_y + 90
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width:.0f}" height="{height}" '
         f'font-family="sans-serif" font-size="11">',
         f'<rect width="100%" height="100%" fill="white"/>',
         f'<text x="10" y="20" font-size="15" font-weight="bold">{escape(qid)}</text>',
         f'<text x="10" y="38">{escape(about)}</text>',
         f'<text x="10" y="54" fill="#555">model: {escape(variant)}'
         + (" (the trace ends before the start t0: times are elapsed model time)"
            if t0 is None else "") + "</text>"]
    per = max(60, int((width - 20) / 6.1))
    qwrap = [query[i:i + per] for i in range(0, len(query), per)]
    if len(qwrap) > 4:
        qwrap = qwrap[:4]
        qwrap[-1] = qwrap[-1][:-1] + "…"
    for j, q in enumerate(qwrap):
        o.append(f'<text x="10" y="{70 + 13 * j}" fill="#555" font-family="monospace" '
                 f'font-size="10">{escape(q)}</text>')
    for li, (key, name) in enumerate(LANES):
        y = lane_y[li]
        o.append(f'<line x1="0" y1="{y}" x2="{width:.0f}" y2="{y}" stroke="#eee"/>')
        o.append(f'<text x="10" y="{y + 16}" font-weight="bold">{escape(name)}</text>')
    for (tc, ev, _), xc in zip(cols, xs):
        o.append(f'<line x1="{xc}" y1="{top - 8}" x2="{xc}" y2="{band_y + 34}" stroke="#999" '
                 f'stroke-dasharray="2,3"/>')
        end = " (end of trace)" if xc == xs[-1] else ""
        tl = f"t = {fmt_t(tc - t0)} s" if t0 is not None else f"{fmt_t(tc)} s elapsed"
        o.append(f'<text x="{xc + 3}" y="{top - 12}" fill="#333">{tl}{end}</text>')
        for li, (key, _) in enumerate(LANES):
            lines = [w for k, x in ev if k == key for w in wrap(x, 36)]
            for j, txt in enumerate(lines):
                color = "#b00020" if key == "obs" else "#000"
                o.append(f'<text x="{xc + 4}" y="{lane_y[li] + 16 + 13 * j}" fill="{color}">'
                         f'{escape(txt)}</text>')
    # delivered class over time
    o.append(f'<text x="10" y="{band_y + 20}" font-weight="bold">delivered (eff)</text>')
    for i, (d, st) in enumerate(delays):
        cls = delivered(st)
        x1, x2 = xs[i], xs[i + 1]
        o.append(f'<text x="{(x1 + x2) / 2 - 20:.0f}" y="{band_y + 44}" fill="#333">'
                 f'+{fmt_t(d)} s</text>')
        if cls is None:
            o.append(f'<text x="{x1 + 4}" y="{band_y + 20}" fill="#777">no pump in this model</text>')
            continue
        o.append(f'<rect x="{x1}" y="{band_y + 6}" width="{x2 - x1}" height="20" '
                 f'fill="{CLASS_COLOR[cls]}"/>')
        o.append(f'<text x="{x1 + 4}" y="{band_y + 20}" fill="white">{cls}</text>')
    last = delivered(cols[-1][2])
    if last is not None:
        o.append(f'<text x="{xs[-1] + 4}" y="{band_y + 20}">at the end: {last}</text>')
    ly = band_y + 70
    for j, (cls, col) in enumerate(CLASS_COLOR.items()):
        o.append(f'<rect x="{10 + 90 * j}" y="{ly - 10}" width="12" height="12" fill="{col}"/>')
        o.append(f'<text x="{26 + 90 * j}" y="{ly}">{cls}</text>')
    o.append("</svg>")
    return "\n".join(o) + "\n"


# ---------------------------------------------------------------- main

def clean(out):
    """verifyta output without progress lines and terminal control codes."""
    out = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", out)
    keep = [l for l in out.replace("\r", "\n").splitlines()
            if l and not l.startswith(" -- Throughput") and not l.startswith(" -- Load")]
    return "\n".join(keep) + "\n"


def trace_problem(cmd, expected):
    """Run verifyta. Return (text, steps) for a good trace, or the reason why not:
    the run must end with exit code 0, give exactly one answer, the expected one
    (satisfied for `reachable`, not satisfied for `fails`), and a trace that `parse`
    accepts."""
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return "timeout"
    if p.returncode != 0:
        return f"verifyta exit code {p.returncode}"
    text = clean(p.stdout + p.stderr)
    sat, unsat = text.count("Formula is satisfied."), text.count("Formula is NOT satisfied.")
    if sat + unsat != 1:
        return "not exactly one answer"
    if (sat == 1) != (expected == "reachable"):
        return f"answer differs from the expected status {expected}"
    try:
        return text, parse(text)
    except TraceError as e:
        return f"trace not understood: {e}"


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verifyta", required=True)
    ap.add_argument("--only", nargs="+", metavar="ID")
    ap.add_argument("--u5", action="store_true",
                    help="render the U5 traces into traces/u5 instead (not replayed in U3)")
    args = ap.parse_args()
    out_dir = OUT / "u5" if args.u5 else OUT
    chosen = [q for q in (C.QUERIES_U5 if args.u5 else C.ALL) if q[6] in ("reachable", "fails")]
    if args.only:
        unknown = sorted(set(args.only) - {q[0] for q in chosen})
        if unknown:
            ap.error(f"unknown or traceless query IDs: {' '.join(unknown)}")
        chosen = [q for q in chosen if q[0] in args.only]
    out_dir.mkdir(exist_ok=True)
    work = HERE / "out"
    work.mkdir(exist_ok=True)
    rows, bad = [], 0
    for (qid, item, kind, model, muts, query, expected, about, _search) in chosen:
        wit = kind == "witness"
        name = model + "".join("." + m for m in muts) + (".witness" if wit else "")
        xml, qfile = work / f"{name}.xml", work / f"{qid}.q"
        M.write_uppaal(C.build(model, muts, wit), xml)
        qfile.write_text(query + "\n")
        cmd = [args.verifyta, "-t1", "-q", str(xml), str(qfile)]
        why = trace_problem(cmd, expected)
        if isinstance(why, str):
            print(f"BAD {qid}: {why}")
            bad += 1
            continue
        text, steps = why
        (out_dir / f"{qid}.trace").write_text(text)
        variant = name.replace(".witness", "") + (" (with witness flags)" if wit else "")
        (out_dir / f"{qid}.svg").write_text(svg(qid, about, query, variant, steps))
        nstates = len(steps)          # every step ends in a printed state
        print(f"ok  {qid:20} {nstates} states")
        rows.append((qid, kind, name, nstates, sha256(xml), sha256(qfile)))
    lines = ["# UPPAAL traces", "",
             "Generated by `uppaal/traces.py`. Each trace is a shortest concrete trace",
             "from `verifyta -t1`: a witness of a reachable query, or a counterexample of",
             "a query that fails (a mutation, or P4b-30-free on the U1a model). The",
             "traces show the model, not T2 runs. `states` counts the printed states,",
             "the initial state included.", "",
             "| ID | kind | model | states | model SHA-256 | query SHA-256 |",
             "|---|---|---|---|---|---|"]
    if args.u5:
        lines[0:7] = ["# UPPAAL traces of the U5 extensions", "",
                      "Generated by `uppaal/traces.py --u5`. Each trace is a shortest concrete",
                      "trace from `verifyta -t1` on a model of `uppaal/extensions.md`. These",
                      "traces are not T2 runs, because T2 excludes the extensions, and U3 does",
                      "not replay them. A counterexample is a candidate finding",
                      "(`docs/FINDINGS.md`). `states` counts the printed states."]
    lines += [f"| [{r[0]}]({r[0]}.svg) | {r[1]} | {r[2]} | {r[3]} | `{r[4]}` | `{r[5]}` |"
              for r in rows]
    if not args.only:
        (out_dir / "index.md").write_text("\n".join(lines) + "\n")
    print(f"{len(rows)} traces, {bad} missing")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
