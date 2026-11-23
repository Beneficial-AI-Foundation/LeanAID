"""Replay the UPPAAL traces of U1a on the T2 pump (work item U3, docs/uppaal-plan.md).

U1a traces have free commands, which no legal controller run gives, so they are
replayed on the pump alone (section 7, level 2). For each trace in uppaal/traces/
on the free model, the script writes to LeanAID/Conformance/UppaalReplay.lean:

  - a T2 environment whose initial temp is the one the trace installs before t0,
  - a T2 run with one step for each cycle of the trace, at the same time, with the
    issued fields of the trace as the result and the channel outcome of the trace,
  - the projection the trace shows: for each cycle its outcome, the pump action and
    whether a bolus is delivered; and the delivered class at the end of each group
    of transitions between steps, and 1 ms before and at each temp deadline that
    falls inside a delay,
  - a theorem, checked by `native_decide`, that the T2 run matches the projection
    (`traceMatch ... = true`, the trace is realized) or does not (`= false`).

The expected result: a witness, and the counterexample of P4b-30-free, is realized.
The counterexample of a mutation is not realized: the mutant does something that the
T2 pump does not. The deadlock counterexample (M-missing-reject) is not replayed,
because deadlock is a property of the automata (section 7, replay categories).

Encoding of classes as T2 rates, with a schedule of 1 U/h (checked at every
checkpoint): the schedule 1, zero 0, low 1/2, high 2.
A fraction in [30, 120] is 91/2 minutes, a fraction outside it 21/2, finite units
<= 0 is 0, positive units is 1/10. Model second s is T2 time T0 + 1000 * (s - t0).

Usage: python3 -I uppaal/replay.py
"""

import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import traces as TR  # noqa: E402

ROOT = HERE.parent
LEAN = ROOT / "LeanAID" / "Conformance" / "UppaalReplay.lean"
REPORT = HERE / "replay.json"
T0 = 1795003200000                    # the start time of the runs in Conformance/TimeRuns.lean

RATE_VAL = {0: None, 1: "nan", 2: "-1", 3: "0", 4: "1/2", 5: "2"}
CLASS_VAL = {"sched": "1", "zero": "0", "low": "1/2", "high": "2"}
UNITS_VAL = {0: None, 1: "nan", 2: "0", 3: "1/10"}


def dur_val(dk, dv):
    return {0: None, 1: "nan", 2: "91/2", 4: "21/2"}.get(dk, str(dv))


def js(v):
    """A Lean `Option JsNum` for a value written as text."""
    if v is None:
        return "none"
    if v == "nan":
        return "some .nan"
    return f"some (.fin ({v}))"


def rat(v):
    return f"({v})"


def project(steps):
    """The cycles, the rate checkpoints, the initial temp and the origin of a trace."""
    cols, delays, t0 = TR.timeline(steps)
    t, prev = 0.0, steps[0][2]
    cycles, cur, init = [], None, None
    for kind, data, st in steps[1:]:
        if kind == "delay":
            t += data
            prev = st
            continue
        b, a = prev["vals"], st["vals"]
        for e in data:
            if e["proc"] == "Pump" and e["sync"] == "initTemp?":
                init = (t, a["tcls"], a["dur"])
            if e["proc"] != "Step":
                continue
            if e["dst"] == "Iss":
                cur = {"time": t, "fields": (a["rc"], a["dk"], a["dv"], a["uk"]), "done": False}
                cycles.append(cur)
            elif (e["src"], e["dst"]) == ("Ch", "End"):
                cur.update(accepted=False, act=("none",), bolus=False, done=True)
            elif (e["src"], e["dst"]) == ("Ch", "Ex"):
                cur.update(accepted=True)
            elif (e["src"], e["dst"]) == ("Ex", "End"):
                rc, dk, dv, uk = cur["fields"]
                act = {"setTemp!": ("temp", RATE_VAL[rc], dv), "cancel!": ("cancel",)}.get(
                    e["sync"], ("none",))
                cur.update(act=act, bolus=(a.get("bolusDone") == 1 and b.get("bolusDone") == 0),
                           done=True)
        prev = st
    origin = t0 if t0 is not None else t
    rates = []
    for i, (tc, _, st) in enumerate(cols):
        # a state between steps, or the last state after a completed execution
        # (rateAt at the time of a step includes all its events)
        last_done = i == len(cols) - 1 and "Step.End" in st["locs"] and all(c["done"] for c in cycles)
        if (st["vals"].get("busy", 0) == 0 or last_done) and TR.delivered(st) is not None:
            rates.append((tc, CLASS_VAL[TR.delivered(st)]))
    # deadlines inside delays: 1 ms before (the temp) and at the deadline (the schedule)
    for i, (d, st) in enumerate(delays):
        v = st["vals"]
        if "Pump.Temp" in st["locs"] and v["Pump.y"] < v["dur"] * 60:
            left = v["dur"] * 60 - v["Pump.y"]
            if left <= d:
                start = cols[i][0]
                rates.append((start + left - 0.001, CLASS_VAL[TR.RATE[v["tcls"]]]))
                if left < d:
                    rates.append((start + left, CLASS_VAL["sched"]))
    # T2 has no pre-run phase, and tempRate applies an initial temp before its start
    # (section 3). So no checkpoint before the initial temp starts, or before t0.
    first = init[0] if init else origin
    rates = [(k, v) for k, v in rates if k >= min(first, origin)]
    return cycles, sorted(rates), init, origin


def ms(t, origin):
    return T0 + round((t - origin) * 1000)


def lean_trace(name, cycles, rates, init, origin):
    lid = name.replace("-", "_")
    out = []
    if init:
        it, tcls, dur = init
        start = ms(it, origin)
        out.append(f"def env_{lid} : Env := {{ profile := prof, initTemp := some "
                   f"{{ rate := {CLASS_VAL[TR.RATE[tcls]]}, start := {start}, "
                   f"deadline := {start + dur * 60000} }} }}")
    else:
        out.append(f"def env_{lid} : Env := {{ profile := prof }}")
    steps = []
    for c in cycles:
        rc, dk, dv, uk = c["fields"]
        o = ".accepted" if c.get("accepted") else ".lost"
        steps.append(f"  {{ time := {ms(c['time'], origin)}, events := "
                     f"[cmd ({js(RATE_VAL[rc])}) ({js(dur_val(dk, dv))}) ({js(UNITS_VAL[uk])}) {o}] }}")
    out.append(f"def run_{lid} : Run Event := [\n" + ",\n".join(steps) + "]" if steps
               else f"def run_{lid} : Run Event := []")
    obs = []
    for c in cycles:
        a = c["act"]
        act = {"none": ".none", "cancel": ".cancel"}.get(a[0]) or f"(.temp ({a[1]}) {a[2]})"
        obs.append(f"  {{ time := {ms(c['time'], origin)}, accepted := {str(c['accepted']).lower()}, "
                   f"act := {act}, bolus := {str(c['bolus']).lower()} }}")
    out.append(f"def obs_{lid} : List CycleObs := [\n" + ",\n".join(obs) + "]" if obs
               else f"def obs_{lid} : List CycleObs := []")
    out.append(f"def rates_{lid} : List (Int × Rat) :=\n  ["
               + ", ".join(f"({ms(k, origin)}, {rat(v)})" for k, v in rates) + "]")
    return lid, "\n".join(out)


def main():
    rows, blocks = [], []
    for line in (HERE / "traces" / "index.md").read_text().splitlines():
        if not line.startswith("| ["):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        qid, kind, model = cells[0].split("]")[0][1:], cells[1], cells[2]
        if not model.startswith("free"):
            rows.append({"id": qid, "model": model, "result": "not replayed in U3a",
                         "why": "U1b trace: controller replay is U3b"})
            continue
        if qid == "M-missing-reject":
            rows.append({"id": qid, "model": model, "result": "not replayed",
                         "why": "deadlock is a property of the automata (section 7)"})
            continue
        steps = TR.parse((HERE / "traces" / f"{qid}.trace").read_text())
        cycles, rates, init, origin = project(steps)
        if any(not c["done"] for c in cycles):
            rows.append({"id": qid, "model": model, "result": "not replayed",
                         "why": "the trace ends inside a cycle"})
            continue
        expect = "false" if kind == "mutation" else "true"
        lid, text = lean_trace(qid, cycles, rates, init, origin)
        what = "the mutant's trace is not realized: T2 does not have its fault" if expect == "false" \
            else "the trace is realized on the T2 pump"
        blocks.append(f"/-! ### {qid}: {what} -/\n\n{text}\n\n"
                      f"theorem replay_{lid} :\n    traceMatch env_{lid} run_{lid} obs_{lid} "
                      f"rates_{lid} = {expect} := by\n  native_decide\n\n"
                      f"theorem schedule_one_{lid} :\n    rates_{lid}.all (fun (k, _) => "
                      f"env_{lid}.sched k == 1) = true := by\n  native_decide\n")
        rows.append({"id": qid, "model": model,
                     "result": "realized" if expect == "true" else "not realized (as expected)",
                     "theorem": f"LeanAID.Time.Replay.U1a.replay_{lid}",
                     "cycles": len(cycles), "checkpoints": len(rates)})
    header = '''import LeanAID.Time.Replay

/-!
# Replay of the U1a UPPAAL traces on the T2 pump

Generated by `uppaal/replay.py` from `uppaal/traces/`. Do not edit by hand.

U1a traces have free commands, which no legal controller run gives, so each trace is
replayed on the pump alone (`docs/uppaal-plan.md`, section 7, level 2): the run has
the trace's commands as results, and the theorem compares its projection with the
trace. A witness, and the counterexample of P4b-30-free, is realized
(`traceMatch ... = true`). The counterexample of a mutation is not realized
(`= false`): the T2 pump does not have the mutant's fault.

The environment has a schedule of 1 U/h (`prof`), and `schedule_one` checks it at
every checkpoint. Classes as rates: the schedule 1, zero 0, low 1/2, high 2. The
checks use `native_decide`, because `rateAt` reads the schedule with `basalLookup`,
which the kernel does not reduce (F-22). The runs are not legal runs: their results
are given, not computed by `LeanAID.step`.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time.Replay.U1a

open LeanAID LeanAID.Time LeanAID.Time.Replay

/-- A schedule of 1 U/h all day. -/
def prof : Profile := { basalprofile := [{ i := some 0, minutes := 0, rate := 1 }] }

'''
    LEAN.write_text(header + "\n".join(blocks) + "\nend LeanAID.Time.Replay.U1a\n")
    rows = main_u1b(rows)
    REPORT.write_text(json.dumps(rows, indent=1) + "\n")
    for r in rows:
        print(f"{r['id']:20} {r['result']}")




# ---------------------------------------------------------------- U3b

LEAN_U1B = ROOT / "LeanAID" / "Conformance" / "UppaalReplayU1b.lean"

# U1b traces that are not replayed as witnesses: mutations and instrumentation.
U1B_STATUS = {
    "M-P1-rejected-high": "not realizable: p1_faithful (an Increase needs a non-stale glucose status)",
    "M-P1-nan-units": "not realizable: p1_faithful (an Increase needs a non-stale glucose status)",
    "M-P1-no-hasreading": "not realizable: p1_faithful (no readings give no glucose status)",
    "M-P3-positive-120": "not realizable: p3_temp_ok (TempOk on every issued result)",
    "M-P4b-30": "not realizable: p3_temp_ok (a positive temp has duration 30)",
    "M-P5-user": "not realizable: p5_faithful with smb_spacing, under BolusSeen",
    "M-P5-user-w": "not realizable: p5_faithful with smb_spacing, under BolusSeen",
    "M-P5-clock": "not replayed: instrumentation (the clock check has no T2 counterpart)",
    "M-cgm-first": "not replayed: a fault of the model's CGM bookkeeping; T2 keeps every reading",
}


B_RATE = 3   # the maximum safe basal of `prof` and `profS`, the rate bound of R_U


def pred_of(qid, lid, pre):
    """The T2 predicate of the query of a trace, as a Lean Bool, or None."""
    base = qid[2:] if qid.startswith("R-") else qid
    env, run = f"env_{lid}", f"run_{lid}"
    pl = "[" + ", ".join(str(x) for x in pre) + "]"
    return {
        "P1-w-noread": f"noReadCycleB {env} {run}",
        "P1-w-inc": f"increaseFreshB {env} {run}",
        "P5-w-first": f"firstUnitsB {env} {run} {pl}",
        "P5-w-spaced": f"spacedUnitsB {env} {run} {pl} 183000",
        "P5-w-early": f"earlyNoUnitsB {env} {run} {pl} 183000",
        "P5-pair-w": f"decide (2 ≤ (smbTimes {env} {run}).length)",
        "P5-w-bolus": f"!(smbTimes {env} {run}).isEmpty",
        "P5-w-user-cycle": f"userBolusCycleB {run}",
        "cgm-w": f"readingStepB {run}",
        "F-20": f"f20B {env} {run} 7199000",
        # the last bolus as T2 sees it: lastBolusTime of Iob.generate at t0
        "prerun-w-t0": (f"({env}.initTemp.map (·.start) == some {T0}) && "
                        f"((iobOut {env} {env}.init {T0} none).lastBolusTime == .fin {T0 - 3600000})"),
        "prerun-w-old": (f"({env}.initTemp.any fun tp => decide (tp.start ≤ {T0 - 1700000})) && "
                         f"(match (iobOut {env} {env}.init {T0} none).lastBolusTime with "
                         f"| .fin tb => decide ({T0 - 10000} ≤ tb ∧ tb ≤ {T0}) | .nan => false)"),
    }.get(base)


def valid_act(rc, dk, dv, uk):
    """`validate` and `applyCmd` on the encoded fields: (act, bolus), as Lean values."""
    if uk in (1, 2):
        return ".none", False
    bolus = uk == 3
    if rc == 0 and dk == 0:
        return ".none", bolus
    if rc >= 3 and dk == 3 and dv == 0:
        return ".cancel", bolus
    if rc >= 3 and dk == 3 and 30 <= dv <= 120:
        return f"(.temp ({RATE_VAL[rc]}) {dv})", bolus
    return ".none", False


def u1b_steps(steps):
    """The steps of a U1b trace, the pre-run events, and the rate checkpoints."""
    t, prev = 0.0, steps[0][2]
    out, cur, init, prebolus = [], None, None, None
    for kind, data, st in steps[1:]:
        if kind == "delay":
            t += data
            prev = st
            continue
        b, a = prev["vals"], st["vals"]
        for e in data:
            if e["proc"] == "Pump" and e["sync"] == "initTemp?":
                init = (t, a["tcls"], a["dur"])
            if e["proc"] != "Step":
                continue
            sd = (e["src"], e["dst"])
            if sd == ("Pre", "Pre"):
                prebolus = t
            elif sd == ("Idle", "S1"):
                cur = {"time": t, "reading": False, "ub": False, "cycle": None}
                out.append(cur)
            elif e["sync"] == "read!":
                cur["reading"] = True
            elif e["sync"] == "ubolus!":
                cur["ub"] = True
            elif e["dst"] == "Iss":
                cur["cycle"] = {"issued": (a["rc"], a["dk"], a["dv"], a["uk"]), "obs": None}
            elif sd == ("Ch", "End"):
                cur["cycle"]["obs"] = (False, ".none", False)
            elif sd == ("Ex", "End"):
                act, _ = valid_act(*cur["cycle"]["issued"])
                bolus = a.get("bolusDone") == 1 and b.get("bolusDone") == 0
                cur["cycle"]["obs"] = (True, act, bolus)
        prev = st
    return [s for s in out if s["reading"] or s["ub"] or s["cycle"]], init, prebolus


def lean_u1b(qid, steps):
    lid = qid.replace("-", "_")
    _, _, init0, origin = project(steps)
    tsteps, init, prebolus = u1b_steps(steps)
    falling = any(s["cycle"] and s["cycle"]["issued"][0] == 3 for s in tsteps)
    prof, free = ("prof", "{}") if falling else ("profS", "smbFree")
    fields = [f"profile := {prof}"]
    if init:
        it, tcls, dur = init
        start = ms(it, origin)
        fields.append(f"initTemp := some {{ rate := {CLASS_VAL[TR.RATE[tcls]]}, start := {start}, "
                      f"deadline := {start + dur * 60000} }}")
    if prebolus is not None:
        fields.append(f"initHistory := encodeAction (.bolus {ms(prebolus, origin)} 1 false)")
    lines = [f"def env_{lid} : Env := {{ " + ", ".join(fields) + " }"]
    script, obs, nread = [], [], 0
    for s in tsteps:
        tm = ms(s["time"], origin)
        envs = []
        if s["reading"]:
            v = 80 - 10 * nread if falling else 150 + 20 * nread
            nread += 1
            envs.append(f"rdAt {tm} {v}")
        if s["ub"]:
            envs.append(".userBolus 1")
        cyc = "none"
        if s["cycle"]:
            o = s["cycle"]["obs"]
            cyc = f"some ({free}, {'.lost' if o and not o[0] else '.accepted'})"
        script.append(f"  {{ time := {tm}, env := [{', '.join(envs)}], cycle := {cyc} }}")
        c = "none"
        if s["cycle"]:
            rc, dk, dv, uk = s["cycle"]["issued"]
            o = s["cycle"]["obs"]
            ob = "none" if o is None else (f"some {{ time := {tm}, accepted := {str(o[0]).lower()}, "
                                            f"act := {o[1]}, bolus := {str(o[2]).lower()} }}")
            c = f"some ({{ rc := {rc}, dk := {dk}, dv := {dv}, uk := {uk} }}, {ob})"
        obs.append(f"  {{ time := {tm}, reading := {str(s['reading']).lower()}, "
                   f"userBolus := {str(s['ub']).lower()}, cycle := {c} }}")
    lines.append(f"def script_{lid} : List ScriptStep := [\n" + ",\n".join(script) + "]" if script
                 else f"def script_{lid} : List ScriptStep := []")
    lines.append(f"def run_{lid} : Run Event := build env_{lid} env_{lid}.init script_{lid}")
    lines.append(f"def obs_{lid} : List StepObs := [\n" + ",\n".join(obs) + "]" if obs
                 else f"def obs_{lid} : List StepObs := []")
    has_pump = any(l.startswith("Pump.") for l in steps[0][2]["locs"])
    rates = [] if not has_pump else project(steps)[1]
    lines.append(f"def rates_{lid} : List (Int × Rat) :=\n  ["
                 + ", ".join(f"({ms(k, origin)}, {rat(v)})" for k, v in rates) + "]")
    lines.append(f"theorem legal_{lid} : Legal env_{lid} run_{lid} :=\n"
                 f"  build_legal env_{lid} script_{lid} (by decide)")
    lines.append(f"theorem replay_{lid} :\n    traceMatchU1b env_{lid} run_{lid} obs_{lid} rates_{lid} = true := by\n"
                 f"  native_decide")
    pre = [ms(prebolus, origin)] if prebolus is not None else []
    pl = "[" + ", ".join(str(x) for x in pre) + "]"
    lines.insert(len(lines) - 2, f"def pre_{lid} : List Int := {pl}")
    lines.append(f"theorem inRU_{lid} :\n    ruB env_{lid} run_{lid} {T0} {B_RATE} pre_{lid} = true := by\n  native_decide")
    lines.append(f"theorem ru_{lid} : RU env_{lid} run_{lid} {T0} {B_RATE} :=\n"
                 f"  ru_of (e := {{ i := some 0, minutes := 0, rate := 1 }}) rfl inRU_{lid}")
    pred = pred_of(qid, lid, pre)
    if pred:
        lines.append(f"theorem pred_{lid} :\n    ({pred}) = true := by\n  native_decide")
    check = (f"traceMatchU1b env_{lid} run_{lid} obs_{lid} rates_{lid}, "
             f"ruB env_{lid} run_{lid} {T0} {B_RATE} pre_{lid}, " + (f"({pred})" if pred else "true"))
    return lid, "\n".join(lines), len(tsteps), len(rates), check


def evaluate(cands):
    """Run Lean on the candidate replays and return {lid: (matches, first differing step)}."""
    import subprocess
    tmp = pathlib.Path("/tmp/leanaid-u3b-eval.lean")
    # the evaluation file holds the definitions only; the theorems come after them
    body = "\n\n".join(text.split("\ntheorem ")[0] for _, text, _ in cands)
    evals = "\n".join(
        f'#eval (\"{lid}\", {check}, '
        f'(List.zip (run_{lid}.map (stepObs env_{lid})) obs_{lid}).findIdx? (fun (a, b) => !stepMatch a b), '
        f'run_{lid}.length, obs_{lid}.length)' for lid, _, check in cands)
    tmp.write_text(HEADER + body + "\n\n" + evals + "\n\nend LeanAID.Time.Replay.U1b\n")
    p = subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=16G", "-p",
                        "MemorySwapMax=0", "lake", "env", "lean", str(tmp)],
                       cwd=ROOT, capture_output=True, text=True, timeout=3000)
    out = {}
    for line in p.stdout.splitlines():
        m = __import__("re").match(
            r'\("(\w+)", (true|false), (true|false), (true|false), (none|some \d+), (\d+), (\d+)\)', line)
        if m:
            out[m[1]] = (m[2] == "true", m[3] == "true", m[4] == "true", m[5], m[6], m[7])
    if p.returncode != 0 or len(out) != len(cands):
        raise SystemExit("Lean evaluation failed:\n" + p.stdout[-3000:] + p.stderr[-3000:])
    return out


def main_u1b(rows):
    """Replace the U1b rows of `rows` and write the U1b Lean file."""
    import check as C
    kinds = {q[0]: q[2] for q in C.ALL}
    u3b = [q[0] for q in C.QUERIES_U3B]
    ids = [r["id"] for r in rows if r["result"].startswith("not replayed in U3a")]
    ids += [q for q in u3b if q not in ids]
    cands, info = [], {}
    for qid in ids:
        if qid != "M-P5-clock" and (qid in U1B_STATUS or kinds.get(qid) != "witness"):
            continue
        if not (HERE / "traces" / f"{qid}.trace").exists():
            continue
        steps = TR.parse((HERE / "traces" / f"{qid}.trace").read_text())
        lid, text, nst, nr, check = lean_u1b(qid, steps)
        cands.append((lid, text, check))
        info[qid] = (lid, text, nst, nr)
    ev = evaluate(cands)
    blocks, out = [], [r for r in rows if not r["result"].startswith("not replayed in U3a")]
    for qid in ids:
        model = next((r["model"] for r in rows if r["id"] == qid), "")
        if qid in U1B_STATUS and qid != "M-P5-clock":
            out.append({"id": qid, "model": model, "result": U1B_STATUS[qid]})
            continue
        if qid not in info:
            out.append({"id": qid, "model": model, "result": "no trace"})
            continue
        lid, text, nst, nr = info[qid]
        proj, ru, pr, diff, n2, nt = ev[lid]
        ok = proj and ru and pr
        if ok and qid == "M-P5-clock":
            blocks.append(f"/-! ### {qid}: the observable part -/\n\n{text}\n")
            out.append({"id": qid, "model": model,
                        "result": "observable part realized; the clock fault has no T2 counterpart",
                        "theorem": f"LeanAID.Time.Replay.U1b.replay_{lid}"})
            continue
        if ok:
            blocks.append(f"/-! ### {qid} -/\n\n{text}\n")
            out.append({"id": qid, "model": model, "result": "realized",
                        "theorem": f"LeanAID.Time.Replay.U1b.replay_{lid}", "steps": nst,
                        "checkpoints": nr})
        else:
            alt = f"R-{qid}" if f"R-{qid}" in u3b else None
            why = ("the run is not in R_U (ruB fails)" if proj and not ru
                   else "the T2 predicate of the query fails" if proj and not pr
                   else f"T2 has {n2} steps, the trace {nt}" if n2 != nt
                   else f"T2 differs from the trace at step {diff.split()[-1]}" if diff != "none"
                   else "T2 differs at a rate checkpoint")
            out.append({"id": qid, "model": model,
                        "result": "unresolved: with the replay inputs, " + why
                        + (f"; {alt} is the realizable witness" if alt else "")})
    LEAN_U1B.write_text(HEADER + "\n".join(blocks) + "\nend LeanAID.Time.Replay.U1b\n")
    import subprocess
    b = subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=16G", "-p",
                        "MemorySwapMax=0", "lake", "build", "LeanAID.Conformance.UppaalReplayU1b"],
                       cwd=ROOT, capture_output=True, text=True, timeout=3000)
    if b.returncode != 0:
        raise SystemExit("the generated U1b replay does not build:\n" + b.stdout[-3000:])
    return out


HEADER = '''import LeanAID.Time.ReplayU1b
import LeanAID.Conformance.TimeRuns

/-!
# Replay of the U1b UPPAAL traces on legal T2 runs

Generated by `uppaal/replay.py` from `uppaal/traces/`. Do not edit by hand.

Each run is built by `build` from a script at the times of the trace, so it is legal
(`legal_*`) and `LeanAID.step` computes every issued output. Readings rise from
150 mg/dL by 20 (with `profS`, microboluses on) or fall from 80 mg/dL by 10 (with
`prof`) when the trace issues a zero temp. User boluses are 1 U. `replay_*` checks that
the projection of the run equals the trace: per step its reading, its positive user
bolus, the issued classes (`Issued`), the execution, and the delivered rate at the
checkpoints when the model has a pump. `ru_*` gives the conditions of R_U (`RU`):
`ValidRun`, a valid profile and a positive constant schedule at every time, the rate
cap B = 3 U/h, `InvTemp` and `InvRate` of the initial state, an initial temp that starts
at or before t0 with a rate >= 0, and steps at or after t0; `inRU_*` also checks
BolusSeen (with the boluses of the initial history), dated readings at positive times
at least 150 s apart with values above 38, and an SMB interval of 3 minutes.
`pred_*` checks the T2 predicate of the trace's query.

The checks use `native_decide`, because `Iob.generate` and `basalLookup` do not
reduce in the kernel (F-22).

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time.Replay.U1b

open LeanAID LeanAID.Time LeanAID.Time.Replay LeanAID.Time.Runs

'''


if __name__ == "__main__":
    sys.exit(main())
