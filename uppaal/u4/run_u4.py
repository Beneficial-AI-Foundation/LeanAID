"""Work item U4: run the queries of uppaal/check.py in Munta and write
uppaal/u4/results.json.

For each query of `check.ALL`, the script decides whether Munta can check it. A query
with a clock (or a clock difference) is `unsupported`, because Munta crashes on a
clock in a formula (uppaal/u0b/README.md, input limit 1). For the other queries:

  1. It builds the model variant of the query, as check.py does.
  2. It lowers the model for Munta (`munta.lower`) and removes the observer
     variables and clocks that the query does not read (`BUNDLES`), as far as
     `munta.drop_names` accepts the removal. Each step of `lower` is argued to keep
     the answers under conditions that it checks (see munta.py); this is not proved. On the lowered network, a formula `A[] p` becomes
     `A[] (Step.Init || p)` and `E<> p` becomes `E<> (!(Step.Init) && p)`, because
     the integers have their start values only after the edge from `Step.Init`.
  3. It runs UPPAAL on the lowered network with the query. The answer must be the
     expected status of check.py. This tests the lowering on each query.
  4. It runs the three gates of U0b on the lowered network: the UPPAAL deadlock
     check, the Munta deadlock check, and UPPAAL `E<> false` without an error. A
     Munta answer counts only if all three pass.
  5. It runs Munta on the same network.

Every model checker runs under `systemd-run --user --scope -p MemoryMax=16G -p
MemorySwapMax=0` with a timeout. Munta statuses: holds, fails, reachable,
unreachable, out of memory (killed at the cap), timeout, reject (Munta printed no
result), crash, unsupported.

The script exits with 1 if a status differs from its expected status: the UPPAAL
answer on the lowered network must be the status of check.py, and the Munta
outcome must be that status too, or the outcome in `EXPECT_MUNTA`. A Munta
answer must also pass the three gates, unless `EXPECT_MUNTA` names the query.

With `--u5b` (work item U5b), the script runs only the queries on a model with a
Pump that Munta can check, lowers them with `reduce_pump` (`munta.few_durations`:
the pump has the durations 30 and 120 only), and writes u4/results-u5b.json. The
reduced network is a restriction of the U1a network. `transfer` says for each
answer whether it carries over to the U1a network, and why. Only an answer that
transfers counts for the U1a pump. `EXPECT_MUNTA_U5B` holds the expected outcomes
that differ from check.py.

`--rescore` applies a changed `EXPECT_MUNTA` to results.json and runs nothing. With
`--u5b`, it also recomputes the transfer of each answer.
`--check-networks` rebuilds every network that results.json records and compares
the sha256 sums; it runs only the order printer. If all are equal, it records the
current generator sums, so the old answers stay valid for the current code.

Usage: python3 -I uppaal/u4/run_u4.py --verifyta PATH --munta PATH --order PATH [--only ID ...]
       [--u5b] [--rescore | --check-networks]
(`--order` is the diagnostic checker of uppaal/munta_order.sh.)
"""

import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import time

HERE = pathlib.Path(__file__).resolve().parent
UP = HERE.parent
sys.path.insert(0, str(UP))
import check as C  # noqa: E402
import model as M  # noqa: E402
import munta as MU  # noqa: E402

OUT = HERE / "out"
TIMEOUT = 1800
CAP = MU.CAP

# Observer variables and clocks, in groups that are removed together. A group is
# removed if the query reads none of its names and `drop_names` accepts the removal
# together with the groups removed before it.
BUNDLES = [
    ("P1 observer", ("err1",)),
    ("P3 observer", ("err3",)),
    ("P5 observer", ("err5", "prior", "p5c")),
    ("P5-pair observer", ("errPair", "mb1", "pb")),
    ("reading observer", ("rdSeen", "rdc", "errRead")),
    ("bolus observer", ("expB", "bolusDone")),
    ("P4a observer", ("oCls", "oDur", "o4")),
    ("close clock", ("obs",)),
    ("pump class and duration", ("tcls", "dur")),
    ("witness wOdd", ("wOdd",)),
    ("witness nRead", ("nRead",)),
    ("witness mb2", ("mb2",)),
    ("witness wUb", ("wUb",)),
    ("witness f20", ("f20",)),
    ("witness wColl", ("wColl",)),
    ("witness wCancel", ("wCancel",)),
    ("witness wRejBolus", ("wRejBolus",)),
    ("witness wNoSteps", ("wNoSteps",)),
]

# Munta outcomes other than the expected status of check.py, with the reason.
PUMP_TIMEOUT = ("timeout", "the free pump networks have about 11,500 Pump edges (one Temp location per "
                "duration); Munta reaches its model checker (last line 'Running precond_mc') and does not "
                "finish in 1800 s (U4 run of 2026-11-20)")
EXPECT_MUNTA = {"P4a-w-cancel": PUMP_TIMEOUT, "deadlock": PUMP_TIMEOUT, "M-missing-reject": PUMP_TIMEOUT}
# U5b: the same for the reduced pump (`--u5b`)
EXPECT_MUNTA_U5B = {
    "M-missing-reject": ("fails", "Munta finds the deadlock of the mutant, as UPPAAL does, but the UPPAAL "
                         "and the Munta deadlock gates fail by design, because the mutant deadlocks. "
                         "So the answer agrees and does not count (U0b gate rule)"),
}


def pump_written(m):
    """The names that the Pump template writes, and its local clocks."""
    out = set()
    for t in m.templates:
        if t.name == "Pump":
            out |= set(MU.parse_decls([t.decl])[1]) if t.decl else set()
            out |= {u.partition(" = ")[0].strip() for e in t.edges for u in MU.updates(e.update)}
    return out


def transfer(m, query, status):
    """Does a Munta answer on the reduced network (`few_durations`) carry over to the
    U1a network? Returns (transfers, how).

    The reduced network is a restriction: every run of it is a run of the U1a network
    (see `munta.few_durations`). So a reachable witness and a counterexample of an
    `A[] p` query transfer directly.

    A deadlock (`A[] (!deadlock)` fails) needs more, because the U1a network has more
    edges, which could leave the deadlock state. The removed edges are the select
    edges with the other values of the duration variable. Checked here: the source
    location of each such edge has an edge without guard, sync and select to a
    location without invariant. So that location is never a deadlock, and a deadlock
    state of the reduced network has no extra edge in the U1a network.

    A result that holds, or an unreachable one, transfers only by an argument, and
    only under conditions checked here. Let D be the names that the pump writes (with
    its clock) and the names that an update copies from the duration variable (such
    as `oDur = dv`). The query must read no name in D and no pump location, and no
    other template may read a name in D in a guard, an invariant or the right side of
    an update. The argument, not checked: a U1a run maps to a reduced run with the
    same Step edges and delays, where each issued duration is replaced by the kept
    value of its class (-1, 0, 1, 30, 120 or 121). The guards and the query treat the
    two values alike (the classes come from all their atoms on the duration
    variable, and from the atoms and bounds of each select variable copied into it),
    and nothing outside D depends on the value itself. The reduced pump
    takes part in every synchronization, because it has a receiving edge for every
    value of its guards in each location where a sender can send, and it never blocks
    time, because its expiry edge releases the invariant of Temp_d. This is the
    argument of the `nopump` variant (check.py, MODEL_RELATION). The same holds from
    reduced runs to U1a runs. For the deadlock query: a state is a deadlock in either
    network exactly when Step is in a committed location with no enabled edge,
    because Step can always leave Pre and Idle after a delay and Closed has a
    self-loop. That is a property of Step and its data, so the two networks have the
    same deadlock answer."""
    ints, _, _ = MU.parse_decls(m.decl)
    x = MU.duration_var(m, ints)
    deadlock = query == "A[] (!deadlock)"
    if status == "fails" and deadlock:
        for t in m.templates:
            for e in t.edges:
                sel = set(re.findall(r"(\w+) : int", e.select or ""))
                if not any(u.partition(" = ")[0].strip() == x and u.partition(" = ")[2].strip() in sel
                           for u in MU.updates(e.update)):
                    continue
                exits = [f for f in t.edges if f.src == e.src and not f.guard and not f.sync and not f.select
                         and not next(l for l in t.locs if l.name == f.dst).inv]
                if not exits:
                    return False, (f"{t.name}.{e.src} has a removed select edge and no edge without guard, "
                                   "so a deadlock of the reduced network need not be one of the U1a network")
        return True, ("restriction: the deadlock state of the reduced network is reachable in the U1a "
                      "network, and the only extra edges there leave a location that always has an edge "
                      "without guard (run_u4.transfer)")
    if status in ("reachable", "fails"):
        return True, ("restriction: the witness or counterexample of the reduced network is a run of "
                      "the U1a network (munta.few_durations)")
    if status not in ("holds", "unreachable"):
        return False, f"no answer ({status})"
    dep = pump_written(m) | {u.partition(" = ")[0].strip() for t in m.templates for e in t.edges
                             for u in MU.updates(e.update)
                             if re.search(rf"\b{x}\b", u.partition(" = ")[2]) and t.name != "Pump"}
    if not deadlock and (MU.names_in(query) & dep or re.search(r"\bPump\.", query)):
        return False, (f"the query reads the pump or a copy of {x}, so only the restriction argument "
                       f"applies, and a {status} result does not transfer by it")
    readers = sorted({t.name for t in m.templates if t.name != "Pump"
                      for x_ in [e.guard for e in t.edges] + [l.inv for l in t.locs]
                      + [u.partition(" = ")[2] for e in t.edges for u in MU.updates(e.update)]
                      if MU.names_in(x_ or "") & dep})
    if readers:
        return False, f"{', '.join(readers)} reads a name that the pump writes or that copies {x}"
    return True, ("argument, not checked: the pump does not affect Step, and the guards and the query "
                  "treat each issued duration like the kept value of its class (run_u4.transfer)")


def sha256(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def clocks_of(m):
    _, clocks, _ = MU.parse_decls(m.decl)
    for t in m.templates:
        if t.decl:
            clocks += MU.parse_decls([t.decl])[1]
    return clocks


def unsupported(m, query):
    names = MU.names_in(query)
    used = sorted(set(clocks_of(m)) & (names | {n.split(".")[1] for n in re.findall(r"\w+\.\w+", query)}))
    if used and re.search(r"\w+\s*-\s*\w+", query):
        return f"a clock difference in the query ({', '.join(used)}): Munta has no clock differences"
    if used:
        return f"a clock in the query ({', '.join(used)}): Munta crashes on a clock in a formula (U0b limit 1)"
    return ""


def choose_drop(m, formula, reduce_pump=False):
    """The groups of BUNDLES to remove, and the reasons for the groups kept."""
    names = MU.names_in(formula)
    ints, clocks, _ = MU.parse_decls(m.decl)
    declared = set(ints) | set(clocks_of(m))
    drop, kept = [], {}
    for label, group in BUNDLES:
        present = [n for n in group if n in declared]
        if not present:
            continue
        if set(present) & names:
            kept[label] = "read by the query"
            continue
        try:
            MU.lower(m, formula, drop + present, reduce_pump=reduce_pump)
        except ValueError as e:
            kept[label] = str(e)
            continue
        drop += present
    return drop, kept


def lowered_formula(formula, low):
    if formula == "A[] (!deadlock)":
        return formula
    if not any(l.name == "Init" for t in low.templates if t.name == "Step" for l in t.locs):
        return formula
    body = formula[4:].strip()
    if MU.strip_parens(body) == body:       # not one parenthesized expression
        body = f"({body})"
    if formula.startswith("A[]"):
        return f"A[] (Step.Init || {body})"
    if formula.startswith("E<>"):
        return f"E<> (!(Step.Init) && {body})"
    raise ValueError(f"query form not handled: {formula}")


def run_capped(cmd, timeout):
    """Run under the memory cap; returns (exit code, output, seconds, peak kB)."""
    with tempfile.NamedTemporaryFile("r", suffix=".time") as tf:
        full = CAP + ["timeout", str(timeout), "/usr/bin/time", "-f", "%M", "-o", tf.name] + cmd
        t0 = time.monotonic()
        p = subprocess.run(full, capture_output=True, text=True)
        secs = time.monotonic() - t0
        tf.seek(0)
        tl = [l for l in tf.read().split() if l.isdigit()]
    return p.returncode, p.stdout + p.stderr, secs, int(tl[-1]) if tl else None


def killed(code, out):
    lines = {l.strip() for l in out.splitlines()}
    return code in (137, -9) or "Killed" in lines or "Command terminated by signal 9" in lines


def uppaal(verifyta, xml, query):
    qfile = xml.with_suffix(f".{hashlib.sha256(query.encode()).hexdigest()[:10]}.q")
    qfile.write_text(query + "\n")
    code, out, secs, kb = run_capped([verifyta, "-q", str(xml), str(qfile)], TIMEOUT)
    sat, unsat = out.count("Formula is satisfied."), out.count("Formula is NOT satisfied.")
    if code == 124:
        return "timeout", secs, out
    if killed(code, out):
        return "out of memory", secs, out
    if code != 0 or sat + unsat != 1 or "[error]" in out:
        return "error", secs, out
    return C.status(query, sat == 1), secs, out


MUNTA_LINES = {"Property is satisfied!": True, "Property is not satisfied!": False,
               "Model has no deadlock!": True, "Model has a deadlock!": False}


def munta(munta_bin, path, deadlock, query):
    code, out, secs, kb = run_capped([munta_bin, "-m", str(path)] + (["-deadlock"] if deadlock else []),
                                     TIMEOUT)
    lines = [l.strip() for l in out.splitlines() if l.strip()]
    res = [l for l in lines if l in MUNTA_LINES]
    explored = next((int(l.split(":")[1]) for l in lines if l.startswith("# explored states:")), None)
    if code == 124:
        st = "timeout"
    elif killed(code, out):
        st = "out of memory"
    elif code != 0:
        st = "crash"
    elif len(res) == 1 and "Failure:" not in lines and deadlock == ("deadlock" in res[0]):
        st = C.status(query, MUNTA_LINES[res[0]])
    else:
        st = "reject"
    return {"status": st, "seconds": round(secs, 2), "peak_kb": kb, "explored": explored,
            "last_line": lines[-1][:300] if lines else ""}


def build_network(args, m, qid, variant, muts, wit, query, deadlock):
    """Lower the network of one query and write it for UPPAAL and for Munta."""
    drop, kept = choose_drop(m, query, args.u5b)
    low = MU.lower(m, query, drop, reduce_pump=args.u5b)
    uq = lowered_formula(query, low)
    name = ("u5b." if args.u5b else "") + variant + "".join("." + x for x in muts) + \
        (".witness" if wit else "") + "." + qid
    xml, mx = OUT / f"{name}.xml", OUT / f"{name}.muntax"
    M.write_uppaal(low, xml)
    mq = "E<> Step.Pre" if deadlock else MU.munta_formula(uq)
    order = MU.munta_order(args.order, low, mq, mx)
    MU.write_munta(low, mq, mx, order)
    return drop, kept, low, uq, xml, mx, mq, order


def rescore(u5b=False):
    path = HERE / RESULTS[u5b]
    expect_munta = EXPECT_MUNTA_U5B if u5b else EXPECT_MUNTA
    report = json.loads(path.read_text())
    bad = 0
    for r in report["results"]:
        if "munta_expected" not in r:       # unsupported or not run
            r["ok"] = r.get("uppaal_main") == r["expected"]
            bad += not r["ok"]
            continue
        exp_m, why = expect_munta.get(r["id"], (r["expected"], ""))
        r["munta_expected"] = exp_m
        r.pop("munta_expected_reason", None)
        if why:
            r["munta_expected_reason"] = why
        r["ok"] = (r["uppaal_lowered"] == r["expected"] and r.get("uppaal_main") == r["expected"]
                   and r["munta"] == exp_m
                   and (r["munta_counts"] or r["id"] in expect_munta))
        if u5b:     # the transfer depends only on the model, the query and the Munta status
            m = C.build(r["model_variant"], tuple(r["mutations"]), r["kind"] == "witness")
            tr, how = transfer(m, r["query"], r["munta"])
            r.update({"transfers_to_u1a": tr, "transfer": how, "counts_for_u1a": r["munta_counts"] and tr})
        bad += not r["ok"]
    report["rescored_by_runner_sha256"] = sha256(__file__)
    path.write_text(json.dumps(report, indent=1) + "\n")
    print(f"{len(report['results'])} queries rescored; {bad} not as expected")
    return 1 if bad else 0


RESULTS = {False: "results.json", True: "results-u5b.json"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verifyta", required=True)
    ap.add_argument("--munta", required=True)
    ap.add_argument("--order", required=True, help="the diagnostic checker of munta_order.sh")
    ap.add_argument("--only", nargs="+", metavar="ID")
    ap.add_argument("--rescore", action="store_true",
                    help="recompute the ok fields of results.json from EXPECT_MUNTA, run nothing")
    ap.add_argument("--check-networks", action="store_true",
                    help="rebuild each network and compare its sha256 with results.json, run no checker")
    ap.add_argument("--u5b", action="store_true",
                    help="U5b: only the pump queries, on the reduced pump; writes results-u5b.json")
    args = ap.parse_args()
    if args.rescore:
        return rescore(args.u5b)
    if args.check_networks and args.only:
        ap.error("--check-networks checks every recorded network; it does not take --only")
    if args.only:
        unknown = sorted(set(args.only) - {q[0] for q in C.ALL})
        if unknown:
            ap.error(f"unknown query IDs: {' '.join(unknown)}")
    OUT.mkdir(exist_ok=True)
    main_results = {r["id"]: r for r in json.loads((UP / "results.json").read_text())["results"]}
    out_path = HERE / RESULTS[args.u5b]
    expect_munta = EXPECT_MUNTA_U5B if args.u5b else EXPECT_MUNTA
    old_report = json.loads(out_path.read_text()) if args.check_networks else {}
    old_results = {r["id"]: r for r in old_report.get("results", [])}
    checked = set()
    gates = {}
    pump_limit = None     # the first pump query whose Munta run ended without a result
    results, bad = [], 0
    for (qid, item, kind, variant, muts, query, expected, about, search) in C.ALL:
        if args.only and qid not in args.only:
            continue
        wit = kind == "witness"
        m = C.build(variant, muts, wit)
        r = {"id": qid, "item": item, "kind": kind, "model_variant": variant,
             "mutations": list(muts), "query": query, "expected": expected,
             "uppaal_main": main_results.get(qid, {}).get("status"),
             "relation": C.relation(variant, kind, muts)}
        why = unsupported(m, query)
        has_pump = any(t.name == "Pump" for t in m.templates)
        if args.u5b and (why or not has_pump):
            continue
        if why:
            r.update({"munta": "unsupported", "reason": why, "ok": r["uppaal_main"] == expected})
            bad += not r["ok"]
            results.append(r)
            print(f"ok  {qid:18} unsupported: {why[:70]}")
            continue
        deadlock = query == "A[] (!deadlock)"
        if args.check_networks and old_results.get(qid, {}).get("munta") == "not run":
            continue
        if has_pump and pump_limit and not deadlock and not args.u5b:
            r.update({"munta": "not run", "ok": r["uppaal_main"] == expected,
                      "reason": f"not run to save time: Munta ended without a result on the pump "
                                f"network of {pump_limit}, and this network also has a Pump template with "
                                f"one Temp location per duration. A choice, not a measurement"})
            bad += not r["ok"]
            results.append(r)
            print(f"ok  {qid:18} not run (pump limit from {pump_limit})")
            continue
        drop, kept, low, uq, xml, mx, mq, order = build_network(args, m, qid, variant, muts, wit,
                                                                query, deadlock)
        if args.check_networks:
            old_r = old_results.get(qid, {})
            same = (old_r.get("xml_sha256") == sha256(xml) and old_r.get("muntax_sha256") == sha256(mx))
            checked.add(qid)
            bad += not same
            print(f"{'same' if same else 'DIFF'} {qid}", flush=True)
            continue
        u_st, u_secs, u_out = uppaal(args.verifyta, xml, uq)
        key = sha256(xml) + sha256(mx)
        if key not in gates:
            g_u, _, _ = uppaal(args.verifyta, xml, "A[] (!deadlock)")
            g_e, _, _ = uppaal(args.verifyta, xml, "E<> false")
            g_m = munta(args.munta, mx, True, "A[] (!deadlock)")
            gates[key] = {"uppaal_deadlock_free": g_u == "holds",
                          "munta_deadlock_free": g_m["status"] == "holds",
                          "munta_deadlock_status": g_m["status"],
                          "uppaal_exhaustive_no_error": g_e == "unreachable"}
            gates[key + ".munta"] = g_m
        g = gates[key]
        # the deadlock query is the Munta deadlock gate itself
        mres = gates[key + ".munta"] if deadlock else munta(args.munta, mx, deadlock, query)
        counts = mres["status"] in ("holds", "fails", "reachable", "unreachable") and all(
            g[k] for k in ("uppaal_deadlock_free", "munta_deadlock_free", "uppaal_exhaustive_no_error"))
        exp_m, exp_why = expect_munta.get(qid, (expected, ""))
        # an answer must also pass the gates, unless EXPECT_MUNTA names another outcome
        ok = (u_st == expected and r["uppaal_main"] == expected and mres["status"] == exp_m
              and (counts or qid in expect_munta))
        if args.u5b:
            tr, how = transfer(m, query, mres["status"])
            r.update({"transfers_to_u1a": tr, "transfer": how, "counts_for_u1a": counts and tr,
                      "relation": "the U1a network with the issued durations reduced by "
                                  "munta.few_durations (pump durations 30 and 120 only), a restriction "
                                  "of the U1a network. " + r["relation"]})
        bad += not ok
        if has_pump and mres["status"] in ("timeout", "out of memory") and not pump_limit:
            pump_limit = qid
        sizes = {t.name: {"locations": len(t.locs), "edges": len(t.edges)} for t in low.templates}
        r.update({"munta": mres["status"], "munta_counts": counts, "munta_expected": exp_m,
                  **({"munta_expected_reason": exp_why} if exp_why else {}),
                  "munta_seconds": mres["seconds"], "munta_peak_kb": mres["peak_kb"],
                  "munta_explored_states": mres["explored"], "munta_last_line": mres["last_line"],
                  "uppaal_lowered": u_st, "uppaal_lowered_seconds": round(u_secs, 2),
                  "uppaal_lowered_message": "" if u_st in ("holds", "fails", "reachable", "unreachable")
                  else u_out.strip()[-300:],
                  "gates": g, "lowered_query_uppaal": uq,
                  "munta_query": ("(-deadlock flag) " if deadlock else "") + mq,
                  "dropped": drop, "kept_groups": kept, "network_size": sizes,
                  "munta_var_order": order,
                  "xml": xml.name, "xml_sha256": sha256(xml),
                  "muntax": mx.name, "muntax_sha256": sha256(mx), "ok": ok})
        results.append(r)
        print(f"{'ok ' if ok else 'BAD'} {qid:18} munta={mres['status']:12} uppaal={u_st:11} "
              f"counts={counts} gates={[g[k] for k in sorted(g) if k != 'munta_deadlock_status']} "
              f"({mres['seconds']} s, {mres['peak_kb']} kB)", flush=True)
    if args.check_networks:
        recorded = {i for i, r in old_results.items() if r.get("xml_sha256")}
        missing = sorted(recorded - checked)
        if missing:
            print(f"recorded networks not rebuilt: {' '.join(missing)}")
            bad += len(missing)
        if not bad:
            old_report["generator_sha256"] = {f: sha256(UP / f) for f in ("model.py", "check.py", "munta.py")}
            old_report["networks_checked_by_runner_sha256"] = sha256(__file__)
            out_path.write_text(json.dumps(old_report, indent=1) + "\n")
        print(f"networks: {bad} differ from {out_path.name}")
        return 1 if bad else 0
    rev = subprocess.run(["git", "-C", str(HERE), "rev-parse", "HEAD"], capture_output=True,
                         text=True).stdout.strip()
    dirty = bool(subprocess.run(["git", "-C", str(HERE), "status", "--porcelain",
                                 "--untracked-files=no", ":/"], capture_output=True, text=True).stdout
                 or subprocess.run(["git", "-C", str(UP), "status", "--porcelain", "--", "."],
                                   capture_output=True, text=True).stdout)
    report = {
        "revision": rev, "dirty": dirty,
        "uppaal": subprocess.run([args.verifyta, "--version"], capture_output=True,
                                 text=True).stdout.splitlines()[0],
        "munta": "commit 62cb1a4a4dbcfcf62c365e90faba15b0012d5a12, built by uppaal/u0b/setup_munta.sh",
        "munta_binary_sha256": sha256(pathlib.Path(args.munta).resolve().parent / "munta"),
        "timeout_seconds": TIMEOUT, "memory_cap": "MemoryMax=16G, MemorySwapMax=0",
        "generator_sha256": {f: sha256(UP / f) for f in ("model.py", "check.py", "munta.py")},
        "runner_sha256": sha256(__file__),
        "results": results,
    }
    if args.u5b:
        report["reduction"] = ("munta.few_durations: the issued duration dv takes one value per class of "
                               "its atoms plus 120 (-1, 0, 1, 30, 120, 121), so the pump has the "
                               "durations 30 and 120; pump_per_duration makes Temp_d only for them")
    if not args.only:
        out_path.write_text(json.dumps(report, indent=1) + "\n")
    n = {s: sum(1 for r in results if r["munta"] == s) for s in sorted({r["munta"] for r in results})}
    print(f"{len(results)} queries: {n}; {bad} not as expected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
