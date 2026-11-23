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

`--rescore` applies a changed `EXPECT_MUNTA` to results.json and runs nothing.
`--check-networks` rebuilds every network that results.json records and compares
the sha256 sums; it runs only the order printer. If all are equal, it records the
current generator sums, so the old answers stay valid for the current code.

Usage: python3 -I uppaal/u4/run_u4.py --verifyta PATH --munta PATH --order PATH [--only ID ...]
       [--rescore | --check-networks]
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


def choose_drop(m, formula):
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
            MU.lower(m, formula, drop + present)
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
    drop, kept = choose_drop(m, query)
    low = MU.lower(m, query, drop)
    uq = lowered_formula(query, low)
    name = variant + "".join("." + x for x in muts) + (".witness" if wit else "") + "." + qid
    xml, mx = OUT / f"{name}.xml", OUT / f"{name}.muntax"
    M.write_uppaal(low, xml)
    mq = "E<> Step.Pre" if deadlock else MU.munta_formula(uq)
    order = MU.munta_order(args.order, low, mq, mx)
    MU.write_munta(low, mq, mx, order)
    return drop, kept, low, uq, xml, mx, mq, order


def rescore():
    path = HERE / "results.json"
    report = json.loads(path.read_text())
    bad = 0
    for r in report["results"]:
        if "munta_expected" not in r:       # unsupported or not run
            r["ok"] = r.get("uppaal_main") == r["expected"]
            bad += not r["ok"]
            continue
        exp_m, why = EXPECT_MUNTA.get(r["id"], (r["expected"], ""))
        r["munta_expected"] = exp_m
        if why:
            r["munta_expected_reason"] = why
        r["ok"] = (r["uppaal_lowered"] == r["expected"] and r.get("uppaal_main") == r["expected"]
                   and r["munta"] == exp_m
                   and (r["munta_counts"] or r["id"] in EXPECT_MUNTA))
        bad += not r["ok"]
    report["rescored_by_runner_sha256"] = sha256(__file__)
    path.write_text(json.dumps(report, indent=1) + "\n")
    print(f"{len(report['results'])} queries rescored; {bad} not as expected")
    return 1 if bad else 0


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
    args = ap.parse_args()
    if args.rescore:
        return rescore()
    if args.check_networks and args.only:
        ap.error("--check-networks checks every recorded network; it does not take --only")
    if args.only:
        unknown = sorted(set(args.only) - {q[0] for q in C.ALL})
        if unknown:
            ap.error(f"unknown query IDs: {' '.join(unknown)}")
    OUT.mkdir(exist_ok=True)
    main_results = {r["id"]: r for r in json.loads((UP / "results.json").read_text())["results"]}
    old_report = json.loads((HERE / "results.json").read_text()) if args.check_networks else {}
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
        if why:
            r.update({"munta": "unsupported", "reason": why, "ok": r["uppaal_main"] == expected})
            bad += not r["ok"]
            results.append(r)
            print(f"ok  {qid:18} unsupported: {why[:70]}")
            continue
        deadlock = query == "A[] (!deadlock)"
        if args.check_networks and old_results.get(qid, {}).get("munta") == "not run":
            continue
        has_pump = any(t.name == "Pump" for t in m.templates)
        if has_pump and pump_limit and not deadlock:
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
        exp_m, exp_why = EXPECT_MUNTA.get(qid, (expected, ""))
        # an answer must also pass the gates, unless EXPECT_MUNTA names another outcome
        ok = (u_st == expected and r["uppaal_main"] == expected and mres["status"] == exp_m
              and (counts or qid in EXPECT_MUNTA))
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
            (HERE / "results.json").write_text(json.dumps(old_report, indent=1) + "\n")
        print(f"networks: {bad} differ from results.json")
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
    if not args.only:
        (HERE / "results.json").write_text(json.dumps(report, indent=1) + "\n")
    n = {s: sum(1 for r in results if r["munta"] == s) for s in sorted({r["munta"] for r in results})}
    print(f"{len(results)} queries: {n}; {bad} not as expected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
