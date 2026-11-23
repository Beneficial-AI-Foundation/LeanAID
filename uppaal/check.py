"""Run every UPPAAL query of the abstraction and write uppaal/results.json.

Each query has an expected status. If a status differs from it, the script exits
with 1. Statuses: holds, fails (for A[] queries), reachable, unreachable (for E<>
queries), error, timeout.

Usage: python3 -I uppaal/check.py --verifyta PATH [--only ID ...]
"""

import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import model as M  # noqa: E402

OUT = HERE / "out"
TIMEOUT = 1800

EFF = "(Pump.Temp && (Pump.y < (dur * 60)))"            # the pump delivers a temp
OBL_TEMP = M.any_of("oCls", [M.ZERO, M.LOW, M.HIGH])
RUNNING = f"({OBL_TEMP} && (o4 < (oDur * 60)))"
EXPIRED = f"({OBL_TEMP} && (o4 >= (oDur * 60)))"
POSITIVE = "((tcls == 4) || (tcls == 5))"

P4A = (f"A[] ((busy == 0) imply ((({RUNNING}) imply ({EFF} && {M.same_class('tcls', 'oCls')})) "
       f"&& (({EXPIRED}) imply (!{EFF})) && ((oCls == {M.SCHED_OBLIGATION}) imply (!{EFF}))))")
P4B_120 = f"A[] ((Step.Closed && (obs >= 7200) && (busy == 0)) imply (!{EFF}))"
BOLUS = ("A[] (Step.End imply (((bolusDone == 1) && (expB == 1)) "
         "|| ((bolusDone == 0) && (expB == 0))))")
P4B_30 = f"A[] ((Step.Closed && (obs >= 1800) && (busy == 0)) imply (!({EFF} && {POSITIVE})))"

# (id, work item, kind, mutations, query, expected, what it shows)
QUERIES = [
    ("P4a", "U1a", "pump", (), P4A, "holds",
     "an accepted temp runs for its duration with its class, then the schedule runs; "
     "an accepted cancel gives the schedule"),
    ("P4a-w-running", "U1a", "witness", (), f"E<> ((busy == 0) && {RUNNING})", "reachable",
     "trigger of P4a: a temp obligation is running"),
    ("P4a-w-expired", "U1a", "witness", (), f"E<> ((busy == 0) && {EXPIRED})", "reachable",
     "trigger of P4a: a temp obligation has expired"),
    ("P4a-w-cancel", "U1a", "witness", (),
     f"E<> ((busy == 0) && (oCls == {M.SCHED_OBLIGATION}) && (wCancel == 1))", "reachable",
     "trigger of P4a: an accepted cancel of a running temp"),
    ("collision", "U1a", "witness", (), "E<> ((busy == 0) && (wColl == 1))", "reachable",
     "a step at the deadline of a temp sets a new temp (P4a holds on it)"),
    ("P4b-120", "U1a", "pump", (), P4B_120, "holds",
     "7200 s after the close, the schedule runs, for any accepted command"),
    ("P4b-120-w", "U1a", "witness", (),
     f"E<> (Step.Closed && (obs >= 7199) && (busy == 0) && {EFF})", "reachable",
     "a temp still runs 7199 s after the close"),
    ("P4b-30-free", "U1a", "pump", (), P4B_30, "fails",
     "without the contract, a positive temp can run 1800 s after the close: P4b-30 "
     "rests on p3_temp_ok, not on validation"),
    ("P4b-30-free-w", "U1a", "witness", (),
     f"E<> (Step.Closed && (obs >= 1800) && (busy == 0) && {EFF} && {POSITIVE} "
     f"&& (dur == 120))", "reachable",
     "a positive temp of 120 minutes is accepted without the contract"),
    ("bolus", "U1a", "pump", (), BOLUS, "holds",
     "at the end of each step, the pump executed a bolus exactly when the observer "
     "expects one: an accepted command that validate accepts, with a positive bolus"),
    ("bolus-w", "U1a", "witness", (), "E<> (Step.End && (bolusDone == 1))", "reachable",
     "an accepted valid bolus executes"),
    ("reject-bolus-w", "U1a", "witness", (),
     "E<> (Step.End && (wRejBolus == 1) && (bolusDone == 0))", "reachable",
     "a command with an invalid duration and a positive bolus is rejected, and its "
     "bolus does not execute (the query bolus covers every such command)"),
    ("close-no-steps-w", "U1a", "witness", (), "E<> (Step.Closed && (wNoSteps == 1))",
     "reachable", "a run with no steps closes at t0"),
    ("deadlock", "U1a", "pump", (), "A[] (!deadlock)", "holds",
     "no reachable state is stuck: every committed chain of a step has an enabled edge "
     "for every issued command"),
    ("M-no-upper-bound", "U1a", "mutation", ("no_duration_upper_bound",), P4B_120, "fails",
     "P4b-120 fails if validDuration accepts 121 minutes"),
    ("M-ignore-cancel", "U1a", "mutation", ("pump_ignores_cancel",), P4A, "fails",
     "P4a fails if the pump ignores a cancel"),
    ("M-missing-reject", "U1a", "mutation", ("missing_reject_bolus",), "A[] (!deadlock)",
     "fails", "the deadlock query finds a command for which no execution edge exists"),
    ("M-reject-initial", "U1a", "mutation", ("reject_cancels_initial",), P4A, "fails",
     "P4a fails if the pump ends the initial temp on a rejected command"),
    ("M-drop-temp", "U1a", "mutation", ("pump_drops_valid_temp",), P4A, "fails",
     "P4a fails if the pump silently drops an accepted valid temp"),
    ("M-reject-bolus", "U1a", "mutation", ("reject_executes_bolus",), BOLUS, "fails",
     "the query bolus fails if the pump executes the bolus of a rejected command"),
    ("M-no-y-reset", "U1a", "mutation", ("pump_no_reset_on_replace",), P4A, "fails",
     "P4a fails if the pump clock is not reset when a temp replaces another"),
]


# How the model of a result relates to the main model, and what the result says
# about the main model.
RELATION = {
    "pump": "the main model, with its self-loop on Step.Closed. A deadlock result "
            "is about this model, not about a model without the self-loop",
    "witness": "the main model plus witness flags that no guard reads. Its states, "
               "with the flags removed, are the states of the main model, so a "
               "reachable result transfers to the main model",
    "mutation": "a mutant of the main model. The result is about the mutant only and "
                "shows that the query detects the fault. A counterexample is not one "
                "of the main model",
}


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def git(*args):
    return subprocess.run(["git", "-C", str(HERE), *args], capture_output=True,
                          text=True).stdout.strip()


def verify(verifyta, xml, qfile):
    cmd = [verifyta, "-q", str(xml), str(qfile)]
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return "timeout", "", time.monotonic() - t0
    out = p.stdout + p.stderr
    sat, unsat = out.count("Formula is satisfied."), out.count("Formula is NOT satisfied.")
    if p.returncode != 0 or sat + unsat != 1 or "[error]" in out:
        return "error", out.strip()[-500:], time.monotonic() - t0
    return (sat == 1), "", time.monotonic() - t0


def status(query, answer):
    if not isinstance(answer, bool):
        return answer
    if query.startswith("A[]"):
        return "holds" if answer else "fails"
    return "reachable" if answer else "unreachable"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verifyta", required=True)
    ap.add_argument("--only", nargs="+", metavar="ID")
    args = ap.parse_args()
    if args.only:
        unknown = sorted(set(args.only) - {q[0] for q in QUERIES})
        if unknown:
            ap.error(f"unknown query IDs: {' '.join(unknown)}")
    OUT.mkdir(exist_ok=True)
    version = subprocess.run([args.verifyta, "--version"], capture_output=True,
                             text=True).stdout.splitlines()[0]
    results, bad = [], 0
    for (qid, item, kind, muts, query, expected, about) in QUERIES:
        if args.only and qid not in args.only:
            continue
        wit = kind == "witness"
        name = "model" + "".join("." + m for m in muts) + (".witness" if wit else "")
        xml = OUT / f"{name}.xml"
        M.write_uppaal(M.build(muts, witnesses=wit), xml)
        qfile = OUT / f"{qid}.q"
        qfile.write_text(query + "\n")
        answer, msg, secs = verify(args.verifyta, xml, qfile)
        st = status(query, answer)
        ok = st == expected
        bad += not ok
        print(f"{'ok ' if ok else 'BAD'} {qid:18} {st:11} (expected {expected}, {secs:.1f} s)")
        results.append({"id": qid, "item": item, "kind": kind, "mutations": list(muts),
                        "about": about, "query": query, "expected": expected,
                        "status": st, "ok": ok, "seconds": round(secs, 2), "message": msg,
                        "model": xml.name, "model_sha256": sha256(xml),
                        "relation": RELATION[kind],
                        "max_valid_duration": 121 if "no_duration_upper_bound" in muts else 120,
                        "query_sha256": sha256(qfile)})
    report = {
        "revision": git("rev-parse", "HEAD"),
        # uncommitted changes to tracked files anywhere in the repository, and
        # untracked files under uppaal/
        "dirty": bool(git("status", "--porcelain", "--untracked-files=no", ":/")
                      or git("status", "--porcelain", "--", ".")),
        "tool": version,
        "command": f"{args.verifyta} -q MODEL QUERY",
        "timeout_seconds": TIMEOUT,
        "base_parameters": {"time_unit": "1 s", "duration_unit": "1 min",
                            "issued_duration_values": "-1..121",
                            "max_valid_duration": 120},
        "generator_sha256": sha256(HERE / "model.py"),
        "checker_sha256": sha256(pathlib.Path(__file__)),
        "results": results,
    }
    if not args.only:
        (HERE / "results.json").write_text(json.dumps(report, indent=1) + "\n")
    print(f"{len(results)} queries, {bad} not as expected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
