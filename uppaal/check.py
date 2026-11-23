"""Run every UPPAAL query of the abstraction and write uppaal/results.json.

Each query has an expected status. If a status differs from it, the script exits
with 1. Statuses: holds, fails (for A[] queries), reachable, unreachable (for E<>
queries), parse error (verifyta rejects the model or the query), error (any other
run without exactly one answer), timeout. The plan's status "unsupported" is for
the Munta run of U4.

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


# U1b: the contract model and its variants
FRESH = f"((hasReading == 1) && (age < {M.FRESH_AGE}))"
P1 = "A[] (err1 == 0)"
P3 = "A[] (err3 == 0)"
P5_ISSUED = "A[] (err5 == 0)"
P5_CLOCK = "A[] ((busy == 0) imply ((sinceBolus - p5c) == 0))"
P5_PAIR = "A[] (errPair == 0)"
CGM_OK = f"A[] ((errRead == 0) && ((rdSeen == 1) imply (hasReading == 1)))"
SOON = f"(Step.O3 && (uk >= 2) && (prior == 1) && (p5c < {M.SPACING}))"

# (id, work item, kind, model, mutations, query, expected, what it shows, search)
# Models: "free" (U1a), "contract" (the main U1b model), "nopump" and "relaxed"
# (variants, see MODEL_RELATION). Search: "" (breadth first) or "dfs".
QUERIES_U1B = [
    ("P1", "U1b", "contract", "nopump", (), P1, "holds",
     "an issued high rate or any issued units field comes with a fresh reading", ""),
    ("P1-w-noread", "U1b", "witness", "nopump", (), "E<> (Step.Iss && (hasReading == 0))",
     "reachable", "a cycle before the first reading", ""),
    ("P1-w-inc", "U1b", "witness", "nopump", (),
     f"E<> (Step.Iss && ((rc == 5) || (uk >= 1)) && {FRESH})", "reachable",
     "an issued Increase with a fresh reading", ""),
    ("M-P1-rejected-high", "U1b", "mutation", "nopump", ("p1_rejected_high",), P1, "fails",
     "P1 fails if the controller issues a rejected high rate without a fresh reading", ""),
    ("M-P1-nan-units", "U1b", "mutation", "nopump", ("p1_nan_units",), P1, "fails",
     "P1 fails if the controller issues NaN or non-positive units without a fresh reading", ""),
    ("M-P1-no-hasreading", "U1b", "mutation", "nopump", ("p1_no_hasreading",), P1, "fails",
     "P1 fails if the freshness guard drops hasReading", ""),
    ("P3", "U1b", "contract", "nopump", (), P3, "holds",
     "every issued output satisfies TempOk on its finite fields", ""),
    ("M-P3-positive-120", "U1b", "mutation", "nopump", ("p3_positive_120",), P3, "fails",
     "P3 fails if the controller issues a positive temp of 120 minutes", ""),
    ("P5-issued", "U1b", "contract", "nopump", (), P5_ISSUED, "holds",
     f"issued finite units after a real prior bolus come at least {M.SPACING} s after it", ""),
    ("P5-w-first", "U1b", "witness", "nopump", (),
     "E<> (Step.O3 && (uk >= 2) && (prior == 0))", "reachable",
     "issued finite units with no prior bolus", ""),
    ("P5-w-spaced", "U1b", "witness", "nopump", (),
     f"E<> (Step.O3 && (uk >= 2) && (prior == 1) && (p5c >= {M.SPACING}))", "reachable",
     "issued finite units after a prior bolus, with enough spacing", ""),
    ("P5-w-early", "U1b", "witness", "nopump", (),
     f"E<> (Step.O3 && (uk == 0) && (prior == 1) && (p5c < {M.SPACING}))", "reachable",
     "a cycle too early for a bolus issues no units (steps can be closer than the spacing)", ""),
    ("M-P5-user", "U1b", "mutation", "nopump", ("p5_no_user_reset",), P5_ISSUED, "fails",
     "P5-issued fails if the controller clock is not reset on a user bolus", ""),
    ("M-P5-user-w", "U1b", "witness", "nopump", ("p5_no_user_reset",), f"E<> {SOON}",
     "reachable", "in that mutant, finite units are issued too soon after a user bolus", ""),
    ("P5-clock", "U1b", "contract", "nopump", (), P5_CLOCK, "holds",
     "the controller clock equals the observer clock between steps", ""),
    ("M-P5-clock", "U1b", "mutation", "nopump", ("p5_reset_on_lost",), P5_CLOCK, "fails",
     "P5-clock fails if the controller clock is also reset on a lost or rejected command", ""),
    ("P5-pair", "U1b", "contract", "nopump", (), P5_PAIR, "holds",
     f"two accepted microboluses are at least {M.SPACING} s apart", ""),
    ("P5-pair-w", "U1b", "witness", "nopump", (), "E<> (mb2 == 1)", "reachable",
     "two accepted microboluses", "dfs"),
    ("P5-w-bolus", "U1b", "witness", "nopump", (),
     "E<> (Step.End && (bolusDone == 1) && (err5 == 0) && (errPair == 0))", "reachable",
     "an accepted valid microbolus with no error", ""),
    ("P5-w-user-cycle", "U1b", "witness", "nopump", (), "E<> (Step.O3 && (wUb == 1))",
     "reachable", "a user bolus followed by a cycle in the same step", ""),
    ("cgm", "U1b", "pump", "nopump", (), CGM_OK, "holds",
     "every reading sets hasReading, and readings are at least 150 s apart by the "
     "observer's own clock", ""),
    ("cgm-w", "U1b", "witness", "nopump", (),
     f"E<> (Step.R1 && (rdSeen == 1) && (rdc == 0) && (g == 0) && (first == 0))",
     "reachable", "a reading in a step", ""),
    ("M-cgm-first", "U1b", "mutation", "nopump", ("cgm_first_unrecorded",), CGM_OK, "fails",
     "the query cgm fails if CGM can take the first reading without setting hasReading", ""),
    ("deadlock-contract", "U1b", "pump", "nopump", (), "A[] (!deadlock)", "holds",
     "no reachable state of the contract model is stuck", ""),
    ("P4b-30", "U1b", "contract", "relaxed", (), P4B_30, "holds",
     "1800 s after the close, no positive temp runs, under the duration rule of the contract", ""),
    ("M-P4b-30", "U1b", "mutation", "relaxed", ("p3_positive_120",), P4B_30, "fails",
     "P4b-30 fails if the controller issues a positive temp of 120 minutes", ""),
    ("F-20", "U1b", "witness", "contract", (),
     f"E<> (Step.Closed && (f20 == 1) && {EFF} && (tcls == 3) && (obs >= 7199))", "reachable",
     "a zero temp of 120 minutes accepted from a cycle still runs 7199 s after the close", "dfs"),
    ("prerun-w-t0", "U1b", "witness", "contract", (),
     "E<> (Step.Idle && (first == 1) && (g == 0) && Pump.Temp && (Pump.y == 0) "
     "&& (sinceBolus == 3600) && (preB == 1))", "reachable",
     "at t0 a temp starts, and the last bolus was 3600 s before", ""),
    ("prerun-w-old", "U1b", "witness", "contract", (),
     "E<> (Step.Idle && (first == 1) && (g == 0) && Pump.Temp && (Pump.y >= 1700) "
     "&& (sinceBolus <= 10) && (preB == 1))", "reachable",
     "at t0 an old temp runs, and the last bolus was recent", ""),
]

# U3b: witnesses that a T2 run can realize. Each needs three readings and issues
# what oref0 issues in the T2 runs of LeanAID/Conformance/UppaalReplayU1b.lean:
# a high temp of 30 minutes with a microbolus (SMB), or a low temp of 30 minutes.
SMB = "(rc == 5) && (dk == 3) && (dv == 30) && (uk == 3)"
LOWT = "(rc == 4) && (dk == 3) && (dv == 30) && (uk == 0)"
QUERIES_U3B = [
    ("R-P1-w-inc", "U3b", "witness", "nopump", (),
     f"E<> (Step.Iss && {SMB} && {FRESH} && (nRead == 3) && (wOdd == 0))", "reachable",
     "P1-w-inc with a realizable output: a microbolus with a fresh reading", ""),
    ("R-P5-w-first", "U3b", "witness", "nopump", (),
     f"E<> (Step.O3 && {SMB} && (prior == 0) && (nRead == 3) && (wOdd == 0))", "reachable",
     "P5-w-first with a realizable output: a first microbolus without history", ""),
    ("R-P5-w-spaced", "U3b", "witness", "nopump", (),
     f"E<> (Step.O3 && (uk == 3) && (prior == 1) && (mb1 == 1) && (p5c >= {M.SPACING}) && (nRead == 3) "
     f"&& (wOdd == 0))",
     "reachable", "P5-w-spaced with a realizable output: a microbolus after an earlier one", ""),
    ("R-P5-w-early", "U3b", "witness", "nopump", (),
     f"E<> (Step.O3 && {LOWT} && (prior == 1) && (p5c < {M.SPACING}) && (nRead == 3) && (wOdd == 0))", "reachable",
     "P5-w-early with a realizable output: a cycle soon after a user bolus issues no units", ""),
    ("R-P5-pair-w", "U3b", "witness", "nopump", (),
     f"E<> (Step.End && (mb2 == 1) && (bolusDone == 1) && (nRead == 3) && (wOdd == 0))", "reachable",
     "P5-pair-w with realizable outputs: two accepted microboluses, both executed", ""),
    ("R-P5-w-bolus", "U3b", "witness", "nopump", (),
     f"E<> (Step.End && (bolusDone == 1) && (err5 == 0) && (errPair == 0) && (rc == 5) && (dk == 3) "
     f"&& (dv == 30) && (nRead == 3) && (wOdd == 0))", "reachable",
     "P5-w-bolus with a realizable output: an executed microbolus with a high temp", ""),
    ("R-P5-w-user-cycle", "U3b", "witness", "nopump", (),
     f"E<> (Step.O3 && (wUb == 1) && {LOWT} && (nRead == 3) && (wOdd == 0))", "reachable",
     "P5-w-user-cycle with a realizable output: a user bolus and a cycle in one step", ""),
    ("R-F-20", "U3b", "witness", "nobolus", (),
     f"E<> (Step.Closed && (f20 == 1) && {EFF} && (tcls == 3) && (obs >= 7199) && (nRead == 3) && (wOdd == 0))",
     "reachable", "F-20 with three readings before the cycle", ""),
]

# How the model of a result relates to the main model of its work item.
MODEL_RELATION = {
    "free": "the U1a model (Step and Pump with a free command choice), with its "
            "self-loop on Step.Closed. A deadlock result is about this model, not "
            "about a model without the self-loop",
    "contract": "the main U1b model: the U1a model with Controller, CGM, User, the "
                "contract and the issue observers",
    "nopump": "the main U1b model without Pump and the P4a observer. Pump never "
              "blocks Step: it has a receiving edge for every value of its guards, "
              "and its expiry edge releases its invariant. So this variant has the "
              "same runs, projected on its variables, and its results, the deadlock "
              "result included, are taken for the main U1b model. This is an "
              "argument, not a check",
    "nobolus": "the main U1b model without user boluses, without the pre-run bolus, and "
               "without controller outputs that carry units. It has fewer behaviors than "
               "the main U1b model, so a reachable result transfers to it. An unreachable "
               "or A[] result does not",
    "relaxed": "the U1a model with the command choice limited to the field domains "
               "and TempOk of the contract, without the freshness and spacing guards. "
               "Readings, user boluses and the issue observers change no pump "
               "variable and block nothing, so on the pump, the P4a observer and the "
               "close this variant has more behaviors than the main U1b model. An A[] "
               "result that holds transfers to the main U1b model. A counterexample "
               "does not",
}
KIND_NOTE = {
    "witness": "Witness flags that no guard reads are added. A reachable result "
               "transfers to the same model without them (for a mutant: to the mutant "
               "only).",
    "mutation": "A mutant: the result is about the mutant only and shows that the "
                "query detects the fault. A counterexample is not one of the main model.",
}


def relation(model, kind, muts):
    notes = [KIND_NOTE["mutation"]] if muts else []
    if kind == "witness":
        notes.append(KIND_NOTE["witness"])
    return MODEL_RELATION[model] + ". " + " ".join(notes)


def build(model, muts, wit):
    if model == "free":
        return M.build(muts, witnesses=wit)
    if model == "relaxed":
        return M.build(muts, witnesses=wit, relaxed=True)
    m = M.build(muts, witnesses=wit, contract=True)
    if model == "nobolus":
        return M.without_boluses(m)
    return M.without_pump(m) if model == "nopump" else m


# every query: the U1a queries run on the free model with breadth-first search
ALL = [(q[0], q[1], q[2], "free", *q[3:], "") for q in QUERIES] + QUERIES_U1B + QUERIES_U3B


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def git(*args):
    return subprocess.run(["git", "-C", str(HERE), *args], capture_output=True,
                          text=True).stdout.strip()


def verify_cmd(verifyta, xml, qfile, search=""):
    return [verifyta, "-q"] + (["-o", "1"] if search == "dfs" else []) + [str(xml), str(qfile)]


def verify(verifyta, xml, qfile, search=""):
    cmd = verify_cmd(verifyta, xml, qfile, search)
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return "timeout", "", time.monotonic() - t0
    out = p.stdout + p.stderr
    sat, unsat = out.count("Formula is satisfied."), out.count("Formula is NOT satisfied.")
    if sat + unsat == 0 and "[error]" in out:
        # verifyta rejected the model or the query (syntax or type error)
        return "parse error", out.strip()[-500:], time.monotonic() - t0
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
        unknown = sorted(set(args.only) - {q[0] for q in ALL})
        if unknown:
            ap.error(f"unknown query IDs: {' '.join(unknown)}")
    OUT.mkdir(exist_ok=True)
    version = subprocess.run([args.verifyta, "--version"], capture_output=True,
                             text=True).stdout.splitlines()[0]
    results, bad = [], 0
    for (qid, item, kind, model, muts, query, expected, about, search) in ALL:
        if args.only and qid not in args.only:
            continue
        wit = kind == "witness"
        name = model + "".join("." + m for m in muts) + (".witness" if wit else "")
        xml = OUT / f"{name}.xml"
        M.write_uppaal(build(model, muts, wit), xml)
        qfile = OUT / f"{qid}.q"
        qfile.write_text(query + "\n")
        answer, msg, secs = verify(args.verifyta, xml, qfile, search)
        st = status(query, answer)
        ok = st == expected
        bad += not ok
        print(f"{'ok ' if ok else 'BAD'} {qid:18} {st:11} (expected {expected}, {secs:.1f} s)")
        results.append({"id": qid, "item": item, "kind": kind, "mutations": list(muts),
                        "about": about, "query": query, "expected": expected,
                        "status": st, "ok": ok, "seconds": round(secs, 2), "message": msg,
                        "model": xml.name, "model_sha256": sha256(xml),
                        "model_variant": model, "search": search or "breadth first",
                        "relation": relation(model, kind, muts),
                        "command": " ".join(verify_cmd("VERIFYTA", xml.name, qfile.name, search)),
                        "max_valid_duration": 121 if "no_duration_upper_bound" in muts else 120,
                        "query_sha256": sha256(qfile)})
    report = {
        "revision": git("rev-parse", "HEAD"),
        # uncommitted changes to tracked files anywhere in the repository, and
        # untracked files under uppaal/
        "dirty": bool(git("status", "--porcelain", "--untracked-files=no", ":/")
                      or git("status", "--porcelain", "--", ".")),
        "tool": version,
        "verifyta": args.verifyta,
        # each result has its own command line; VERIFYTA stands for the binary above
        "command": "per result, in results[].command",
        "timeout_seconds": TIMEOUT,
        "base_parameters": {"time_unit": "1 s", "duration_unit": "1 min",
                            "issued_duration_values": "-1..121",
                            "max_valid_duration": 120,
                            "smb_spacing_s": M.SPACING, "fresh_age_s": M.FRESH_AGE,
                            "reading_gap_s": M.READ_GAP},
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
