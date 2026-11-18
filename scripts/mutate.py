#!/usr/bin/env python3
"""Mutation testing of the verified core (M12).

For each mutation: apply one small textual change to a file in LeanAID/Core, run
`lake build LeanAID`, record which proof modules / theorems fail and whether the
conformance checks (LeanAID/Conformance/Checks.lean) fail, then restore the file.
A mutation that breaks no theorem and passes conformance is a gap in the
specification. Writes docs/mutation.json and docs/MUTATION.md.

Run from the repository root:  python3 scripts/mutate.py
"""
import json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
C = "LeanAID/Core/"
MUTATIONS = [
    ("M01", C + "BasalSetTemp.lean", "else if rate >ʲ maxSafeBasal then maxSafeBasal", "else if false then maxSafeBasal", "remove the maxSafeBasal clamp"),
    ("M02", C + "BasalSetTemp.lean", "if rate <ʲ 0 then 0", "if false then 0", "remove the clamp at 0"),
    ("M03", C + "BasalSetTemp.lean", "(multiplierOr p.max_daily_safety_multiplier 3 * p.max_daily_basal.js)", "(multiplierOr p.max_daily_safety_multiplier 30 * p.max_daily_basal.js)", "default daily multiplier 3 -> 30"),
    ("M04", C + "BasalSetTemp.lean", "JsNum.min3 p.max_basal.js", "JsNum.min3 (p.max_basal.js * 2)", "double max_basal in maxSafeBasal"),
    ("M05", C + "BasalSetTemp.lean", "suggestedRate ≤ʲ ctRate * 1.2", "suggestedRate ≤ʲ ctRate * 3", "keep running temps up to 3x the request"),
    ("M06", C + "RoundBasal.lean", "else if basal <ʲ 10 then roundToScale basal 20", "else if basal <ʲ 10 then roundToScale basal 10", "round 1-10 U/h to 0.1 instead of 0.05"),
    ("M07", C + "JsNum.lean", "def roundInt (q : Rat) : Int := (q + 1/2).floor", "def roundInt (q : Rat) : Int := (q + 1).floor", "Math.round rounds up"),
    ("M08", C + "DetermineBasal.lean", "  else if c.bg <ʲ c.threshold || c.minGuardBG <ʲ c.threshold then", "  else if c.bg <ʲ c.threshold then", "low glucose suspend ignores predicted lows"),
    ("M09", C + "DetermineBasal.lean", "    setTempBasal 0 durationReq p rT (some c.ct)\n  else dbDoseRest c rT", "    setTempBasal c.basal durationReq p rT (some c.ct)\n  else dbDoseRest c rT", "low glucose suspend sets the basal instead of 0"),
    ("M10", C + "DetermineBasal.lean", "def thresholdOf (min_bg : JsNum) : JsNum := min_bg - 0.5 * (min_bg - 40)", "def thresholdOf (min_bg : JsNum) : JsNum := min_bg - 0.9 * (min_bg - 40)", "lower the hypo threshold"),
    ("M11", C + "DetermineBasal.lean", "  if insulinReq >ʲ room then room else insulinReq", "  if false then room else insulinReq", "no max_iob cap on insulinReq"),
    ("M12", C + "DetermineBasal.lean", "mathFloor (JsNum.min (insulinReq / 2) (smbMaxBolus c) * roundSMBTo) / roundSMBTo", "mathFloor (JsNum.min insulinReq (smbMaxBolus c) * roundSMBTo) / roundSMBTo", "microbolus = full insulinReq instead of half"),
    ("M13", C + "DetermineBasal.lean", "  lastBolusAge c >ʲ smbInterval c.p && smbMicroBolus c insulinReq >ʲ 0", "  smbMicroBolus c insulinReq >ʲ 0", "no SMB interval check"),
    ("M14", C + "DetermineBasal.lean", "  else (30, rnd (basal * durationReq / 30) 2)", "  else (30, rnd (basal * durationReq / 20) 2)", "SMB low temp computed over 20 min"),
    ("M15", C + "DetermineBasal.lean", "def cgmBad (g : GluVals) : Bool := g.bg ≤ʲ 10 || g.bg =ʲ 38 || g.noise ≥ʲ 3", "def cgmBad (g : GluVals) : Bool := g.bg ≤ʲ 5 || g.bg =ʲ 38 || g.noise ≥ʲ 3", "error-code threshold 10 -> 5"),
    ("M16", C + "DetermineBasal.lean", "def cgmStale (g : GluVals) : Bool := g.minAgo >ʲ 12 || g.minAgo <ʲ (-5)", "def cgmStale (g : GluVals) : Bool := g.minAgo >ʲ 120 || g.minAgo <ʲ (-5)", "staleness limit 12 -> 120 min"),
    ("M17", C + "DetermineBasal.lean", "duration := some 30, rate := some basal }", "duration := some 30, rate := some (basal * 2) }", "CGM-error branch doubles the basal"),
    ("M18", C + "DetermineBasal.lean", "  | _, _ => .error (Result.err \"Error: could not determine target_bg. \")", "  | _, _ => .ok (100, 100)", "missing targets default to 100"),
    ("M19", C + "DetermineBasal.lean", "    setTempBasal c.basal 30 c.p\n      (rT.addReason (\"; setting current basal of \"", "    setTempBasal (c.basal * 1.1) 30 c.p\n      (rT.addReason (\"; setting current basal of \"", "neutral temp is 110% of basal"),
    ("M20", C + "DetermineBasal.lean", "    let insulinReq0 := rnd (2 * JsNum.min 0 ((eventualBG - c.target_bg) / c.sens)) 2", "    let insulinReq0 := rnd (2 * JsNum.max 0 ((eventualBG - c.target_bg) / c.sens)) 2", "low eventualBG adds insulin (min -> max)"),
    ("M21", C + "DetermineBasal.lean", "  let five_min_blocks : JsNum := 24", "  let five_min_blocks : JsNum := 12", "expected delta over 1 h instead of 2 h"),
    ("M22", C + "DetermineBasal.lean", "  if sensitivityRatio.truthyN then roundBasal (p.current_basal.js * sensitivityRatio.js) p.model", "  if sensitivityRatio.truthyN then roundBasal (p.current_basal.js * sensitivityRatio.js * 2) p.model", "sensitivity-adjusted basal doubled"),
    ("M23", C + "DetermineBasal.lean", "      if c.iobd.iob.js >ʲ c.max_iob then", "      if c.iobd.iob.js >ʲ c.max_iob * 2 then", "IOB check against 2 x max_iob"),
    ("M24", C + "Iob.lean", "iobContrib := insulin * ((-0.001852 * x1 * x1)", "iobContrib := insulin * ((-0.0019 * x1 * x1)", "bilinear IOB coefficient changed"),
]

def theorem_at(path, line):
    try:
        lines = open(os.path.join(ROOT, path)).read().split("\n")
    except OSError:
        return None
    for i in range(min(line, len(lines)) - 1, -1, -1):
        m = re.match(r"^(?:private )?theorem\s+(\S+)", lines[i])
        if m:
            return m.group(1)
    return None

results = []
for mid, path, old, new, desc in MUTATIONS:
    full = os.path.join(ROOT, path)
    orig = open(full).read()
    if orig.count(old) != 1:
        results.append({"id": mid, "file": path, "description": desc, "applied": False,
                        "note": "pattern found %d times" % orig.count(old)})
        print(mid, "NOT APPLIED", flush=True)
        continue
    try:
        open(full, "w").write(orig.replace(old, new))
        p = subprocess.run(["lake", "build", "LeanAID"], cwd=ROOT, capture_output=True, text=True, timeout=3600)
        out = p.stdout + p.stderr
    finally:
        open(full, "w").write(orig)
    errs = re.findall(r"error: ([\w/]+\.lean):(\d+):\d+", out)
    broken_files = sorted(set(f for f, _ in errs))
    thms = sorted(set(t for t in (theorem_at(f, int(l)) for f, l in errs if f.startswith("LeanAID/Proofs")) if t))
    core_fails = any(f.startswith("LeanAID/Core") for f in broken_files)
    conformance = any(f.startswith("LeanAID/Conformance") for f in broken_files)
    proofs = [f for f in broken_files if f.startswith("LeanAID/Proofs")]
    # downstream modules that could not be built because an import failed
    blocked = sorted(set(re.findall(r"- (LeanAID\.[\w.]+)", out)))
    r = {"id": mid, "file": path, "description": desc, "applied": True, "buildOk": p.returncode == 0,
         "coreDoesNotCompile": core_fails, "brokenProofFiles": proofs, "brokenTheorems": thms,
         "conformanceFails": conformance, "failedModules": blocked}
    r["caught"] = (not r["buildOk"])
    results.append(r)
    print(mid, desc, "->", "CAUGHT" if r["caught"] else "NOT CAUGHT", "| theorems:", len(thms),
          "| conformance:", conformance, flush=True)

subprocess.run(["git", "diff", "--quiet", "--", "LeanAID/Core"], cwd=ROOT, check=True)
json.dump(results, open(os.path.join(ROOT, "docs/mutation.json"), "w"), indent=1)
rows = ["| id | mutation | caught by proofs | caught by conformance | theorems that break |", "|---|---|---|---|---|"]
for r in results:
    if not r["applied"]:
        rows.append("| %s | %s | not applied (%s) | | |" % (r["id"], r["description"], r["note"])); continue
    rows.append("| %s | %s (`%s`) | %s | %s | %s |" % (
        r["id"], r["description"], r["file"].split("/")[-1],
        "yes" if r["brokenProofFiles"] else "no", "yes" if r["conformanceFails"] else "no",
        ", ".join("`%s`" % t for t in r["brokenTheorems"][:8]) + (" …" if len(r["brokenTheorems"]) > 8 else "")))
open(os.path.join(ROOT, "docs/MUTATION.md"), "w").write(
    "# Mutation testing\n\nGenerated by `scripts/mutate.py`. Each row is one mutation of `LeanAID/Core`, "
    "built with `lake build LeanAID`. \"Caught by proofs\": some theorem in `LeanAID/Proofs` no longer checks. "
    "\"Caught by conformance\": a check in `LeanAID/Conformance/Checks.lean` fails. A mutation caught by neither "
    "is a gap in the specification.\n\n" + "\n".join(rows) + "\n")
print("done")
