/-
  TestDriver — the `lake test` driver (see `testDriver` in lakefile.toml).

  Runs, in order, and stops at the first failure:
    1. `lake build`: checks every proof and every conformance case;
    2. `.lake/build/bin/aid-lean selftest`;
    3. `bash scripts/check.sh`: forbidden constructs and headline axioms.
  Exits with the exit code of the first step that fails, or 0.
-/

/-- Run `cmd args`, print its output, and return its exit code. -/
def step (cmd : String) (args : Array String) : IO UInt32 := do
  let out ← IO.Process.output { cmd, args }
  IO.print out.stdout
  IO.eprint out.stderr
  return out.exitCode

def main : IO UInt32 := do
  let steps : List (String × Array String) :=
    [("lake", #["build"]),
     (".lake/build/bin/aid-lean", #["selftest"]),
     ("bash", #["scripts/check.sh"])]
  for (cmd, args) in steps do
    let rc ← step cmd args
    if rc != 0 then return rc
  return 0
