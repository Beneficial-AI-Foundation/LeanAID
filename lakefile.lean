import Lake
open Lake DSL

package LeanAID where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib LeanAID where
  roots := #[`LeanAID]

lean_lib App where
  roots := #[`App.Json]

@[default_target]
lean_exe «aid-lean» where
  root := `App.Main

/-- `lake test`: build everything (which checks every proof and every
    conformance case), run `aid-lean selftest`, then run `scripts/check.sh`. -/
@[test_driver]
script test do
  let build ← IO.Process.output { cmd := "lake", args := #["build"] }
  IO.print build.stdout
  IO.eprint build.stderr
  if build.exitCode != 0 then return build.exitCode
  let self ← IO.Process.output { cmd := ".lake/build/bin/aid-lean", args := #["selftest"] }
  IO.print self.stdout
  IO.eprint self.stderr
  if self.exitCode != 0 then return self.exitCode
  let chk ← IO.Process.output { cmd := "bash", args := #["scripts/check.sh"] }
  IO.print chk.stdout
  IO.eprint chk.stderr
  return chk.exitCode
