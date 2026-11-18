/-
  LeanAID.Core.Step — the single entry point of the verified core, exported to C
  as `aid_step` for embedding (e.g. in an seL4 protection domain). Pure: no I/O,
  the clock is part of the input.
-/
import LeanAID.Core.DetermineBasal

namespace LeanAID

/-- One decision of oref0's dose algorithm: `determine_basal` on the given inputs. -/
@[export aid_step]
def step (inp : DBInputs) : Result := determineBasal inp

end LeanAID
