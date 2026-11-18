/-
  LeanAID.Conformance.Case — the shape of a conformance case.
-/
import LeanAID.Core.DetermineBasal
import LeanAID.Core.JsonOut

namespace LeanAID.Conformance

/-- A `determine_basal` call made by oref0's test suite: the inputs and oref0's
    output as `JSON.stringify` printed it (`none` if oref0 threw). -/
structure DBCase where
  id : String
  name : String
  input : DBInputs
  expected : Option String

/-- Does the Lean transcription produce exactly oref0's output? -/
def DBCase.ok (c : DBCase) : Bool :=
  match c.expected with
  | some e => JsonOut.result (determineBasal c.input) == e
  | none => (determineBasal c.input).error.isSome

end LeanAID.Conformance
