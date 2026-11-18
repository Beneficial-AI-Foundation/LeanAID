/-
  LeanAID.Core.RoundBasal — transcription of `lib/round-basal.js` (lines 3-41).
-/
import LeanAID.Core.Types

namespace LeanAID

/-- `Math.round(x * scale) / scale` -/
def roundToScale (x : JsNum) (scale : Rat) : JsNum :=
  JsNum.div (JsNum.mathRound (JsNum.mul x (.fin scale))) (.fin scale)

/-- The `lowest_rate_scale` of round-basal.js lines 11-24: 40 (0.025 U/h steps) for
    pump models ending in "54" or "23", otherwise 20 (0.05 U/h steps).
    `model` is `profile.model` when it is a string; `none` covers both a missing
    profile and a non-string model. -/
def lowestRateScale (model : Option String) : Rat :=
  match model with
  | some m => if m.endsWith "54" || m.endsWith "23" then 40 else 20
  | none => 20

/-- `round_basal(basal, profile)`, round-basal.js lines 3-41. -/
def roundBasal (basal : JsNum) (model : Option String) : JsNum :=
  if basal <ʲ 1 then roundToScale basal (lowestRateScale model)
  else if basal <ʲ 10 then roundToScale basal 20
  else roundToScale basal 10

end LeanAID
