import LeanAID.Core.JsNum
namespace LeanAID
theorem nan_falsy : JsNum.truthy JsNum.nan = false := rfl
end LeanAID
