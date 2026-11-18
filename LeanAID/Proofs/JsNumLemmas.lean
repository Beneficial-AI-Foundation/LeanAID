/-
  LeanAID.Proofs.JsNumLemmas — rewriting `JsNum` operations on finite values.
-/
import LeanAID.Core.Types

namespace LeanAID.JsNum

@[simp] theorem fin_add (a b : Rat) : (fin a) + (fin b) = fin (a + b) := rfl
@[simp] theorem fin_sub (a b : Rat) : (fin a) - (fin b) = fin (a - b) := rfl
@[simp] theorem fin_mul (a b : Rat) : (fin a) * (fin b) = fin (a * b) := rfl
@[simp] theorem fin_neg (a : Rat) : -(fin a) = fin (-a) := rfl
theorem fin_div {a b : Rat} (h : b ≠ 0) : (fin a) / (fin b) = fin (a / b) := by
  show JsNum.div (fin a) (fin b) = _
  simp [JsNum.div, h]
@[simp] theorem nan_add (x : JsNum) : JsNum.nan + x = .nan := rfl
@[simp] theorem add_nan (x : JsNum) : x + JsNum.nan = .nan := by cases x <;> rfl
@[simp] theorem nan_sub (x : JsNum) : JsNum.nan - x = .nan := rfl
@[simp] theorem sub_nan (x : JsNum) : x - JsNum.nan = .nan := by cases x <;> rfl
@[simp] theorem mul_nan (x : JsNum) : x * JsNum.nan = .nan := by cases x <;> rfl
@[simp] theorem div_nan (x : JsNum) : x / JsNum.nan = .nan := by cases x <;> rfl
@[simp] theorem nan_mul (x : JsNum) : JsNum.nan * x = .nan := rfl
@[simp] theorem nan_div (x : JsNum) : JsNum.nan / x = .nan := rfl
@[simp] theorem min_fin (a b : Rat) : JsNum.min (fin a) (fin b) = fin (if a ≤ b then a else b) := rfl
@[simp] theorem max_fin (a b : Rat) : JsNum.max (fin a) (fin b) = fin (if a ≤ b then b else a) := rfl
@[simp] theorem min3_fin (a b c : Rat) :
    JsNum.min3 (fin a) (fin b) (fin c) = JsNum.min (JsNum.min (fin a) (fin b)) (fin c) := rfl
@[simp] theorem lt_fin (a b : Rat) : (fin a <ʲ fin b) = decide (a < b) := rfl
@[simp] theorem le_fin (a b : Rat) : (fin a ≤ʲ fin b) = decide (a ≤ b) := rfl
@[simp] theorem gt_fin (a b : Rat) : (fin a >ʲ fin b) = decide (b < a) := rfl
@[simp] theorem ge_fin (a b : Rat) : (fin a ≥ʲ fin b) = decide (b ≤ a) := rfl
@[simp] theorem seq_fin (a b : Rat) : (fin a =ʲ fin b) = decide (a = b) := rfl
@[simp] theorem lt_nan (x : JsNum) : (x <ʲ .nan) = false := by cases x <;> rfl
@[simp] theorem nan_lt (x : JsNum) : (JsNum.nan <ʲ x) = false := rfl
@[simp] theorem le_nan (x : JsNum) : (x ≤ʲ .nan) = false := by cases x <;> rfl
@[simp] theorem nan_le (x : JsNum) : (JsNum.nan ≤ʲ x) = false := rfl
@[simp] theorem gt_nan (x : JsNum) : (x >ʲ .nan) = false := rfl
@[simp] theorem nan_gt (x : JsNum) : (JsNum.nan >ʲ x) = false := by cases x <;> rfl
@[simp] theorem ge_nan (x : JsNum) : (x ≥ʲ .nan) = false := rfl
@[simp] theorem nan_ge (x : JsNum) : (JsNum.nan ≥ʲ x) = false := by cases x <;> rfl
theorem ofNat_eq (n : Nat) : (OfNat.ofNat n : JsNum) = fin (OfNat.ofNat n) := rfl
@[simp] theorem zero_eq : (0 : JsNum) = fin 0 := rfl
@[simp] theorem one_eq : (1 : JsNum) = fin 1 := rfl
@[simp] theorem truthy_fin (a : Rat) : (fin a).truthy = (a != 0) := rfl
@[simp] theorem truthy_nan : JsNum.nan.truthy = false := rfl

end LeanAID.JsNum

namespace LeanAID
@[simp] theorem Option.js_some (x : JsNum) : (some x).js = x := rfl
@[simp] theorem Option.js_none : (none : Option JsNum).js = .nan := rfl
@[simp] theorem Option.truthyN_some (x : JsNum) : (some x).truthyN = x.truthy := rfl
@[simp] theorem Option.truthyN_none : (none : Option JsNum).truthyN = false := rfl
end LeanAID
