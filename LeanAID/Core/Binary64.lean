/-
  LeanAID.Core.Binary64 — IEEE-754 binary64 rounding on exact rationals.

  JavaScript numbers are IEEE-754 doubles, and every arithmetic operation (+, −, ×, ÷)
  is defined as: compute the exact real result, then round it to the nearest double,
  ties to even. `rd` is that rounding, on rationals. With it, `JsNum` arithmetic is
  bit-for-bit JavaScript arithmetic, computed without floating point.

  A finite double is `n · 2^e` with integer `|n| < 2^53` and `e ≥ −1074`. For `a > 0`
  let `E(a) = max(⌊log₂ a⌋ − 52, −1074)`; then `rd a = rhe(a / 2^E(a)) · 2^E(a)`,
  where `rhe` rounds to the nearest integer, ties to even. Subnormals are included.
  Overflow is not modelled: values above the largest double (≈ 1.8·10³⁰⁸) are rounded
  with an unbounded exponent instead of becoming ±Infinity (they never occur in
  oref0's computations on valid input).
-/

namespace LeanAID.Binary64

/-- `2^e` for an integer exponent. -/
def pow2 (e : Int) : Rat :=
  if 0 ≤ e then (2 : Rat) ^ e.toNat else 1 / (2 : Rat) ^ (-e).toNat

/-- `⌊log₂ a⌋` for `a > 0`, from the binary lengths of numerator and denominator. -/
def flog2 (a : Rat) : Int :=
  let k0 : Int := (a.num.natAbs.log2 : Int) - (a.den.log2 : Int)
  if pow2 k0 ≤ a then k0 else k0 - 1

/-- The exponent of the last significant bit of the double nearest to `a > 0`. -/
def ulpExp (a : Rat) : Int := max (flog2 a - 52) (-1074)

/-- Round to the nearest integer, ties to even. -/
def rhe (m : Rat) : Int :=
  let f := m.floor
  let r := m - f
  if r < 1/2 then f else if 1/2 < r then f + 1 else if f % 2 = 0 then f else f + 1

/-- Round a positive rational to the nearest double. -/
def rdPos (a : Rat) : Rat := (rhe (a / pow2 (ulpExp a)) : Rat) * pow2 (ulpExp a)

/-- Round to the nearest IEEE-754 binary64 value, ties to even. -/
def rd (x : Rat) : Rat :=
  if x = 0 then 0 else if 0 < x then rdPos x else -(rdPos (-x))

end LeanAID.Binary64
