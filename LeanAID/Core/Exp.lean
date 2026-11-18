/-
  LeanAID.Core.Exp — a rational approximation of `Math.exp`, used by oref0's
  exponential insulin curves (`lib/iob/calculate.js` lines 125-128).

  Method, for x ≤ 0 (the only case oref0 uses: the arguments are `-end/tau` and
  `-minsAgo/tau` with positive `tau`):
    1. halve: y = x / 2^k with k the least natural number such that |y| ≤ 1/2;
    2. Taylor polynomial of degree 30 for e^y, evaluated exactly;
    3. square k times.
  After step 2 and after every squaring the value is rounded down to a multiple
  of 2^-128, which keeps the rationals small.

  Error: the Taylor remainder for |y| ≤ 1/2 is below (1/2)^31/31! < 10^-42; each
  rounding adds at most 2^-128 < 3·10^-39, and squaring a value in [0, 1] at most
  doubles an absolute error, so after k ≤ 8 squarings (|x| ≤ 128) the absolute
  error is below 2^9 · 2^-127 < 10^-35. The proof of this bound against Mathlib's
  `Real.exp` is planned for M8 (`docs/LOG.md`); until then the bound is a design
  claim, not a theorem, and nothing in the safety theorems depends on it.
  For x > 0 (never used by oref0) we return 1/approx(-x).
-/
import LeanAID.Core.JsNum

namespace LeanAID.Exp

/-- Round a non-negative rational down to a multiple of 2^-128. -/
def trunc128 (q : Rat) : Rat :=
  let s : Rat := (2 : Rat) ^ 128
  ((q * s).floor : Rat) / s

/-- Taylor polynomial `Σ_{i ≤ n} y^i / i!`, computed by Horner's rule. -/
def taylor (y : Rat) (n : Nat) : Rat :=
  horner n 1
where
  /-- `horner m acc` evaluates `1 + y/1 (1 + y/2 (... (1 + y/m · acc)))`. -/
  horner : Nat → Rat → Rat
    | 0, acc => acc
    | m + 1, acc => horner m (1 + y / (m + 1 : Nat) * acc)

/-- Number of halvings so that |x| / 2^k ≤ 1/2 (bounded by 64 iterations). -/
def halvings (x : Rat) : Nat :=
  go 0 64
where
  go (k : Nat) : Nat → Nat
    | 0 => k
    | fuel + 1 => if (if x < 0 then -x else x) / (2 : Rat) ^ k ≤ 1/2 then k else go (k + 1) fuel

/-- Square `v` `k` times, truncating to 2^-128 after each squaring. -/
def squareN : Nat → Rat → Rat
  | 0, v => v
  | k + 1, v => squareN k (trunc128 (v * v))

/-- e^x for x ≤ 0. -/
def expNonpos (x : Rat) : Rat :=
  let k := halvings x
  let y := x / (2 : Rat) ^ k
  squareN k (trunc128 (taylor y 30))

/-- `Math.exp(x)` -/
def exp (x : Rat) : Rat :=
  if x ≤ 0 then expNonpos x
  else
    let e := expNonpos (-x)
    if e = 0 then 0 else 1 / e

/-- `Math.exp` on JavaScript numbers. -/
def jsExp : JsNum → JsNum
  | .fin x => .fin (Binary64.rd (exp x))
  | .nan => .nan

end LeanAID.Exp
