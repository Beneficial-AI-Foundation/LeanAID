import LeanAID.Core.Binary64Impl
/-
  LeanAID.Core.JsNum — a model of the JavaScript numbers oref0 computes with.

  oref0 is written in JavaScript, where every number is an IEEE-754 double and
  where missing object fields (`undefined`) silently turn into `NaN` when used in
  arithmetic. oref0's own tests rely on this: they call `determine_basal` with
  objects that lack fields, and the algorithm carries `NaN` values through
  several branches. A faithful transcription therefore has to model `NaN`.

  We model a JavaScript number as either `NaN` or a finite value held exactly as
  a rational, and every arithmetic operation as JavaScript defines it: the exact
  result rounded to the nearest IEEE-754 double, ties to even (`Binary64.rd`).
  Decimal literals denote the double nearest to them, as in JavaScript.
  Known, documented differences from JavaScript (`docs/DESIGN.md`):

  * Division by zero yields `NaN` here; JavaScript yields `±Infinity` for a
    non-zero numerator. Valid inputs never divide by zero.
  * No overflow to ±Infinity (values never exceed 1.8·10³⁰⁸ here).
  * Negative zero is not modelled (`-0 === 0` in JavaScript, and it prints as
    `0`, so it is unobservable in oref0's outputs).
  * Integer literals are taken as exact (all literals in the code are below 2^53,
    where integers are doubles).

  Everything here is pure and uses only Lean core.
-/

namespace LeanAID

/-- A JavaScript number: `NaN`, or a finite value held exactly as a rational. -/
inductive JsNum where
  | nan
  | fin (q : Rat)
  deriving DecidableEq, Inhabited, Repr

namespace JsNum

instance (n : Nat) : OfNat JsNum n := ⟨fin (OfNat.ofNat n)⟩

/-- A decimal literal such as `0.9` denotes the double nearest to it, as in JavaScript. -/
instance : OfScientific JsNum := ⟨fun m s e => fin (Binary64.rd (OfScientific.ofScientific m s e))⟩

/-- `x + y` -/
@[inline] def add : JsNum → JsNum → JsNum
  | fin a, fin b => fin (Binary64.rd (a + b))
  | _, _ => nan

/-- `x - y` -/
@[inline] def sub : JsNum → JsNum → JsNum
  | fin a, fin b => fin (Binary64.rd (a - b))
  | _, _ => nan

/-- `x * y` -/
@[inline] def mul : JsNum → JsNum → JsNum
  | fin a, fin b => fin (Binary64.rd (a * b))
  | _, _ => nan

/-- `x / y`. Division by zero gives `NaN` (JavaScript: `±Infinity` or `NaN`). -/
@[inline] def div : JsNum → JsNum → JsNum
  | fin a, fin b => if b = 0 then nan else fin (Binary64.rd (a / b))
  | _, _ => nan

/-- `-x` -/
@[inline] def neg : JsNum → JsNum
  | fin a => fin (-a)
  | nan => nan

instance : Add JsNum := ⟨add⟩
instance : Sub JsNum := ⟨sub⟩
instance : Mul JsNum := ⟨mul⟩
instance : Div JsNum := ⟨div⟩
instance : Neg JsNum := ⟨neg⟩

/-! ### Comparisons. Every comparison involving `NaN` is `false`. -/

/-- `x < y` -/
@[inline] def lt : JsNum → JsNum → Bool
  | fin a, fin b => decide (a < b)
  | _, _ => false

/-- `x <= y` -/
@[inline] def le : JsNum → JsNum → Bool
  | fin a, fin b => decide (a ≤ b)
  | _, _ => false

/-- `x > y` -/
@[inline] def gt (x y : JsNum) : Bool := lt y x

/-- `x >= y` -/
@[inline] def ge (x y : JsNum) : Bool := le y x

/-- `x === y` (and `x == y` between numbers). `NaN === NaN` is `false`. -/
@[inline] def seq : JsNum → JsNum → Bool
  | fin a, fin b => decide (a = b)
  | _, _ => false

/-- `x !== y` -/
@[inline] def sne (x y : JsNum) : Bool := !(seq x y)

infix:50 " <ʲ " => JsNum.lt
infix:50 " ≤ʲ " => JsNum.le
infix:50 " >ʲ " => JsNum.gt
infix:50 " ≥ʲ " => JsNum.ge
infix:50 " =ʲ " => JsNum.seq
infix:50 " ≠ʲ " => JsNum.sne

/-- JavaScript truthiness of a number: `0` and `NaN` are falsy. -/
@[inline] def truthy : JsNum → Bool
  | fin a => a != 0
  | nan => false

/-- `isNaN(x)` -/
@[inline] def isNaN : JsNum → Bool
  | nan => true
  | fin _ => false

/-- `Math.min(x, y)`: `NaN` if either argument is `NaN`. -/
@[inline] def min : JsNum → JsNum → JsNum
  | fin a, fin b => fin (if a ≤ b then a else b)
  | _, _ => nan

/-- `Math.max(x, y)`: `NaN` if either argument is `NaN`. -/
@[inline] def max : JsNum → JsNum → JsNum
  | fin a, fin b => fin (if a ≤ b then b else a)
  | _, _ => nan

/-- `Math.min(x, y, z)` -/
@[inline] def min3 (x y z : JsNum) : JsNum := min (min x y) z

/-- `Math.max(x, y, z)` -/
@[inline] def max3 (x y z : JsNum) : JsNum := max (max x y) z

/-! ### Rounding -/

/-- The integer `Math.round` picks for a rational: the nearest integer, ties
    towards `+∞`. ECMAScript defines `Math.round(x)` as the integral value
    closest to `x`, choosing the one closer to `+∞` on a tie, which is
    exactly `⌊x + 1/2⌋`. -/
def roundInt (q : Rat) : Int := (q + 1/2).floor

/-- `Math.round(x)` -/
@[inline] def mathRound : JsNum → JsNum
  | fin a => fin (roundInt a)
  | nan => nan

/-- `Math.floor(x)` -/
@[inline] def mathFloor : JsNum → JsNum
  | fin a => fin a.floor
  | nan => nan

/-- The scale `Math.pow(10, digits)` used by oref0's `round`. -/
def pow10 : Nat → Rat
  | 0 => 1
  | n + 1 => 10 * pow10 n

/-- oref0's `round(value, digits)` helper
    (`lib/determine-basal/determine-basal.js` lines 21-26):
    `Math.round(value * 10^digits) / 10^digits`, with double arithmetic. -/
def round (value : JsNum) (digits : Nat := 0) : JsNum :=
  div (mathRound (mul value (fin (pow10 digits)))) (fin (pow10 digits))

/-- JavaScript `x % y` on numbers (remainder truncated towards zero). -/
def mod : JsNum → JsNum → JsNum
  | fin a, fin b =>
    if b = 0 then nan
    else
      let q := a / b
      let t : Int := if q < 0 then -((-q).floor) else q.floor
      fin (a - b * t)
  | _, _ => nan

/-- Value or `NaN`: how an `undefined` field behaves in arithmetic. -/
@[inline] def ofOpt : Option JsNum → JsNum
  | some x => x
  | none => nan

end JsNum

/-! ### Number formatting -/

namespace JsFmt

/-- Decimal digits of a natural number. -/
def natStr (n : Nat) : String := toString n

/-- Find `k ≤ bound` with `den ∣ 10^k`, i.e. the number of decimals needed to
    write a rational with this denominator exactly, if it terminates. -/
def decimalsNeeded (den : Nat) (bound : Nat := 40) : Option Nat :=
  go 0 bound
where
  go (k : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 => if (10 ^ k) % den = 0 then some k else go (k + 1) fuel

/-- Write `n / 10^k` (with `n ≥ 0`) in plain decimal notation, without trailing
    zeros after the point. -/
def fixedStr (n : Nat) (k : Nat) : String :=
  if k = 0 then natStr n
  else
    let s := natStr n
    let s := if s.length ≤ k then String.ofList (List.replicate (k + 1 - s.length) '0') ++ s else s
    let intPart := s.take (s.length - k)
    let fracPart := (s.drop (s.length - k)).toString
    let fracTrim := (fracPart.toList.reverse.dropWhile (· == '0')).reverse
    if fracTrim.isEmpty then intPart.toString else intPart.toString ++ "." ++ String.ofList fracTrim

/-- Round a non-negative rational to `k` decimals, ties away from zero (the
    behaviour of `Number.prototype.toFixed` on the exact value). Returns the
    scaled integer. -/
def roundHalfUpNat (q : Rat) (k : Nat) : Nat :=
  ((q * JsNum.pow10 k) + 1/2).floor.toNat

/-- `⌊log₁₀ a⌋` for `a > 0` (bounded search; doubles lie within 10^±325). -/
def flog10 (a : Rat) : Int :=
  if a ≥ 1 then (natStr a.floor.toNat).length - 1
  else go 1 400
where
  go (j : Nat) : Nat → Int
    | 0 => -(j : Int)
    | fuel + 1 => if a * JsNum.pow10 j ≥ 1 then -(j : Int) else go (j + 1) fuel

/-- `10^e` for an integer exponent. -/
def pow10Z (e : Int) : Rat := if 0 ≤ e then JsNum.pow10 e.toNat else 1 / JsNum.pow10 (-e).toNat

/-- The digits `s` (with `10^(k-1) ≤ s < 10^k`) and exponent `n` of ECMAScript's
    Number::toString for a positive double `a`: the smallest `k` such that
    `s · 10^(n−k)` rounds to `a`, choosing the `s` closest to `a` (ties to even). -/
def shortest (a : Rat) : Nat × Int :=
  go 1 17
where
  go (k : Nat) : Nat → Nat × Int
    | 0 => cand 17
    | fuel + 1 => let (sd, n) := cand k
                  if Binary64.rd ((sd : Rat) * pow10Z (n - k)) = a || k ≥ 17 then (sd, n) else go (k + 1) fuel
  cand (k : Nat) : Nat × Int :=
    let n := flog10 a + 1
    let sd := (Binary64.rhe (a / pow10Z (n - k))).toNat
    if sd ≥ 10 ^ k then (sd / 10, n + 1) else (sd, n)

/-- JavaScript `ToString(Number)` (ECMAScript Number::toString, radix 10). -/
def numToString : JsNum → String
  | .nan => "NaN"
  | .fin q =>
    if q = 0 then "0" else
    let sign := if q < 0 then "-" else ""
    let a := if q < 0 then -q else q
    let (sd, n) := shortest a
    let digits := (natStr sd).toList
    let k : Int := digits.length
    let body :=
      if k ≤ n && n ≤ 21 then String.ofList digits ++ String.ofList (List.replicate (n - k).toNat '0')
      else if 0 < n && n ≤ 21 then
        String.ofList (digits.take n.toNat) ++ "." ++ String.ofList (digits.drop n.toNat)
      else if -6 < n && n ≤ 0 then
        "0." ++ String.ofList (List.replicate (-n).toNat '0') ++ String.ofList digits
      else
        let e := n - 1
        let es := (if e ≥ 0 then "+" else "-") ++ natStr e.natAbs
        if k = 1 then String.ofList digits ++ "e" ++ es
        else String.ofList (digits.take 1) ++ "." ++ String.ofList (digits.drop 1) ++ "e" ++ es
    sign ++ body

/-- `x.toFixed(digits)` -/
def toFixed (x : JsNum) (digits : Nat) : String :=
  match x with
  | .nan => "NaN"
  | .fin q =>
    let neg := q < 0
    let a := if neg then -q else q
    let n := roundHalfUpNat a digits
    let s := natStr n
    let s := if s.length ≤ digits then String.ofList (List.replicate (digits + 1 - s.length) '0') ++ s else s
    let body := if digits = 0 then s
      else (s.take (s.length - digits)).toString ++ "." ++ (s.drop (s.length - digits)).toString
    (if neg then "-" else "") ++ body

end JsFmt

end LeanAID
