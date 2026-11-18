/-
  LeanAID.Core.JsNum — a model of the JavaScript numbers oref0 computes with.

  oref0 is written in JavaScript, where every number is an IEEE-754 double and
  where missing object fields (`undefined`) silently turn into `NaN` when used in
  arithmetic. oref0's own tests rely on this: they call `determine_basal` with
  objects that lack fields, and the algorithm carries `NaN` values through
  several branches. A faithful transcription therefore has to model `NaN`.

  We model a JavaScript number as either `NaN` or a *finite rational* held
  exactly (see `docs/DESIGN.md`, section "Numbers"). Arithmetic on finite values
  is exact rational arithmetic, i.e. the real-number result that the double
  computation approximates. Known, documented differences from JavaScript:

  * Division by zero yields `NaN` here; JavaScript yields `±Infinity` for a
    non-zero numerator. Valid inputs never divide by zero (`docs/DESIGN.md`).
  * Doubles round every intermediate result; we do not. Results can differ when
    a value lands exactly on a rounding tie (e.g. `Math.round(x*100)` for an
    `x` whose double is just below `.xx5`). The differential tester measures
    how often this happens.
  * Negative zero is not modelled (`-0 === 0` in JavaScript, and it prints as
    `0`, so it is unobservable in oref0's outputs).

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

/-- Decimal literals such as `0.9` denote the exact rational `9/10`. -/
instance : OfScientific JsNum := ⟨fun m s e => fin (OfScientific.ofScientific m s e)⟩

/-- `x + y` -/
@[inline] def add : JsNum → JsNum → JsNum
  | fin a, fin b => fin (a + b)
  | _, _ => nan

/-- `x - y` -/
@[inline] def sub : JsNum → JsNum → JsNum
  | fin a, fin b => fin (a - b)
  | _, _ => nan

/-- `x * y` -/
@[inline] def mul : JsNum → JsNum → JsNum
  | fin a, fin b => fin (a * b)
  | _, _ => nan

/-- `x / y`. Division by zero gives `NaN` (JavaScript: `±Infinity` or `NaN`). -/
@[inline] def div : JsNum → JsNum → JsNum
  | fin a, fin b => if b = 0 then nan else fin (a / b)
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
    `Math.round(value * 10^digits) / 10^digits`. -/
def round (value : JsNum) (digits : Nat := 0) : JsNum :=
  match value with
  | fin a => fin ((roundInt (a * pow10 digits) : Rat) / pow10 digits)
  | nan => nan

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

/-- JavaScript `ToString(Number)` for our model. Exact for every value whose
    decimal expansion terminates within 17 significant digits (all values oref0
    prints after rounding); otherwise prints 16 significant digits, which can
    differ from JavaScript's shortest round-trip form in the last digit. -/
def numToString : JsNum → String
  | .nan => "NaN"
  | .fin q =>
    if q = 0 then "0" else
    let sign := if q < 0 then "-" else ""
    let a := if q < 0 then -q else q
    match decimalsNeeded a.den with
    | some k =>
      if k ≤ 20 then sign ++ fixedStr (a * JsNum.pow10 k).floor.toNat k
      else sign ++ fixedStr (roundHalfUpNat a 20) 20
    | none =>
      -- 16 significant digits (JavaScript prints the shortest form, 16 or 17)
      let intDigits := (natStr a.floor.toNat).length
      let k := if a ≥ 1 then 16 - min 16 intDigits else 15 + (natStr (1 / a).floor.toNat).length
      sign ++ fixedStr (roundHalfUpNat a k) k

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
