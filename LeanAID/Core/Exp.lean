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
import Std.Data.HashMap

namespace LeanAID.Exp

/-- Round a non-negative rational down to a multiple of 2^-128. -/
def trunc128 (q : Rat) : Rat :=
  let s : Rat := (2 : Rat) ^ 128
  ((q * s).floor : Rat) / s

/-- Taylor polynomial `Σ_{i ≤ n} y^i / i!`, by Horner's rule on rationals (the
    reference form; `taylor` computes the same value faster). -/
def taylorHorner (y : Rat) (n : Nat) : Rat :=
  horner n 1
where
  /-- `horner m acc` evaluates `1 + y/1 (1 + y/2 (... (1 + y/m · acc)))`. -/
  horner : Nat → Rat → Rat
    | 0, acc => acc
    | m + 1, acc => horner m (1 + y / (m + 1 : Nat) * acc)

/-- The same polynomial `Σ_{i ≤ n} y^i / i!` with integers: for `y = a/b`,
    `(Σ_i a^i · b^(n-i) · n!/i!) / (b^n · n!)`. Both forms are exact, so they denote
    the same rational; this one normalises a fraction once instead of `n` times
    (about 10x faster, which the closed-loop simulation needs, sim/). The IOB
    conformance cases (`iob_exact`) and the per-step IOB comparison with oref0 in the
    simulation check it; the equality is not proved. -/
def taylor (y : Rat) (n : Nat) : Rat :=
  let a := y.num
  let b : Int := y.den
  -- i runs from n down to 0: acc ← acc·a + (n!/i!)·b^(n-i)
  let rec go : Nat → Int → Int → Int → Int
    | i, acc, c, bp =>
      let acc := acc * a + c * bp
      match i with
      | 0 => acc
      | i + 1 => go i acc (c * (i + 1)) (bp * b)
  let fact : Int := (List.range n).foldl (fun f i => f * (i + 1 : Nat)) 1
  (go n 0 1 1 : Rat) / ((b ^ n * fact : Int) : Rat)

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

/-! ### A lookup table for the compiled code

The exponential insulin curves call `Math.exp` with few distinct arguments
(calculate.js lines 125-128: `-end/tau`, and `-minsAgo/tau` for whole minutes
`minsAgo ≤ end`), but very often: twice per dose and per point of the 4-hour IOB
curve. `jsExpFast` looks these values up in a table filled by `jsExp` itself, and
`jsExp_eq_jsExpFast` proves that it equals `jsExp`; as a `@[csimp]` lemma it makes the
compiled code use the table (needed for the closed-loop simulation, sim/). -/

/-- The arguments: DIA 5 to 8 h, peak times 55 and 75 min, computed with the same
    JavaScript arithmetic as `Iob.iobCalcExponential`. -/
def jsExpArgs : List Rat :=
  ([5, 6, 7, 8] : List Nat).flatMap fun d => ([55, 75] : List Nat).flatMap fun pk =>
    let end_ : JsNum := .fin ((d * 60 : Nat) : Rat)
    let peak : JsNum := .fin ((pk : Nat) : Rat)
    let tau := peak * (1 - peak / end_) / (1 - 2 * peak / end_)
    ((-end_ / tau) :: (List.range (d * 60 + 1)).map (fun (k : Nat) => -(JsNum.fin ((k : Int) : Rat)) / tau)).filterMap
      fun x => match x with | .fin q => some q | .nan => none

def jsExpInsert (m : Std.HashMap (Int × Nat) JsNum) (q : Rat) : Std.HashMap (Int × Nat) JsNum :=
  m.insert (q.num, q.den) (jsExp (.fin q))

def jsExpTable : Std.HashMap (Int × Nat) JsNum := jsExpArgs.foldl jsExpInsert ∅

def jsExpLookup (x : Rat) : Option JsNum := jsExpTable[(x.num, x.den)]?

/-- `jsExp`, looking the value up in `jsExpTable` first. -/
def jsExpFast : JsNum → JsNum
  | .fin x => (jsExpLookup x).getD (jsExp (.fin x))
  | .nan => .nan

private def TableOk (m : Std.HashMap (Int × Nat) JsNum) : Prop :=
  ∀ k v, m[k]? = some v → ∃ q : Rat, (q.num, q.den) = k ∧ v = jsExp (.fin q)

private theorem tableOk_foldl (l : List Rat) (m : Std.HashMap (Int × Nat) JsNum) (h : TableOk m) :
    TableOk (l.foldl jsExpInsert m) := by
  induction l generalizing m with
  | nil => exact h
  | cons q l ih =>
    apply ih
    intro k v hk
    unfold jsExpInsert at hk
    rw [Std.HashMap.getElem?_insert] at hk
    split at hk
    · rename_i hq
      have hq : (q.num, q.den) = k := by simpa using hq
      exact ⟨q, hq, (Option.some.inj hk).symm⟩
    · exact h k v hk

private theorem jsExpTable_ok : TableOk jsExpTable :=
  tableOk_foldl _ _ (by intro k v h; simp at h)

@[csimp] theorem jsExp_eq_jsExpFast : @jsExp = @jsExpFast := by
  funext v
  cases v with
  | nan => rfl
  | fin x =>
    show jsExp (.fin x) = (jsExpLookup x).getD (jsExp (.fin x))
    cases hw : jsExpLookup x with
    | none => rfl
    | some w =>
      unfold jsExpLookup at hw
      obtain ⟨q, hq, rfl⟩ := jsExpTable_ok _ _ hw
      have : q = x := by
        simp only [Prod.mk.injEq] at hq
        exact Rat.ext hq.1 hq.2
      rw [this]; rfl

end LeanAID.Exp
