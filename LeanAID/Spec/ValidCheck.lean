/-
  LeanAID.Spec.ValidCheck — a decision procedure for `ValidInput`, used to show
  that concrete inputs (oref0's test inputs) are valid. Soundness is proved in
  `LeanAID/Proofs/ValidCheck.lean`.
-/
import LeanAID.Spec.Valid

namespace LeanAID

/-- `x` is the double nearest to a number `n/100` with `0 ≤ n ≤ 2^40`. -/
def twoDecimals (x : Rat) : Bool :=
  let n := JsNum.roundInt (x * 100)
  decide (0 ≤ n) && decide (n ≤ 2 ^ 40) && decide (Binary64.rd ((n : Rat) / 100) = x)

/-- `x` is a double. -/
def isDouble (x : Rat) : Bool := decide (Binary64.rd x = x)

/-- The finite value of a `getMaxSafeBasal`, if any. -/
def finOf : JsNum → Option Rat
  | .fin x => some x
  | .nan => none

def multOk : Option JsNum → Bool
  | some (.fin x) => decide (1 ≤ x)
  | _ => true

def validProfileB (p : Profile) : Bool :=
  match p.current_basal, p.max_basal, p.max_daily_basal, finOf (getMaxSafeBasal p), p.max_iob, p.sens with
  | some (.fin cb), some (.fin mb), some (.fin mdb), some M, some (.fin mi), some (.fin s) =>
    decide (0 < cb) && decide (cb ≤ mb) && decide (cb ≤ mdb) &&
    multOk p.max_daily_safety_multiplier && multOk p.current_basal_safety_multiplier &&
    (match p.autosens_max with
     | some (.fin amax) => decide (0 < amax) && twoDecimals amax && decide (cb * amax ≤ M)
     | _ => true) &&
    decide (0 ≤ mi) &&
    (match p.bolus_increment with
     | some (.fin x) => decide (0 < x)
     | _ => true) &&
    decide (0 < s) &&
    isDouble cb && isDouble mb && decide (mb ≤ 2 ^ 30)
  | _, _, _, _, _, _ => false

def validInputB (inp : DBInputs) : Bool :=
  match inp.profile with
  | none => false
  | some p =>
    validProfileB p &&
    (match inp.autosens_data with
     | none => true
     | some a =>
       match a.ratio, p.current_basal, finOf (getMaxSafeBasal p) with
       | some (.fin r), some (.fin cb), some M => decide (0 < r) && decide (cb * r ≤ M)
       | _, _, _ => false)

end LeanAID
