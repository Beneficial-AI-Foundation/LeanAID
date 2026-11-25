import LeanAID.Fixed.Rounding
import LeanAID.Fixed.Undated
import LeanAID.Fixed.MaxBasal
import LeanAID.Fixed.LowGlucose
import LeanAID.Fixed.SplitTimespan

/-!
# The corrected oref0: all five fixes together

**This is not oref0.** `LeanAID/Core` is the faithful transcription of oref0 0.7.1 and is
not changed. `determineBasalFixed` combines the fixes of F-04, F-11, F-12 and F-23, and
`generateFixed` (insulin on board) the fix of F-24. Each fix is the function of its own file;
in source order of `determine_basal`:

1. lines 138-143: a missing profile or `current_basal` is oref0's error (`stProfile`);
2. **F-12** (`Fixed/MaxBasal.lean`): without a positive `maxSafeBasal`, return `refuseF12`;
3. lines 145-423 with **F-11** (`Fixed/Undated.lean`): the prelude `dbPreludeF11`;
4. lines 428-903: oref0's predictions `dbPredict`;
5. lines 905-1188 with **F-23** (`Fixed/LowGlucose.lean`): `dbDosePatched`;
6. **F-04** (`Fixed/Rounding.lean`): at the exit, `capRate`.

`LeanAID.Fixed.ValidInputFixed` is `LeanAID.ValidInput` without the conditions that the F-12
fix makes unnecessary: `max_basal` and `max_daily_basal` may be missing or not numbers.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Fixed

open LeanAID JsNum

/-- `determine_basal` with the fixes of F-11, F-12 and F-23, before the F-04 step. -/
def determineBasalUncapped (inp : DBInputs) : Result :=
  match stProfile inp with
  | .error r => r
  | .ok p =>
    if maxSafeOk p then
      match dbPreludeF11 inp with
      | .error r => r
      | .ok pre => dbDosePatched (dbPredict inp pre)
    else refuseF12 inp p

/-- **The corrected `determine_basal`**: the fixes of F-04, F-11, F-12 and F-23. -/
def determineBasalFixed (inp : DBInputs) : Result :=
  match inp.profile with
  | some p => capRate p (determineBasalUncapped inp)
  | none => determineBasalUncapped inp

/-- **The corrected insulin on board** (`lib/iob/index.js` `generate`): the fix of F-24. -/
abbrev generateFixed (inp : Iob.HistoryInputs) (currentIOBOnly : Bool := false) : Iob.IobOut :=
  generateF24 inp currentIOBOnly

/-- Which triggers hold, in the order F-04, F-11, F-12, F-23 (for `aid-lean --fixed`). -/
def triggers (inp : DBInputs) : List String :=
  (if triggerF04 inp then ["F-04"] else []) ++ (if triggerF11 inp then ["F-11"] else []) ++
  (if triggerF12 inp then ["F-12"] else []) ++ (if triggerF23 inp then ["F-23"] else [])

/-! ### Valid input without the conditions the F-12 fix makes unnecessary -/

/-- `LeanAID.ValidProfile` with V2, V3 and V10 required only when `max_basal` and
    `max_daily_basal` are numbers. Every other condition is unchanged. -/
structure ValidProfileFixed (p : Profile) : Prop where
  current_basal : ∃ cb : Rat, p.current_basal = some (.fin cb) ∧ 0 < cb
  /-- V2, when `max_basal` is a number -/
  max_basal : ∀ mb cb : Rat, p.max_basal = some (.fin mb) → p.current_basal = some (.fin cb) → cb ≤ mb
  /-- V3, when `max_daily_basal` is a number -/
  max_daily_basal : ∀ mdb cb : Rat, p.max_daily_basal = some (.fin mdb) → p.current_basal = some (.fin cb) → cb ≤ mdb
  max_daily_safety_multiplier : ∀ x : Rat, p.max_daily_safety_multiplier = some (.fin x) → 1 ≤ x
  current_basal_safety_multiplier : ∀ x : Rat, p.current_basal_safety_multiplier = some (.fin x) → 1 ≤ x
  autosens_max : ∀ amax : Rat, p.autosens_max = some (.fin amax) → 0 < amax ∧
    (∃ n : Int, 0 ≤ n ∧ n ≤ 2 ^ 40 ∧ amax = Binary64.rd ((n : Rat) / 100)) ∧
    ∀ cb M : Rat, p.current_basal = some (.fin cb) → getMaxSafeBasal p = .fin M → cb * amax ≤ M
  max_iob : ∃ mi : Rat, p.max_iob = some (.fin mi) ∧ 0 ≤ mi
  bolus_increment : ∀ x : Rat, p.bolus_increment = some (.fin x) → 0 < x
  sens : ∃ s : Rat, p.sens = some (.fin s) ∧ 0 < s
  current_basal_double : ∀ cb : Rat, p.current_basal = some (.fin cb) → Binary64.rd cb = cb
  /-- V10, when `max_basal` is a number -/
  max_basal_double : ∀ mb : Rat, p.max_basal = some (.fin mb) → Binary64.rd mb = mb ∧ mb ≤ 2 ^ 30

/-- `LeanAID.ValidInput` with `ValidProfileFixed` for the profile. -/
structure ValidInputFixed (inp : DBInputs) : Prop where
  profile : ∃ p, inp.profile = some p ∧ ValidProfileFixed p
  autosens : ∀ p a, inp.profile = some p → inp.autosens_data = some a →
    ∃ r : Rat, a.ratio = some (.fin r) ∧ 0 < r ∧
      ∀ cb M : Rat, p.current_basal = some (.fin cb) → getMaxSafeBasal p = .fin M → cb * r ≤ M

end LeanAID.Fixed
