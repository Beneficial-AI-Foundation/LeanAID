/-
  LeanAID.Spec.Valid — what "valid input" means for the safety theorems.

  Every condition is a plain statement about the JSON inputs of
  `oref0-determine-basal`. The justification of each is in `docs/DESIGN.md`,
  section "Valid input". Conditions that the theorems do not need are not
  imposed: in particular glucose values, deltas, IOB and meal data may be
  anything (missing, NaN, negative, huge) unless a theorem says otherwise.
-/
import LeanAID.Core.DetermineBasal

namespace LeanAID

/-- A valid profile. -/
structure ValidProfile (p : Profile) : Prop where
  /-- `current_basal` is a positive number (V1) -/
  current_basal : ∃ cb : Rat, p.current_basal = some (.fin cb) ∧ 0 < cb
  /-- `max_basal` is a number at least `current_basal` (V2) -/
  max_basal : ∃ mb cb : Rat, p.max_basal = some (.fin mb) ∧ p.current_basal = some (.fin cb) ∧ cb ≤ mb
  /-- `max_daily_basal` (the largest scheduled rate) is at least `current_basal` (V3) -/
  max_daily_basal : ∃ mdb cb : Rat, p.max_daily_basal = some (.fin mdb) ∧ p.current_basal = some (.fin cb) ∧ cb ≤ mdb
  /-- the safety multipliers, when set to a number, are at least 1 (V4) -/
  max_daily_safety_multiplier : ∀ x : Rat, p.max_daily_safety_multiplier = some (.fin x) → 1 ≤ x
  current_basal_safety_multiplier : ∀ x : Rat, p.current_basal_safety_multiplier = some (.fin x) → 1 ≤ x
  /-- `autosens_max`, when it is a number, is positive, is (the double nearest to) a
      number with at most two decimals, and the basal rate scaled by it is within
      `maxSafeBasal` (V5) -/
  autosens_max : ∀ amax : Rat, p.autosens_max = some (.fin amax) → 0 < amax ∧
    (∃ n : Int, 0 ≤ n ∧ n ≤ 2 ^ 40 ∧ amax = Binary64.rd ((n : Rat) / 100)) ∧
    ∀ cb M : Rat, p.current_basal = some (.fin cb) → getMaxSafeBasal p = .fin M → cb * amax ≤ M
  /-- `max_iob` is a non-negative number (V6) -/
  max_iob : ∃ mi : Rat, p.max_iob = some (.fin mi) ∧ 0 ≤ mi
  /-- `bolus_increment`, when set to a number, is positive (V7) -/
  bolus_increment : ∀ x : Rat, p.bolus_increment = some (.fin x) → 0 < x
  /-- `sens` (ISF) is a positive number (V8) -/
  sens : ∃ s : Rat, p.sens = some (.fin s) ∧ 0 < s
  /-- `current_basal` and `max_basal` are doubles, as every number parsed from JSON
      is, and `max_basal` is at most 2^30 U/h (V10; see DESIGN, "Valid input") -/
  current_basal_double : ∀ cb : Rat, p.current_basal = some (.fin cb) → Binary64.rd cb = cb
  max_basal_double : ∀ mb : Rat, p.max_basal = some (.fin mb) → Binary64.rd mb = mb ∧ mb ≤ 2 ^ 30

/-- Valid input to `determine_basal`. -/
structure ValidInput (inp : DBInputs) : Prop where
  /-- a valid profile is given (V0) -/
  profile : ∃ p, inp.profile = some p ∧ ValidProfile p
  /-- the autosens ratio, when autosens data is given, is a positive number, and the
      basal rate scaled by it is within `maxSafeBasal` (V9) -/
  autosens : ∀ p a, inp.profile = some p → inp.autosens_data = some a →
    ∃ r : Rat, a.ratio = some (.fin r) ∧ 0 < r ∧
      ∀ cb M : Rat, p.current_basal = some (.fin cb) → getMaxSafeBasal p = .fin M → cb * r ≤ M

end LeanAID
