import LeanAID.Proofs.Prelude

/-!
# Issued rates are doubles

**Objects.**
- `RateDouble.Dbl x`: a JavaScript number `x` that is finite is a double (`Binary64.rd q = q`).
- `RateDouble.RateDbl res`: the rate of `res`, when finite, is a double.

**Theorem.**
- `rate_double`: every finite rate that `determineBasal inp` returns is a double, for every
  input `inp`.

**Proof.** `RateOk res base` states that the rate of `res` is `base` or `res` satisfies
`RateDbl`. Every finite rate the model writes is `0`, a result of `roundBasal` or a result of
`rnd`, and the last two end in a rounded division. Every branch of `dbDose` preserves
`RateOk`, the result that enters `dbDose` has no rate, and every error result of `dbPrelude`
satisfies `RateDbl`.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Proofs

open LeanAID JsNum

namespace RateDouble

/-- A finite JavaScript number `x` is a double. -/
def Dbl (x : JsNum) : Prop := ∀ q : Rat, x = .fin q → Binary64.rd q = q

/-- The rate of `res`, when finite, is a double. -/
def RateDbl (res : Result) : Prop := ∀ q : Rat, res.rate = some (.fin q) → Binary64.rd q = q

/-- The rate of `res` is `base`, or `res` satisfies `RateDbl`. -/
def RateOk (res : Result) (base : Option JsNum) : Prop := res.rate = base ∨ RateDbl res

theorem dbl_zero : Dbl 0 := by
  intro q h; cases h; exact Binary64.rd_zero

theorem dbl_div (x : JsNum) (s : Rat) : Dbl (JsNum.div x (.fin s)) := by
  intro q h
  cases x with
  | nan => cases h
  | fin a =>
    simp only [JsNum.div] at h
    split at h
    · cases h
    · cases h; exact Binary64.rd_rd _

/-- Let `b` be a JavaScript number and `m` a pump model. Then `Dbl (roundBasal b m)`. -/
theorem dbl_roundBasal (b : JsNum) (m : Option String) : Dbl (roundBasal b m) := by
  unfold roundBasal roundToScale
  split
  · exact dbl_div _ _
  · split <;> exact dbl_div _ _

/-- Let `v` be a JavaScript number and `d` a number of digits. Then `Dbl (rnd v d)`. -/
theorem dbl_rnd (v : JsNum) (d : Nat) : Dbl (rnd v d) := dbl_div _ _

theorem rateOk_of_dbl {res : Result} {base : Option JsNum} (h : RateDbl res) : RateOk res base :=
  Or.inr h

theorem rateDbl_of_none {res : Result} (h : res.rate = none) : RateDbl res := by
  intro q hq; rw [h] at hq; cases hq

theorem rateOk_trans {res rT : Result} (h : RateOk res rT.rate) (h0 : rT.rate = none) : RateDbl res := by
  rcases h with h | h
  · exact rateDbl_of_none (h.trans h0)
  · exact h

@[simp] theorem addReasonIf_rate (r : Result) (b : Bool) (s : String) :
    (r.addReasonIf b s).rate = r.rate := by
  unfold Result.addReasonIf; cases b <;> rfl

/-- Let `rate` and `dur` be JavaScript numbers, `p` a profile, `rT` a result and `ct` an
    optional running temp. Then `RateOk (setTempBasal rate dur p rT ct) rT.rate`. -/
theorem stb_rateOk (rate dur : JsNum) (p : Profile) (rT : Result) (ct : Option CurrentTemp) :
    RateOk (setTempBasal rate dur p rT ct) rT.rate := by
  have hr := dbl_roundBasal (clampRate rate (getMaxSafeBasal p)) p.model
  unfold setTempBasal
  simp only
  cases keepRunning (roundBasal (clampRate rate (getMaxSafeBasal p)) p.model) dur ct with
  | some v => exact Or.inl rfl
  | none =>
    simp only
    split
    · split
      · split
        · right; intro q hq
          simp only [Option.some.injEq] at hq
          exact dbl_zero q hq
        · left; rfl
      · right; intro q hq
        simp only [Option.some.injEq] at hq
        exact hr q hq
    · right; intro q hq
      simp only [Option.some.injEq] at hq
      exact hr q hq

theorem neutralTemp_rateOk (c : Ctx) (rT : Result) : RateOk (neutralTemp c rT) rT.rate := by
  unfold neutralTemp
  split
  · exact Or.inl rfl
  · exact stb_rateOk _ _ _ _ _

theorem lowEventualBG_rateOk (c : Ctx) (rT : Result) : RateOk (lowEventualBG c rT) rT.rate := by
  unfold lowEventualBG
  simp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact stb_rateOk _ _ _ _ _
    | exact neutralTemp_rateOk _ _

theorem highTempSet_rateOk (c : Ctx) (rT : Result) (rate ir : JsNum) :
    RateOk (highTempSet c rT rate ir) rT.rate := by
  unfold highTempSet
  simp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact stb_rateOk _ _ _ _ _

/-- Let `basal` and `d` be JavaScript numbers. Then the rate `(smbLowTemp basal d).2` of the
    SMB low temp (`determine-basal.js:1111-1122`) satisfies `Dbl`. -/
theorem dbl_smbLowTemp (basal d : JsNum) : Dbl (smbLowTemp basal d).2 := by
  unfold smbLowTemp
  split
  · exact dbl_zero
  · split
    · exact dbl_zero
    · exact dbl_rnd _ _

theorem highTemp_rateOk (c : Ctx) (rT : Result) : RateOk (highTemp c rT) rT.rate := by
  unfold highTemp
  simp only
  generalize hs : (if (c.microBolusAllowed && c.enableSMB && c.bg >ʲ c.threshold) = true then _ else _) = s
  cases s with
  | inl res =>
    split at hs
    · unfold smbBlock smbFinish at hs
      split at hs
      · injection hs with hs; subst hs
        right; intro q hq
        simp only [Option.some.injEq] at hq
        exact dbl_smbLowTemp _ _ q hq
      · cases hs
    · cases hs
  | inr rT' =>
    have hd : rT'.rate = rT.rate := by
      split at hs
      · unfold smbBlock smbFinish at hs
        split at hs
        · cases hs
        · injection hs with hs; subst hs
          simp [smbReasonUnits]
      · injection hs with hs; subst hs; simp
    simp only
    repeat' split
    all_goals
      rcases highTempSet_rateOk c _ _ _ with h | h
      · left; rw [h]; (try simp only [addReason_rate]); exact hd
      · right; exact h

theorem dbDoseRest_rateOk (c : Ctx) (rT : Result) : RateOk (dbDose.dbDoseRest c rT) rT.rate := by
  unfold dbDose.dbDoseRest
  simp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact stb_rateOk _ _ _ _ _
    | exact neutralTemp_rateOk _ _
    | exact lowEventualBG_rateOk _ _
    | exact highTemp_rateOk _ _

theorem dbDose_rateOk (c : Ctx) : RateOk (dbDose c) c.rT.rate := by
  unfold dbDose
  simp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact dbDoseRest_rateOk _ _
    | exact stb_rateOk _ _ _ _ _

theorem cgmResult_rateDbl (inp : DBInputs) (p : Profile) (g : GluVals) : RateDbl (cgmResult inp p g) := by
  unfold cgmResult
  split
  · exact rateDbl_of_none rfl
  · simp only
    split
    · intro q hq
      simp only [Option.some.injEq] at hq
      exact dbl_roundBasal _ _ q hq
    · split
      · intro q hq
        simp only [Option.some.injEq] at hq
        exact dbl_zero q hq
      · exact rateDbl_of_none (by simp)

/-- Let `inp` be an input and `e` a result with `dbPrelude inp = .error e`
    (`determine-basal.js:128-423`). Then `RateDbl e`. -/
theorem prelude_error_rateDbl {inp : DBInputs} {e : Result} (h : dbPrelude inp = .error e) :
    RateDbl e := by
  exact prelude_error_induction h RateDbl
    (fun _ hr _ => rateDbl_of_none hr)
    (fun p _ g => cgmResult_rateDbl inp p g)
    (fun _ _ _ _ hr _ => rateOk_trans (stb_rateOk _ _ _ _ _) hr)

end RateDouble

open RateDouble in
/-- Let `inp` be an input and `x` a rational with `(determineBasal inp).rate = some (.fin x)`.
    Then `Binary64.rd x = x`: `x` is fixed by the model's binary64 rounding, whose exponent
    is unbounded, so `x` need not be a finite IEEE-754 double. -/
theorem rate_double {inp : DBInputs} {x : Rat} (h : (determineBasal inp).rate = some (.fin x)) :
    Binary64.rd x = x := by
  revert h
  unfold determineBasal
  cases hpre : dbPrelude inp with
  | error e => exact prelude_error_rateDbl hpre x
  | ok pre => exact rateOk_trans (dbDose_rateOk _) rfl x

end LeanAID.Proofs
