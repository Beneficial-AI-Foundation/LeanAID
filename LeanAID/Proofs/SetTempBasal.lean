/-
  LeanAID.Proofs.SetTempBasal — properties of `tempBasalFunctions.setTempBasal`
  (`lib/basal-set-temp.js`), the function through which almost every temp basal
  that oref0 issues passes.
-/
import LeanAID.Core.BasalSetTemp
import LeanAID.Proofs.Rounding

namespace LeanAID.Proofs

open JsNum

@[simp] theorem addReason_rate (r : Result) (s : String) : (r.addReason s).rate = r.rate := rfl
@[simp] theorem addReason_units (r : Result) (s : String) : (r.addReason s).units = r.units := rfl
@[simp] theorem addReason_duration (r : Result) (s : String) : (r.addReason s).duration = r.duration := rfl
@[simp] theorem setReason_rate (r : Result) (s : String) : (r.setReason s).rate = r.rate := rfl
@[simp] theorem setReason_units (r : Result) (s : String) : (r.setReason s).units = r.units := rfl
@[simp] theorem reasonMsg_rate (r : Result) (s : String) : (r.reasonMsg s).rate = r.rate := rfl
@[simp] theorem reasonMsg_units (r : Result) (s : String) : (r.reasonMsg s).units = r.units := rfl
@[simp] theorem reasonMsg_duration (r : Result) (s : String) : (r.reasonMsg s).duration = r.duration := rfl

@[simp] theorem ite_addReason_rate (c : Prop) [Decidable c] (r : Result) (s : String) :
    (if c then r.addReason s else r).rate = r.rate := by split <;> rfl
@[simp] theorem ite_addReason_units (c : Prop) [Decidable c] (r : Result) (s : String) :
    (if c then r.addReason s else r).units = r.units := by split <;> rfl

/-- The clamp of basal-set-temp.js lines 24-28 keeps a finite rate within
    `[0, maxSafeBasal]` (for a non-negative `maxSafeBasal`). -/
theorem clampRate_fin {x M : Rat} (hM : 0 ≤ M) :
    ∃ c, clampRate (.fin x) (.fin M) = .fin c ∧ 0 ≤ c ∧ c ≤ M := by
  unfold clampRate
  by_cases h0 : x < 0
  · exact ⟨0, by simp [h0], Rat.le_refl, hM⟩
  · by_cases h1 : M < x
    · refine ⟨M, ?_, hM, Rat.le_refl⟩
      simp [JsNum.lt, JsNum.gt, h0, h1]
    · refine ⟨x, ?_, by grind, by grind⟩
      simp [JsNum.lt, JsNum.gt, h0, h1]

theorem clampRate_nan (M : JsNum) : clampRate .nan M = .nan := by
  simp [clampRate, JsNum.lt, JsNum.gt]

/-- `setTempBasal` never touches `units`. -/
@[simp] theorem setTempBasal_units (rate dur : JsNum) (p : Profile) (rT : Result) (ct : Option CurrentTemp) :
    (setTempBasal rate dur p rT ct).units = rT.units := by
  simp only [setTempBasal]
  cases keepRunning (roundBasal (clampRate rate (getMaxSafeBasal p)) p.model) dur ct with
  | some v => rfl
  | none =>
    simp only
    split
    · split
      · split <;> rfl
      · rfl
    · rfl

/-- The rate `setTempBasal` would set: the request clamped to
    `[0, maxSafeBasal]` and rounded with `round_basal`. -/
def suggestedRate (rate : JsNum) (p : Profile) : JsNum :=
  roundBasal (clampRate rate (getMaxSafeBasal p)) p.model

/-- `setTempBasal` either leaves the rate of `rT` as it was (a running temp is
    close enough, or "doing nothing" in skip-neutral mode), cancels (rate 0),
    or sets the clamped and rounded request. -/
theorem setTempBasal_rate_cases (rate dur : JsNum) (p : Profile) (rT : Result) (ct : Option CurrentTemp) :
    (setTempBasal rate dur p rT ct).rate = rT.rate ∨
    (setTempBasal rate dur p rT ct).rate = some 0 ∨
    (setTempBasal rate dur p rT ct).rate = some (suggestedRate rate p) := by
  simp only [setTempBasal, suggestedRate]
  cases keepRunning (roundBasal (clampRate rate (getMaxSafeBasal p)) p.model) dur ct with
  | some v => left; rfl
  | none =>
    simp only
    split
    · split
      · split
        · right; left; rfl
        · left; rfl
      · right; right; rfl
    · right; right; rfl

/-- The suggested rate of a finite request is within `[0, round_basal(maxSafeBasal)]`. -/
theorem suggestedRate_bound {rate : JsNum} {p : Profile} {M r : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) (h : suggestedRate rate p = .fin r) :
    0 ≤ r ∧ r ≤ rbR M p.model := by
  unfold suggestedRate at h
  rw [hM] at h
  cases rate with
  | nan => rw [clampRate_nan, roundBasal_nan] at h; cases h
  | fin x =>
    obtain ⟨c, hc, hc0, hcM⟩ := clampRate_fin (x := x) hM0
    rw [hc, roundBasal_fin] at h
    cases h
    exact ⟨rbR_nonneg _ hc0, rbR_mono _ hcM⟩

/-- **H1 for setTempBasal.** A finite rate issued by `setTempBasal` is within
    `[0, round_basal(maxSafeBasal)]`, unless it is the rate `rT` already had. -/
theorem setTempBasal_rate_bound {rate dur : JsNum} {p : Profile} {rT : Result} {ct : Option CurrentTemp}
    {M r : Rat} (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M)
    (h : (setTempBasal rate dur p rT ct).rate = some (.fin r)) :
    rT.rate = some (.fin r) ∨ (0 ≤ r ∧ r ≤ rbR M p.model) := by
  rcases setTempBasal_rate_cases rate dur p rT ct with h1 | h1 | h1
  · left; rw [← h1]; exact h
  · right; rw [h1] at h
    have h2 : (0 : JsNum) = .fin r := Option.some.inj h
    have : r = 0 := by injection h2 with h3; exact h3.symm
    subst this; exact ⟨Rat.le_refl, rbR_nonneg _ hM0⟩
  · right; rw [h1] at h; exact suggestedRate_bound hM hM0 (Option.some.inj h)

/-- `setTempBasal(0, ...)` issues 0 or nothing (for a non-negative `maxSafeBasal`). -/
theorem setTempBasal_zero_rate {dur : JsNum} {p : Profile} {rT : Result} {ct : Option CurrentTemp}
    {M : Rat} (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) :
    (setTempBasal 0 dur p rT ct).rate = rT.rate ∨ (setTempBasal 0 dur p rT ct).rate = some 0 := by
  have hs : suggestedRate 0 p = 0 := by
    unfold suggestedRate; rw [hM]
    have : clampRate (0 : JsNum) (.fin M) = .fin 0 := by
      show clampRate (.fin 0) (.fin M) = .fin 0
      simp [clampRate, JsNum.lt, JsNum.gt]; grind
    rw [this, roundBasal_fin, rbR_zero]; rfl
  rcases setTempBasal_rate_cases 0 dur p rT ct with h1 | h1 | h1
  · left; exact h1
  · right; exact h1
  · right; rw [h1, hs]

end LeanAID.Proofs
