/-
  LeanAID.Proofs.Prelude — facts about lines 128-423 of determine_basal
  (`dbPrelude` and its stages) and about `dbPredict`.
-/
import LeanAID.Core.DetermineBasal
import LeanAID.Proofs.SetTempBasal

namespace LeanAID.Proofs

open JsNum

/-- What a successful prelude passes on. -/
theorem prelude_ok {inp : DBInputs} {pre : Pre} (h : dbPrelude inp = .ok pre) :
    ∃ p g mm io ct meal, stProfile inp = .ok p ∧ stGlucose inp p = .ok g ∧ stTargets p = .ok mm ∧
      stIob inp = .ok io ∧ stPumpHistory inp p io.1 = .ok ct ∧ stMeal inp = .ok meal ∧
      pre.p = p ∧ pre.ct = ct ∧ pre.iobd = io.1 ∧ pre.bg = g.bg ∧ pre.minDelta = g.minDelta ∧
      pre.sensitivityRatio = sensitivityRatioOf p inp.autosens_data ((mm.1 + mm.2) / 2) ∧
      pre.basal = adjustedBasal p (sensitivityRatioOf p inp.autosens_data ((mm.1 + mm.2) / 2)) ∧
      pre.max_iob = p.max_iob.js ∧ pre.gs = g.gs := by
  unfold dbPrelude at h
  cases h1 : stProfile inp <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rename_i p
  cases h2 : stGlucose inp p <;> simp only [h2] at h
  · cases h
  rename_i g
  cases h3 : stTargets p <;> simp only [h3] at h
  · cases h
  rename_i mm
  cases h4 : stIob inp <;> simp only [h4] at h
  · cases h
  rename_i io
  cases h5 : stPumpHistory inp p io.1 <;> simp only [h5] at h
  · cases h
  rename_i ct
  cases h6 : stEventual inp (eventualVals g p (sensOf p inp.autosens_data
      (sensitivityRatioOf p inp.autosens_data ((mm.1 + mm.2) / 2))) io.1) <;> simp only [h6] at h
  · cases h
  cases h7 : stMeal inp <;> simp only [h7, pure, Except.pure] at h
  · cases h
  rename_i meal
  cases h
  refine ⟨p, g, mm, io, ct, meal, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
    first | rfl | assumption

theorem stProfile_ok {inp : DBInputs} {p : Profile} (h : stProfile inp = .ok p) : inp.profile = some p := by
  unfold stProfile at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; assumption

/-- The CGM-error branch (lines 198-221) issues the unadjusted basal, 0, or nothing,
    and never a microbolus. -/
theorem cgmResult_rate (inp : DBInputs) (p : Profile) (g : GluVals) :
    (cgmResult inp p g).units = none ∧
    ((cgmResult inp p g).rate = none ∨ (cgmResult inp p g).rate = some 0 ∨
      (cgmResult inp p g).rate = some (profileCurrentBasal p)) := by
  unfold cgmResult
  split
  · exact ⟨rfl, Or.inl rfl⟩
  · simp only
    split
    · exact ⟨rfl, Or.inr (Or.inr rfl)⟩
    · split
      · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨rfl, Or.inl rfl⟩

/-- An early return of lines 369-392: a TypeError, or a cancelling `setTempBasal(0, 0)`. -/
theorem stPumpHistory_error {inp : DBInputs} {p : Profile} {iobd : IobTick} {e : Result}
    (h : stPumpHistory inp p iobd = .error e) :
    e = typeError "duration" ∨
    ∃ rT ct, rT.rate = none ∧ rT.units = none ∧ e = setTempBasal 0 0 p rT (some ct) := by
  unfold stPumpHistory at h
  cases hct : inp.currenttemp with
  | none => simp [hct] at h; exact Or.inl h.symm
  | some ct =>
    cases hlt : iobd.lastTemp with
    | none => simp [hct, hlt] at h
    | some lt =>
      simp only [hct, hlt] at h
      split at h
      · simp at h; exact Or.inr ⟨_, ct, rfl, rfl, h.symm⟩
      · split at h
        · simp at h; exact Or.inr ⟨_, ct, rfl, rfl, h.symm⟩
        · simp at h

theorem stPumpHistory_ok {inp : DBInputs} {p : Profile} {iobd : IobTick} {ct : CurrentTemp}
    (h : stPumpHistory inp p iobd = .ok ct) : inp.currenttemp = some ct := by
  unfold stPumpHistory at h
  cases hct : inp.currenttemp with
  | none => simp [hct] at h
  | some c =>
    cases hlt : iobd.lastTemp with
    | none => simp [hct, hlt] at h; rw [h]
    | some lt =>
      simp only [hct, hlt] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h; rw [h]

/-- When the prelude succeeds, IOB is a finite number: a missing or NaN IOB makes
    eventualBG NaN, and oref0 returns an error (lines 419-422). -/
theorem prelude_iob_fin {inp : DBInputs} {pre : Pre} (h : dbPrelude inp = .ok pre) :
    ∃ i : Rat, pre.iobd.iob = some (.fin i) := by
  unfold dbPrelude at h
  cases h1 : stProfile inp <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rename_i p
  cases h2 : stGlucose inp p <;> simp only [h2] at h
  · cases h
  rename_i g
  cases h3 : stTargets p <;> simp only [h3] at h
  · cases h
  rename_i mm
  cases h4 : stIob inp <;> simp only [h4] at h
  · cases h
  rename_i io
  cases h5 : stPumpHistory inp p io.1 <;> simp only [h5] at h
  · cases h
  rename_i ct
  cases h6 : stEventual inp (eventualVals g p (sensOf p inp.autosens_data
      (sensitivityRatioOf p inp.autosens_data ((mm.1 + mm.2) / 2))) io.1) <;> simp only [h6] at h
  · cases h
  cases h7 : stMeal inp <;> simp only [h7, pure, Except.pure] at h
  · cases h
  cases h
  show ∃ i, io.1.iob = some (.fin i)
  unfold stEventual at h6
  split at h6
  · cases h6
  · rename_i hnan
    cases hio : io.1.iob with
    | none =>
      exfalso; apply hnan
      unfold eventualVals; rw [hio]; simp only [Option.js_none]
      simp [rnd, JsNum.round, JsNum.isNaN]
    | some v =>
      cases v with
      | nan =>
        exfalso; apply hnan
        unfold eventualVals; rw [hio]; simp only [Option.js_some]
        simp [rnd, JsNum.round, JsNum.isNaN]
      | fin i => exact ⟨i, rfl⟩

/-- What an early return of the prelude can contain. -/
theorem prelude_error {inp : DBInputs} {e : Result} (h : dbPrelude inp = .error e)
    (hM : ∀ p, inp.profile = some p → ∃ M, getMaxSafeBasal p = .fin M ∧ 0 ≤ M) :
    e.units = none ∧
    (e.rate = none ∨ e.rate = some 0 ∨ ∃ p, inp.profile = some p ∧ e.rate = some (profileCurrentBasal p)) := by
  unfold dbPrelude at h
  cases h1 : stProfile inp with
  | error e1 =>
    simp only [h1, bind, Except.bind] at h; cases h
    unfold stProfile at h1
    split at h1
    · cases h1; exact ⟨rfl, Or.inl rfl⟩
    · split at h1 <;> cases h1; exact ⟨rfl, Or.inl rfl⟩
  | ok p =>
  have hp := stProfile_ok h1
  simp only [h1, bind, Except.bind] at h
  cases h2 : stGlucose inp p with
  | error e2 =>
    simp only [h2] at h; cases h
    unfold stGlucose at h2
    split at h2
    · cases h2; exact ⟨rfl, Or.inl rfl⟩
    · simp only at h2
      split at h2
      · cases h2
        obtain ⟨hu, hr⟩ := cgmResult_rate inp p _
        refine ⟨hu, ?_⟩
        rcases hr with hr | hr | hr
        · exact Or.inl hr
        · exact Or.inr (Or.inl hr)
        · exact Or.inr (Or.inr ⟨p, hp, hr⟩)
      · cases h2
  | ok g =>
  simp only [h2] at h
  cases h3 : stTargets p with
  | error e3 =>
    simp only [h3] at h; cases h
    unfold stTargets at h3; split at h3 <;> cases h3; exact ⟨rfl, Or.inl rfl⟩
  | ok mm =>
  simp only [h3] at h
  cases h4 : stIob inp with
  | error e4 =>
    simp only [h4] at h; cases h
    unfold stIob at h4
    split at h4
    · cases h4; exact ⟨rfl, Or.inl rfl⟩
    · simp only at h4
      split at h4
      · cases h4; exact ⟨rfl, Or.inl rfl⟩
      · split at h4 <;> cases h4; exact ⟨rfl, Or.inl rfl⟩
  | ok io =>
  simp only [h4] at h
  cases h5 : stPumpHistory inp p io.1 with
  | error e5 =>
    simp only [h5] at h; cases h
    obtain ⟨M, hM1, hM0⟩ := hM p hp
    rcases stPumpHistory_error h5 with he | ⟨rT, ct, hr, hu, he⟩
    · subst he; exact ⟨rfl, Or.inl rfl⟩
    · subst he
      refine ⟨by simp; exact hu, ?_⟩
      rcases setTempBasal_zero_rate (dur := 0) (rT := rT) (ct := some ct) hM1 hM0 with h | h
      · left; rw [h]; exact hr
      · right; left; exact h
  | ok ct =>
  simp only [h5] at h
  split at h
  · rename_i e6 h6
    cases h
    unfold stEventual at h6
    split at h6 <;> cases h6; exact ⟨rfl, Or.inl rfl⟩
  · rename_i h6
    split at h
    · rename_i e7 h7
      cases h
      unfold stMeal at h7
      split at h7 <;> cases h7; exact ⟨rfl, Or.inl rfl⟩
    · cases h

/-- `dbPredict` builds a fresh `rT`: no rate, no microbolus. -/
@[simp] theorem dbPredict_rT_rate (inp : DBInputs) (pre : Pre) : (dbPredict inp pre).rT.rate = none := rfl
@[simp] theorem dbPredict_rT_units (inp : DBInputs) (pre : Pre) : (dbPredict inp pre).rT.units = none := rfl
/-- `dbPredict` passes the prelude's values through unchanged. -/
@[simp] theorem dbPredict_toPre (inp : DBInputs) (pre : Pre) : (dbPredict inp pre).toPre = pre := rfl

end LeanAID.Proofs
