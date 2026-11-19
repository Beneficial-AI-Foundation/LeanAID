/-
  LeanAID.Time.Duration — R4 and P3: the durations `determine_basal` issues
  (docs/timing-plan.md, item T4).

  Per call: every finite issued duration is 0 (cancel) or between 30 and 120
  minutes (R4, P3a); with a finite rate as well, the duration is 0, or in
  [30, 120] with rate 0, or exactly 30 with a rate ≥ 0 (P3b). NaN durations and
  NaN rates are not covered (F-06).

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import LeanAID.Time.Lift

namespace LeanAID.Time

open LeanAID LeanAID.Proofs JsNum

/-- The temp of a result is well formed (P3): a finite duration is 0 or in [30, 120];
    with a finite rate, the duration is 0, or in [30, 120] with rate 0, or 30 with a
    rate ≥ 0. -/
def TempOk (res : Result) : Prop :=
  ∀ d : Rat, res.duration = some (.fin d) →
    (d = 0 ∨ (30 ≤ d ∧ d ≤ 120)) ∧
    ∀ r : Rat, res.rate = some (.fin r) → d = 0 ∨ (30 ≤ d ∧ d ≤ 120 ∧ r = 0) ∨ (d = 30 ∧ 0 ≤ r)

/-- A result keeps the duration it started from, or is well formed. -/
def DurOk (res : Result) (base : Option JsNum) : Prop := res.duration = base ∨ TempOk res

theorem tempOk_of_none {res : Result} (h : res.duration = none) : TempOk res := by
  intro d hd; rw [h] at hd; cases hd

@[simp] theorem addReasonIf_duration (r : Result) (b : Bool) (s : String) :
    (r.addReasonIf b s).duration = r.duration := by
  unfold Result.addReasonIf; cases b <;> rfl

theorem durOk_self (rT : Result) : DurOk rT rT.duration := Or.inl rfl

theorem rbR_zero (m : Option String) : rbR 0 m = 0 := by
  unfold rbR
  rcases lowestRateScale_cases m with h | h <;> simp [h, rts] <;> decide +kernel

theorem suggestedRate_nonpos {x M : Rat} {p : Profile} (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M)
    (hx : x ≤ 0) : suggestedRate (.fin x) p = .fin 0 := by
  unfold suggestedRate
  rw [hM]
  have : clampRate (.fin x) (.fin M) = .fin 0 := by
    unfold clampRate
    by_cases h : x < 0
    · simp [h]
    · have : x = 0 := by grind
      subst this
      simp; intro h'; grind
  rw [this, roundBasal_fin, rbR_zero]

/-- The durations `setTempBasal` is called with in `determine_basal`. -/
def DurArg (rate dur : JsNum) : Prop :=
  dur = 30 ∨ dur = 0 ∨ dur = .nan ∨ ((∃ q, dur = .fin q ∧ 30 ≤ q ∧ q ≤ 120) ∧ ∃ x, rate = .fin x ∧ x ≤ 0)

theorem stb_durOk {rate dur : JsNum} {p : Profile} {rT : Result} {ct : Option CurrentTemp} {M : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) (hd : DurArg rate dur) :
    DurOk (setTempBasal rate dur p rT ct) rT.duration := by
  have hsr : ∀ r, suggestedRate rate p = .fin r → 0 ≤ r := fun r h => (suggestedRate_bound hM hM0 h).1
  -- the issued (duration, rate) when `setTempBasal` sets a temp
  have key : TempOk { rT with duration := some dur, rate := some (suggestedRate rate p) } := by
    intro d hdd
    simp only [Option.some.injEq] at hdd
    subst hdd
    rcases hd with h | h | h | ⟨⟨q, hq, h1, h2⟩, x, hx, hx0⟩
    · cases h
      refine ⟨Or.inr ⟨by decide, by decide⟩, fun r hr => Or.inr (Or.inr ⟨rfl, hsr r ?_⟩)⟩
      simpa using hr
    · cases h; exact ⟨Or.inl rfl, fun _ _ => Or.inl rfl⟩
    · cases h
    · cases hq
      refine ⟨Or.inr ⟨h1, h2⟩, fun r hr => Or.inr (Or.inl ⟨h1, h2, ?_⟩)⟩
      simp only [Option.some.injEq] at hr
      rw [hx, suggestedRate_nonpos hM hM0 hx0] at hr
      cases hr; rfl
  unfold setTempBasal
  simp only
  cases keepRunning (roundBasal (clampRate rate (getMaxSafeBasal p)) p.model) dur ct with
  | some v => exact Or.inl rfl
  | none =>
    simp only
    split
    · split
      · split
        · right; intro d hd
          simp at hd; subst hd
          exact ⟨Or.inl rfl, fun _ _ => Or.inl rfl⟩
        · left; rfl
      · right; exact key
    · right; exact key

theorem durOk_trans {res : Result} {rT : Result} (h : DurOk res rT.duration) (h0 : rT.duration = none) :
    TempOk res := by
  rcases h with h | h
  · exact tempOk_of_none (h.trans h0)
  · exact h

theorem neutralTemp_durOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) :
    DurOk (neutralTemp c rT) rT.duration := by
  unfold neutralTemp
  split
  · exact Or.inl rfl
  · exact stb_durOk H.hM H.hM0 (Or.inl rfl)

/-- `min C (max 0 (round(y) · 30))`, when positive, is between 30 and `C`. -/
theorem steps30 (y : JsNum) (C : Rat) (hC : 30 ≤ C)
    (h : (JsNum.min (.fin C) (JsNum.max 0 (JsNum.round y 0 * 30)) >ʲ 0) = true) :
    ∃ q, JsNum.min (.fin C) (JsNum.max 0 (JsNum.round y 0 * 30)) = .fin q ∧ 30 ≤ q ∧ q ≤ C := by
  cases y with
  | nan => simp [JsNum.round, JsNum.mathRound, JsNum.mul, JsNum.max, JsNum.min] at h
  | fin y =>
    obtain ⟨N, hN⟩ := rnd0_int y
    rw [hN] at h ⊢
    have e : (JsNum.fin (Binary64.rd (N : Rat)) * 30 : JsNum) = .fin (Binary64.rd (Binary64.rd (N : Rat) * 30)) := rfl
    rw [e] at h ⊢
    generalize hv : Binary64.rd (Binary64.rd (N : Rat) * 30) = v at h ⊢
    have hv30 : 0 < v → 30 ≤ v := by
      intro hpos
      have hN1 : 1 ≤ N := by
        by_cases h1 : 1 ≤ N
        · exact h1
        · exfalso
          have h1 : N ≤ 0 := by omega
          have : Binary64.rd (N : Rat) ≤ 0 := Binary64.rd_nonpos (by exact_mod_cast h1)
          have : Binary64.rd (Binary64.rd (N : Rat) * 30) ≤ 0 := Binary64.rd_nonpos (by grind)
          grind
      have h1 : (1 : Rat) ≤ Binary64.rd (N : Rat) := by
        have := LeanAID.Binary64.rd_mono (show ((1 : Int) : Rat) ≤ (N : Rat) by exact_mod_cast hN1)
        rwa [LeanAID.Binary64.rd_intCast (by decide)] at this
      have := LeanAID.Binary64.rd_mono (show ((30 : Int) : Rat) ≤ Binary64.rd (N : Rat) * 30 by push_cast; grind)
      rw [LeanAID.Binary64.rd_intCast (by decide)] at this
      push_cast at this; grind
    simp only [JsNum.max, JsNum.min, show (0 : JsNum) = .fin 0 from rfl, gt_fin, decide_eq_true_eq] at h ⊢
    refine ⟨_, rfl, ?_⟩
    split <;> split at h <;> grind

/-- The zero temp of lines 983-1003: a rate ≤ 0 with `durationReq` in [30, 120]. -/
theorem zero_temp_arg {rate y : JsNum} (hle : (rate ≤ʲ 0) = true)
    (hpos : (JsNum.min 120 (JsNum.max 0 (rnd y * 30)) >ʲ 0) = true) :
    DurArg rate (JsNum.min 120 (JsNum.max 0 (rnd y * 30))) := by
  refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
  · exact steps30 y 120 (by decide) hpos
  · cases rate with
    | nan => simp [show (0 : JsNum) = .fin 0 from rfl] at hle
    | fin x => exact ⟨x, rfl, by simpa [show (0 : JsNum) = .fin 0 from rfl] using hle⟩

theorem lowEventualBG_durOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) :
    DurOk (lowEventualBG c rT) rT.duration := by
  unfold lowEventualBG
  simp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact stb_durOk H.hM H.hM0 (Or.inl rfl)
    | exact neutralTemp_durOk H _
    | (exfalso; rename_i h; simp [show (0 : JsNum) = .fin 0 from rfl] at h; done)
    | exact stb_durOk H.hM H.hM0 (zero_temp_arg ‹_› ‹_›)

theorem highTempSet_durOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) (rate ir : JsNum) :
    DurOk (highTempSet c rT rate ir) rT.duration := by
  unfold highTempSet
  simp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact stb_durOk H.hM H.hM0 (Or.inl rfl)

theorem smbLowTemp_cases (basal d : JsNum) :
    smbLowTemp basal d = (0, 0) ∨
    (smbLowTemp basal d = (JsNum.min 60 (JsNum.max 0 (rnd (d / 30) * 30)), 0)) ∨
    (smbLowTemp basal d).1 = 30 := by
  unfold smbLowTemp
  split
  · left; rfl
  · split
    · right; left; rfl
    · right; right; rfl

/-- The SMB low temp (lines 1111-1122), when issued, is well formed. -/
theorem smbLowTemp_tempOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) (ir : JsNum)
    (hpos : ((smbLowTemp c.basal (smbDurationReq c ir)).1 >ʲ 0) = true) :
    TempOk { rT with rate := some (smbLowTemp c.basal (smbDurationReq c ir)).2,
                     duration := some (smbLowTemp c.basal (smbDurationReq c ir)).1, rateFirst := true } := by
  obtain ⟨n, s, hn, hs, hbk⟩ := H.hbgrid
  have hrate := fun r => smbLowTemp_rate (r := r) hn hs hbk _ (smbDurationReq_int c ir)
  rw [H.hb] at hpos ⊢
  generalize smbDurationReq c ir = d at hpos hrate ⊢
  intro q hq
  simp only [Option.some.injEq] at hq
  rcases smbLowTemp_cases (.fin b) d with h | h | h
  · rw [h] at hpos; simp [show (0 : JsNum) = .fin 0 from rfl] at hpos
  · rw [h] at hpos hq ⊢
    obtain ⟨q', hq', h1, h2⟩ := steps30 _ 60 (by decide) hpos
    have e : JsNum.min 60 (JsNum.max 0 (rnd (d / 30) * 30)) = .fin q' := hq'
    simp only at hq; rw [e] at hq; cases hq
    refine ⟨Or.inr ⟨h1, by grind⟩, fun r hr => Or.inr (Or.inl ⟨h1, by grind, ?_⟩)⟩
    simp only [Option.some.injEq] at hr
    cases hr; rfl
  · rw [h] at hq; cases hq
    refine ⟨Or.inr ⟨by decide, by decide⟩, fun r hr => Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
    simp only [Option.some.injEq] at hr
    exact (hrate r hr).1

theorem highTemp_durOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) :
    DurOk (highTemp c rT) rT.duration := by
  unfold highTemp
  simp only
  generalize hs : (if (c.microBolusAllowed && c.enableSMB && c.bg >ʲ c.threshold) = true then _ else _) = s
  cases s with
  | inl res =>
    split at hs
    · unfold smbBlock smbFinish at hs
      split at hs
      · injection hs with hs; subst hs
        right
        rename_i hpos
        exact smbLowTemp_tempOk H _ _ hpos
      · cases hs
    · cases hs
  | inr rT' =>
    have hd : rT'.duration = rT.duration := by
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
      rcases highTempSet_durOk H _ _ _ with h | h
      · left; rw [h]; (try simp only [addReason_duration]); exact hd
      · right; exact h

theorem dbDoseRest_durOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) (rT : Result) :
    DurOk (dbDose.dbDoseRest c rT) rT.duration := by
  unfold dbDose.dbDoseRest
  simp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact stb_durOk H.hM H.hM0 (Or.inr (Or.inl rfl))
    | exact neutralTemp_durOk H _
    | exact lowEventualBG_durOk H _
    | exact highTemp_durOk H _

/-- `min 120 (max 30 x)` is NaN or in [30, 120]. -/
theorem clamp30_120 (x : JsNum) :
    JsNum.min 120 (JsNum.max 30 x) = .nan ∨ ∃ q, JsNum.min 120 (JsNum.max 30 x) = .fin q ∧ 30 ≤ q ∧ q ≤ 120 := by
  cases x with
  | nan => left; rfl
  | fin a =>
    right
    simp only [JsNum.max, JsNum.min, show (120 : JsNum) = .fin 120 from rfl]
    refine ⟨_, rfl, ?_⟩
    split <;> split <;> grind

theorem dbDose_durOk {c : Ctx} {M b : Rat} (H : DoseHyp c M b) : DurOk (dbDose c) c.rT.duration := by
  unfold dbDose
  simp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact dbDoseRest_durOk H _
    | skip
  apply stb_durOk H.hM H.hM0
  rcases clamp30_120 (rnd (rnd (60 * ((c.target_bg - c.minGuardBG) / c.sens) / c.p.current_basal.js) / 30) * 30) with h | ⟨q, hq, h1, h2⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨q, hq, h1, h2⟩, 0, rfl, Rat.le_refl⟩))

theorem stPumpHistory_error' {inp : DBInputs} {p : Profile} {iobd : IobTick} {e : Result}
    (h : stPumpHistory inp p iobd = .error e) :
    e = typeError "duration" ∨
    ∃ rT ct, rT.duration = none ∧ e = setTempBasal 0 0 p rT (some ct) := by
  unfold stPumpHistory at h
  cases hct : inp.currenttemp with
  | none => simp [hct] at h; exact Or.inl h.symm
  | some ct =>
    cases hlt : iobd.lastTemp with
    | none => simp [hct, hlt] at h
    | some lt =>
      simp only [hct, hlt] at h
      split at h
      · simp at h; exact Or.inr ⟨_, ct, rfl, h.symm⟩
      · split at h
        · simp at h; exact Or.inr ⟨_, ct, rfl, h.symm⟩
        · simp at h

theorem cgmResult_tempOk (inp : DBInputs) (p : Profile) (g : GluVals)
    (hpcb : ∀ r, profileCurrentBasal p = .fin r → 0 ≤ r) : TempOk (cgmResult inp p g) := by
  unfold cgmResult
  split
  · exact tempOk_of_none rfl
  · simp only
    split
    · intro d hd
      simp only [Option.some.injEq] at hd
      cases hd
      refine ⟨Or.inr ⟨by decide, by decide⟩, fun r hr => Or.inr (Or.inr ⟨rfl, hpcb r ?_⟩)⟩
      simpa using hr
    · split
      · intro d hd
        simp only [Option.some.injEq] at hd
        cases hd
        exact ⟨Or.inr ⟨by decide, by decide⟩, fun r hr => Or.inr (Or.inr ⟨rfl, by simp at hr; subst hr; decide⟩)⟩
      · exact tempOk_of_none (by simp)

/-- The early returns of the prelude (lines 128-423) are well formed. -/
theorem prelude_error_tempOk {inp : DBInputs} {e : Result} (h : dbPrelude inp = .error e)
    (hM : ∀ p, inp.profile = some p → ∃ M, getMaxSafeBasal p = .fin M ∧ 0 ≤ M)
    (hpcb : ∀ p, inp.profile = some p → ∀ r, profileCurrentBasal p = .fin r → 0 ≤ r) : TempOk e := by
  unfold dbPrelude at h
  cases h1 : stProfile inp with
  | error e1 =>
    simp only [h1, bind, Except.bind] at h; cases h
    unfold stProfile at h1
    split at h1
    · cases h1; exact tempOk_of_none rfl
    · split at h1 <;> cases h1; exact tempOk_of_none rfl
  | ok p =>
  have hp := stProfile_ok h1
  simp only [h1, bind, Except.bind] at h
  cases h2 : stGlucose inp p with
  | error e2 =>
    simp only [h2] at h; cases h
    unfold stGlucose at h2
    split at h2
    · cases h2; exact tempOk_of_none rfl
    · simp only at h2
      split at h2
      · cases h2; exact cgmResult_tempOk _ _ _ (hpcb p hp)
      · cases h2
  | ok g =>
  simp only [h2] at h
  cases h3 : stTargets p with
  | error e3 =>
    simp only [h3] at h; cases h
    unfold stTargets at h3; split at h3 <;> cases h3; exact tempOk_of_none rfl
  | ok mm =>
  simp only [h3] at h
  cases h4 : stIob inp with
  | error e4 =>
    simp only [h4] at h; cases h
    unfold stIob at h4
    split at h4
    · cases h4; exact tempOk_of_none rfl
    · simp only at h4
      split at h4
      · cases h4; exact tempOk_of_none rfl
      · split at h4 <;> cases h4; exact tempOk_of_none rfl
  | ok io =>
  simp only [h4] at h
  cases h5 : stPumpHistory inp p io.1 with
  | error e5 =>
    simp only [h5] at h; cases h
    obtain ⟨M, hM1, hM0⟩ := hM p hp
    rcases stPumpHistory_error' h5 with he | ⟨rT, ct, hr, he⟩
    · subst he; exact tempOk_of_none rfl
    · subst he
      exact durOk_trans (stb_durOk hM1 hM0 (Or.inr (Or.inl rfl))) hr
  | ok ct =>
  simp only [h5] at h
  split at h
  · rename_i e6 h6
    cases h
    unfold stEventual at h6
    split at h6 <;> cases h6; exact tempOk_of_none rfl
  · rename_i h6
    split at h
    · rename_i e7 h7
      cases h
      unfold stMeal at h7
      split at h7 <;> cases h7; exact tempOk_of_none rfl
    · cases h

/-- **R4 and P3 (per call).** For valid input, the temp that `determine_basal`
    issues is well formed: a finite duration is 0 or between 30 and 120 minutes; with a
    finite rate as well, the duration is 0, or between 30 and 120 with rate 0, or
    exactly 30 with a rate ≥ 0. NaN durations or rates are not covered (F-06). -/
theorem issued_temp_ok {inp : DBInputs} (hv : ValidInput inp) : TempOk (determineBasal inp) := by
  have hM : ∀ p, inp.profile = some p → ∃ M, getMaxSafeBasal p = .fin M ∧ 0 ≤ M := by
    intro p hp
    obtain ⟨-, M, -, -, hM, -, hMpos⟩ := maxSafeBasal_exists (hv.validProfile hp)
    exact ⟨M, hM, Rat.le_of_lt hMpos⟩
  have hpcb : ∀ p, inp.profile = some p → ∀ r, profileCurrentBasal p = .fin r → 0 ≤ r := by
    intro p hp r hr
    obtain ⟨b, hb, hb0⟩ := profileCurrentBasal_nonneg (hv.validProfile hp)
    rw [hb] at hr; cases hr; exact hb0
  unfold determineBasal
  cases hpre : dbPrelude inp with
  | error e => exact prelude_error_tempOk hpre hM hpcb
  | ok pre =>
    simp only
    obtain ⟨p, g, mm, io, ct, meal, h1, -, -, -, -, -, hpp, -, -, -, -, -, hbasal, -, -⟩ := prelude_ok hpre
    have hp := stProfile_ok h1
    obtain ⟨M, hM1, hM0⟩ := hM p hp
    obtain ⟨b, hb, hb0, hbg, hbM, -⟩ := adjustedBasal_bound hv hp hM1 ((mm.1 + mm.2) / 2)
    have H : DoseHyp (dbPredict inp pre) M b :=
      { hM := by simp [hpp, hM1], hM0, hb := by simp [hbasal, hb], hb0, hbgrid := hbg, hbM := by simp [hpp, hbM] }
    exact durOk_trans (dbDose_durOk H) rfl

/-- **P3 over runs.** In a legal run with valid input, every cycle's issued temp is
    well formed (`TempOk`). -/
theorem p3_temp_ok {env : Env} {r : Run Event} (hl : Legal env r) (hv : ValidRun env r) :
    ∀ c ∈ cycles env r, TempOk c.res := by
  intro c hc
  rw [(hl.cycle c hc).result]
  exact issued_temp_ok (hv c hc)

end LeanAID.Time
