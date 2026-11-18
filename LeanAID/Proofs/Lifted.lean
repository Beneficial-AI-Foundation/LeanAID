/-
  LeanAID.Proofs.Lifted — general theorems behind oref0's class A and B unit tests
  (M6) that are not already headline theorems.
-/
import LeanAID.Proofs.Headline
import LeanAID.Core.Iob

namespace LeanAID.Proofs

open JsNum

/-! ### Building the dose-phase hypotheses from valid input -/

theorem basalHyp_of_valid {inp : DBInputs} (hv : ValidInput inp) {pre : Pre} (hpre : dbPrelude inp = .ok pre) :
    ∃ M b, BasalHyp (dbPredict inp pre) M b ∧ pre.basal = .fin b := by
  obtain ⟨p, g, mm, io, ct, meal, h1, -, -, -, -, -, hpp, -, -, -, -, -, hbasal, -, -⟩ := prelude_ok hpre
  have hp := stProfile_ok h1
  have vp := hv.validProfile hp
  obtain ⟨cb, M, hcb, -, hM, -, hMpos⟩ := maxSafeBasal_exists vp
  obtain ⟨b, hb, hb0, hbg, hbM, hbid⟩ := adjustedBasal_bound hv hp hM ((mm.1 + mm.2) / 2)
  have H : BasalHyp (dbPredict inp pre) M b :=
    ⟨⟨by simp [hpp, hM], Rat.le_of_lt hMpos, by simp [hbasal, hb], hb0, hbg, by simp [hpp, hbM]⟩,
      by simp [hpp, hbid]⟩
  exact ⟨M, b, H, by rw [hbasal, hb]⟩

/-! ### R10: low eventual BG never raises insulin (class B tests) -/

theorem dbDose_lowEv {c : Ctx} {M b : Rat} (H : BasalHyp c M b) (hev : (c.eventualBG' <ʲ c.min_bg) = true) :
    RateOk b (dbDose c) c.rT.rate := by
  have rest : ∀ rT : Result, rT.rate = c.rT.rate → RateOk b (dbDose.dbDoseRest c rT) c.rT.rate := by
    intro rT h0
    unfold dbDose.dbDoseRest
    simp only
    split
    · rw [← h0]; exact rateOk_stb_le H.hM H.hM0 H.hb0 H.hbid (zeroReq b H.hb0)
    · first
        | (rw [ite_eq_left_iff.mpr (fun h => absurd hev h), ← h0]; exact lowEventualBG_le H _)
        | (rw [← h0]; exact lowEventualBG_le H _)
  unfold dbDose
  simp only
  split
  · exact rest _ (by simp)
  · split
    · exact rateOk_stb_le H.hM H.hM0 H.hb0 H.hbid (zeroReq b H.hb0)
    · exact rest _ rfl

/-- **R10 (class B tests DB-08, 13, 14, 26-28, 34, 64).** For valid input, if
    oref0's eventual BG is below `min_bg`, every finite issued rate is between 0 and
    the (sensitivity-adjusted) basal: a low eventual BG never raises insulin. -/
theorem low_eventual_rate_le_basal {inp : DBInputs} (hv : ValidInput inp) {pre : Pre}
    (hpre : dbPrelude inp = .ok pre) (hev : ((dbPredict inp pre).eventualBG' <ʲ pre.min_bg) = true) :
    ∃ b, pre.basal = .fin b ∧ ∀ r, (determineBasal inp).rate = some (.fin r) → 0 ≤ r ∧ r ≤ b := by
  obtain ⟨M, b, H, hb⟩ := basalHyp_of_valid hv hpre
  refine ⟨b, hb, fun r hr => ?_⟩
  unfold determineBasal at hr; rw [hpre] at hr; simp only at hr
  rcases dbDose_lowEv H hev r hr with h | h
  · simp at h
  · exact h

/-! ### In range or falling: a neutral temp (class A tests) -/

/-- **Class A tests DB-06, 33, 36-38, 69, 70.** When no low-glucose suspend applies,
    skip-neutral mode is off, eventual BG is at least `min_bg`, SMB is not active,
    and BG is either falling faster than expected or predicted in range, the
    decision is oref0's neutral temp (`neutralTemp`, lines 1016-1022/1030-1036):
    keep a running temp equal to the basal, or set the basal for 30 minutes. -/
theorem dbDose_neutral {c : Ctx}
    (hexc : (c.bg <ʲ c.threshold && c.iobd.iob.js <ʲ -c.p.current_basal.js * 20 / 60 &&
      c.minDelta >ʲ 0 && c.minDelta >ʲ c.expectedDelta) = false)
    (hlgs : (c.bg <ʲ c.threshold || c.minGuardBG <ʲ c.threshold) = false)
    (hskip : c.p.skip_neutral_temps.truthy = false)
    (hev : (c.eventualBG' <ʲ c.min_bg) = false)
    (hsmb : (c.microBolusAllowed && c.enableSMB) = false)
    (hcase : (c.minDelta <ʲ c.expectedDelta) = true ∨ (JsNum.min c.eventualBG' c.minPredBG <ʲ c.max_bg) = true) :
    ∃ rT', rT'.rate = c.rT.rate ∧ rT'.units = c.rT.units ∧ dbDose c = neutralTemp c rT' := by
  unfold dbDose dbDose.dbDoseRest
  simp only
  rw [if_neg (by rw [hexc]; decide), if_neg (by rw [hlgs]; decide)]
  rw [if_neg (by simp [hskip]), if_neg (by rw [hev]; decide)]
  rcases hcase with h | h
  · rw [if_pos (by simp [h, hsmb])]
    refine ⟨_, ?_, ?_, rfl⟩ <;> split <;> rfl
  · by_cases h2 : (c.minDelta <ʲ c.expectedDelta) = true
    · rw [if_pos (by simp [h2, hsmb])]
      refine ⟨_, ?_, ?_, rfl⟩ <;> split <;> rfl
    · rw [if_neg (by simp [h2]), if_pos (by simp [h, hsmb])]
      refine ⟨_, ?_, ?_, rfl⟩ <;> rfl

/-- The neutral temp leaves the rate unchanged or issues the basal, clamped and
    rounded (0 only in skip-neutral mode). -/
theorem neutralTemp_rate (c : Ctx) (rT : Result) :
    (neutralTemp c rT).rate = rT.rate ∨ (neutralTemp c rT).rate = some 0 ∨
    (neutralTemp c rT).rate = some (suggestedRate c.basal c.p) := by
  unfold neutralTemp
  split
  · left; rfl
  · rcases setTempBasal_rate_cases c.basal 30 c.p (rT.addReason _) (some c.ct) with h | h | h
    · left; rw [h]; rfl
    · right; left; exact h
    · right; right; exact h

/-! ### setTempBasal (set-temp-basal.test.js) -/

/-- **STB-01..03, 05..10.** With no temp running and skip-neutral mode off,
    `setTempBasal` issues exactly the request clamped to `[0, maxSafeBasal]` and
    rounded by `round_basal`, for the requested duration. -/
theorem setTempBasal_no_temp (rate dur : JsNum) (p : Profile) (rT : Result)
    (hskip : p.skip_neutral_temps ≠ some true) :
    (setTempBasal rate dur p rT none).rate = some (suggestedRate rate p) ∧
    (setTempBasal rate dur p rT none).duration = some dur := by
  have hk : ∀ s, keepRunning s dur none = none := fun _ => rfl
  simp only [setTempBasal, suggestedRate, hk]
  split
  · have : (p.skip_neutral_temps == some true) = false := by
      cases h : p.skip_neutral_temps with
      | none => rfl
      | some v => cases v <;> simp_all
    simp only [this]; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- **STB-04.** In skip-neutral mode, a request equal to the scheduled basal
    cancels a running temp (rate 0, duration 0) or, with none running, issues nothing. -/
theorem setTempBasal_skip_neutral (rate dur : JsNum) (p : Profile) (rT : Result) (ct : Option CurrentTemp)
    (hskip : p.skip_neutral_temps = some true)
    (hkeep : keepRunning (suggestedRate rate p) dur ct = none)
    (heq : (suggestedRate rate p =ʲ p.current_basal.js) = true) :
    (tempActive ct = true → (setTempBasal rate dur p rT ct).rate = some 0 ∧
      (setTempBasal rate dur p rT ct).duration = some 0) ∧
    (tempActive ct = false → (setTempBasal rate dur p rT ct).rate = rT.rate) := by
  unfold suggestedRate at hkeep heq
  simp only [setTempBasal, hkeep, heq, hskip, ite_true]
  constructor
  · intro h; simp only [h, ite_true]; exact ⟨rfl, rfl⟩
  · intro h; simp only [h, Bool.false_eq_true, ite_false]; rfl

/-! ### round_basal (DB-01..05) -/

/-- The scale `round_basal` rounds to: 1/scale U/h steps. -/
def basalScale (x : Rat) (m : Option String) : Rat :=
  if x < 1 then lowestRateScale m else if x < 10 then 20 else 10

/-- **DB-01..05.** `round_basal(x)` is `x` rounded to the nearest multiple of
    `1/scale` (ties up): steps of 0.05 U/h below 10 U/h (0.025 below 1 U/h for
    x23/x54 pump models) and 0.1 U/h from 10 U/h. -/
theorem roundBasal_nearest (x : Rat) (m : Option String) :
    roundBasal (.fin x) m = .fin (rts x (basalScale x m)) ∧
    rts x (basalScale x m) * basalScale x m ≤ x * basalScale x m + 1/2 ∧
    x * basalScale x m - 1/2 < rts x (basalScale x m) * basalScale x m := by
  have hpos : 0 < basalScale x m := by
    unfold basalScale; split
    · exact lowestRateScale_pos m
    · split <;> decide
  refine ⟨?_, rts_mul_le hpos, lt_rts_mul hpos⟩
  rw [roundBasal_fin]; congr 1
  unfold rbR basalScale; split <;> (try split) <;> rfl

theorem lowestRateScale_x23 (m : String) (h : m.endsWith "23" = true ∨ m.endsWith "54" = true) :
    lowestRateScale (some m) = 40 := by
  unfold lowestRateScale; rcases h with h | h <;> simp [h]

/-! ### Insulin on board (iob.test.js) -/

/-- **IOB-08.** The exponential insulin curves use a DIA of at least 5 hours
    (total.js lines 52-56), and every curve at least 3 hours. -/
theorem curveSetup_dia_eq (p : Profile) :
    (Iob.curveSetup p).2.1 =
      (if ((Iob.curveSetup p).1 != "bilinear") && ((if p.dia.js <ʲ 3 then 3 else p.dia.js) <ʲ 5) then 5
       else (if p.dia.js <ʲ 3 then 3 else p.dia.js)) := rfl

theorem curveSetup_dia (p : Profile) {d : Rat} (h : (Iob.curveSetup p).2.1 = JsNum.fin d) :
    3 ≤ d ∧ ((Iob.curveSetup p).1 ≠ "bilinear" → 5 ≤ d) := by
  rw [curveSetup_dia_eq] at h
  generalize (Iob.curveSetup p).1 = cv at h ⊢
  generalize p.dia.js = dia0 at h
  rw [show (3 : JsNum) = .fin 3 from rfl, show (5 : JsNum) = .fin 5 from rfl] at h
  cases dia0 with
  | nan => simp at h
  | fin x =>
    have hd1 : (if (JsNum.fin x <ʲ .fin 3) = true then JsNum.fin 3 else .fin x) =
        .fin (if x < 3 then 3 else x) := by by_cases hx : x < 3 <;> simp [hx]
    rw [hd1] at h
    have h3 : 3 ≤ (if x < 3 then (3 : Rat) else x) := by split <;> grind
    generalize hy : (if x < 3 then (3 : Rat) else x) = y at h h3
    by_cases hc : cv = "bilinear"
    · subst hc; simp at h; subst h; exact ⟨h3, fun h => absurd rfl h⟩
    · have : (cv != "bilinear") = true := by simp [hc]
      rw [this] at h
      by_cases h5 : y < 5
      · simp [h5] at h; subst h; exact ⟨by decide, fun _ => by decide⟩
      · simp [h5] at h; subst h; exact ⟨h3, fun _ => by grind⟩

/-- **IOB-01 (bilinear curve).** A dose is fully on board when given
    (`iobContrib = insulin` at `minsAgo = 0`) and contributes nothing once the
    scaled time reaches 180 minutes (DIA). -/
theorem bilinear_at_zero (a dia : Rat) (hdia : 0 < dia) :
    (Iob.iobCalcBilinear (.fin a) 0 (.fin dia)).iobContrib = .fin a := by
  have hd : dia ≠ 0 := by grind
  have hd60 : dia * 60 ≠ 0 := by grind
  unfold Iob.iobCalcBilinear
  simp only [JsNum.ofNat_eq, JsNum.zero_eq, JsNum.fin_div hd, JsNum.fin_mul, JsNum.fin_div hd60]
  have h75 : (75 : Rat) ≠ 0 := by decide
  rw [JsNum.fin_div h75]
  simp only [JsNum.fin_mul, JsNum.fin_div (by decide : (5 : Rat) ≠ 0), JsNum.fin_add, JsNum.ofSci_eq,
    JsNum.fin_neg, JsNum.lt_fin]
  rw [if_pos (by simp; decide +kernel)]
  congr 1
  have : (3 / dia * 0 / 5 + 1 : Rat) = 1 := by grind
  simp only [this]
  have e : (-(OfScientific.ofScientific 1852 true 6 : Rat) * 1 * 1 + OfScientific.ofScientific 1852 true 6 * 1 +
      OfScientific.ofScientific 1000000 true 6) = 1 := by decide +kernel
  rw [e]; try grind

theorem bilinear_after_dia (a m dia : Rat) (hdia : 0 < dia) (hm : 180 ≤ 3 / dia * m) :
    (Iob.iobCalcBilinear (.fin a) (.fin m) (.fin dia)).iobContrib = .fin 0 := by
  have hd : dia ≠ 0 := by grind
  unfold Iob.iobCalcBilinear
  simp only [JsNum.ofNat_eq, JsNum.fin_div hd, JsNum.fin_mul, JsNum.lt_fin]
  rw [if_neg (by simp; grind), if_neg (by simp; grind)]
  try rfl

/-- **Finding F-10.** The bilinear curve's IOB polynomial dips below zero just
    before DIA: a 10 U dose 177 minutes ago (DIA 3 h) contributes −0.0021352 U, so
    oref0 can report negative IOB for positive doses. -/
theorem bilinear_negative :
    ((Iob.iobCalcBilinear 10 177 3).iobContrib <ʲ (-0.002 : JsNum)) = true := by
  decide +kernel

/-- **BAS-01.** `maxDailyBasal` is at least every rate of the schedule. -/
theorem maxDailyBasal_ge (b : BasalEntry) (bs : List BasalEntry) (e : BasalEntry) (he : e ∈ b :: bs)
    (hfin : ∀ x ∈ b :: bs, ∃ r, x.rate = .fin r) :
    ∃ m r, Iob.maxDailyBasal (b :: bs) = .fin m ∧ e.rate = .fin r ∧ r ≤ m := by
  -- the fold keeps the entry with the largest rate
  have key : ∀ (acc : BasalEntry) (l : List BasalEntry) (ra : Rat), acc.rate = .fin ra →
      (∀ x ∈ l, ∃ r, x.rate = .fin r) →
      ∃ rm, (l.foldl (fun m e => if (e.rate >ʲ m.rate) = true then e else m) acc).rate = .fin rm ∧ ra ≤ rm ∧
        ∀ x ∈ l, ∀ r, x.rate = .fin r → r ≤ rm := by
    intro acc l
    induction l generalizing acc with
    | nil => intro ra h _; exact ⟨ra, h, Rat.le_refl, by simp⟩
    | cons x xs ih =>
      intro ra h hf
      obtain ⟨rx, hx⟩ := hf x (by simp)
      simp only [List.foldl_cons]
      by_cases hgt : ra < rx
      · have : (x.rate >ʲ acc.rate) = true := by rw [hx, h]; simp [hgt]
        rw [if_pos this]
        obtain ⟨rm, h1, h2, h3⟩ := ih x rx hx (fun y hy => hf y (by simp [hy]))
        refine ⟨rm, h1, by grind, ?_⟩
        intro y hy r hr
        simp at hy; rcases hy with rfl | hy
        · rw [hx] at hr; cases hr; exact h2
        · exact h3 y hy r hr
      · have : (x.rate >ʲ acc.rate) = false := by rw [hx, h]; simp; grind
        rw [if_neg (by rw [this]; decide)]
        obtain ⟨rm, h1, h2, h3⟩ := ih acc ra h (fun y hy => hf y (by simp [hy]))
        refine ⟨rm, h1, h2, ?_⟩
        intro y hy r hr
        simp at hy; rcases hy with rfl | hy
        · rw [hx] at hr; cases hr; grind
        · exact h3 y hy r hr
  obtain ⟨rb, hb⟩ := hfin b (by simp)
  obtain ⟨rm, h1, h2, h3⟩ := key b bs rb hb (fun x hx => hfin x (by simp [hx]))
  obtain ⟨re, hre⟩ := hfin e he
  refine ⟨rm * 1000 / 1000, re, ?_, hre, ?_⟩
  · unfold Iob.maxDailyBasal; simp only [h1, JsNum.ofNat_eq, JsNum.fin_mul]
    rw [JsNum.fin_div (by decide)]
  · have : rm * 1000 / 1000 = rm := by rw [Rat.mul_div_cancel (by decide)]
    rw [this]
    simp at he; rcases he with rfl | he
    · rw [hb] at hre; cases hre; exact h2
    · exact h3 e he re hre

end LeanAID.Proofs
