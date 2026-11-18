/-
  LeanAID.Proofs.MaxIob — H4: with insulin on board at or above `max_iob`, oref0
  issues no rate above the (sensitivity-adjusted) basal and no microbolus.
-/
import LeanAID.Proofs.Hypo

namespace LeanAID.Proofs

open JsNum

/-- `x` is NaN or a non-positive number. -/
def NonPos (x : JsNum) : Prop := x = .nan ∨ ∃ v, x = .fin v ∧ v ≤ 0

theorem rts_nonpos {x s : Rat} (hs : 0 < s) (h : x ≤ 0) : rts x s ≤ 0 := by
  have := rts_le_of_lt (x := x) (s := s) (n := 0) hs (by
    have : x * s ≤ 0 * s := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hs)
    grind)
  rwa [show ((0 : Int) : Rat) / s = 0 by rw [Rat.div_def]; simp] at this

theorem pow10_pos (d : Nat) : 0 < pow10 d := by
  induction d with
  | zero => decide
  | succ n ih => unfold pow10; have : (0 : Rat) < 10 := by decide
                 exact Rat.mul_pos this ih

theorem NonPos.rnd {x : JsNum} (h : NonPos x) (d : Nat) : NonPos (JsNum.round x d) := by
  rcases h with h | ⟨v, h, hv⟩
  · subst h; left; rfl
  · subst h; right; exact ⟨_, rnd_fin v d, rts_nonpos (pow10_pos d) hv⟩

theorem NonPos.of_le {x : JsNum} {bound : Rat} (hb : bound ≤ 0)
    (h : x = .nan ∨ ∃ v, x = .fin v ∧ v ≤ bound) : NonPos x := by
  rcases h with h | ⟨v, h, hv⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, h, Rat.le_trans hv hb⟩

/-- `2 * Math.min(0, y)` is NaN or non-positive. -/
theorem nonPos_two_min (y : JsNum) : NonPos (2 * JsNum.min 0 y) := by
  cases y with
  | nan => left; rfl
  | fin y =>
    right; refine ⟨2 * (if 0 ≤ y then 0 else y), rfl, ?_⟩
    split <;> grind

theorem nonPos_min (y : JsNum) : NonPos (JsNum.min 0 y) := by
  cases y with
  | nan => left; rfl
  | fin y => right; refine ⟨(if 0 ≤ y then 0 else y), rfl, ?_⟩; split <;> grind

/-- A request `round_basal(basal + 2·ir)` with `ir` NaN or non-positive is NaN or
    at most the basal. -/
theorem req_le_basal {b : Rat} {m : Option String} (hb0 : 0 ≤ b) (hbid : rbR b m = b) {ir : JsNum}
    (h : NonPos ir) : roundBasal (.fin b + 2 * ir) m = .nan ∨
      ∃ x, roundBasal (.fin b + 2 * ir) m = .fin x ∧ x ≤ b := by
  rcases h with h | ⟨v, h, hv⟩
  · subst h; left; simp [roundBasal_nan]
  · subst h; right
    refine ⟨rbR (b + 2 * v) m, by rw [show (2 : JsNum) = .fin 2 from rfl]; simp only [JsNum.fin_mul, JsNum.fin_add, roundBasal_fin], ?_⟩
    rw [← hbid]; exact rbR_mono m (by grind)

/-- `clampRate` returns 0 or a value at most the request. -/
theorem clampRate_le {x M c : Rat} (h : clampRate (.fin x) (.fin M) = .fin c) : c = 0 ∨ c ≤ x := by
  unfold clampRate at h
  split at h
  · left; injection h with h; exact h.symm
  · split at h
    · right; rename_i h2; simp at h h2; subst h; grind
    · right; simp at h; subst h; exact Rat.le_refl

/-- A `setTempBasal` request that is NaN or at most `b` issues at most `b`. -/
theorem rateOk_stb_le {rate dur : JsNum} {p : Profile} {rT : Result} {ct : Option CurrentTemp} {M b : Rat}
    (hM : getMaxSafeBasal p = .fin M) (hM0 : 0 ≤ M) (hb0 : 0 ≤ b) (hbid : rbR b p.model = b)
    (hreq : rate = .nan ∨ ∃ x, rate = .fin x ∧ x ≤ b) :
    RateOk b (setTempBasal rate dur p rT ct) rT.rate := by
  intro r hr
  rcases setTempBasal_rate_cases rate dur p rT ct with h | h | h
  · left; rw [← h]; exact hr
  · right; rw [h] at hr; simp at hr; subst hr; exact ⟨Rat.le_refl, hb0⟩
  · right; rw [h] at hr
    have hr' := Option.some.inj hr
    unfold suggestedRate at hr'; rw [hM] at hr'
    rcases hreq with hreq | ⟨x, hx, hxb⟩
    · subst hreq; rw [clampRate_nan, roundBasal_nan] at hr'; cases hr'
    · subst hx
      obtain ⟨c, hc, hc0, -⟩ := clampRate_fin (x := x) hM0
      rw [hc, roundBasal_fin] at hr'; injection hr' with hr'; subst hr'
      refine ⟨rbR_nonneg _ hc0, ?_⟩
      have : c ≤ b := by rcases clampRate_le hc with h | h <;> grind
      rw [← hbid]; exact rbR_mono _ this

/-- Hypotheses for H4 about a dose context. -/
structure IobHyp (c : Ctx) (M b : Rat) : Prop extends DoseHyp c M b where
  hbid : rbR b c.p.model = b
  hiob : ∃ i mi : Rat, c.iobd.iob = some (.fin i) ∧ c.max_iob = .fin mi ∧ mi ≤ i
  hinc : ∀ x : Rat, c.p.bolus_increment = some (.fin x) → 0 < x

theorem IobHyp.basalReq {c : Ctx} {M b : Rat} (H : IobHyp c M b) :
    c.basal = .nan ∨ ∃ x, c.basal = .fin x ∧ x ≤ b := Or.inr ⟨b, H.hb, Rat.le_refl⟩

theorem zeroReq (b : Rat) (hb0 : 0 ≤ b) : (0 : JsNum) = .nan ∨ ∃ x, (0 : JsNum) = .fin x ∧ x ≤ b :=
  Or.inr ⟨0, rfl, hb0⟩

theorem neutralTemp_le {c : Ctx} {M b : Rat} (H : IobHyp c M b) (rT : Result) :
    RateOk b (neutralTemp c rT) rT.rate := by
  unfold neutralTemp
  split
  · exact rateOk_self _ _
  · exact rateOk_stb_le H.hM H.hM0 H.hb0 H.hbid H.basalReq

theorem lowEventualBG_le {c : Ctx} {M b : Rat} (H : IobHyp c M b) (rT : Result) :
    RateOk b (lowEventualBG c rT) rT.rate := by
  have hreq : ∀ ir : JsNum, NonPos ir → (roundBasal (c.basal + 2 * ir) c.p.model = .nan ∨
      ∃ x, roundBasal (c.basal + 2 * ir) c.p.model = .fin x ∧ x ≤ b) := by
    intro ir h; rw [H.hb]; exact req_le_basal H.hb0 H.hbid h
  have hirB := (nonPos_two_min ((c.eventualBG' - c.target_bg) / c.sens)).rnd 2
  have hirA : (c.minDelta <ʲ 0 && c.minDelta >ʲ c.expectedDelta) = true →
      NonPos (rnd (rnd (2 * JsNum.min 0 ((c.eventualBG' - c.target_bg) / c.sens)) 2 *
        (c.minDelta / c.expectedDelta)) 2) := by
    intro hc
    apply NonPos.rnd
    have hir0 := hirB
    simp only [rnd]
    generalize JsNum.round (2 * JsNum.min 0 ((c.eventualBG' - c.target_bg) / c.sens)) 2 = a at hir0 ⊢
    cases hm : c.minDelta with
    | nan => rw [hm] at hc; simp at hc
    | fin m =>
      cases he : c.expectedDelta with
      | nan => rw [hm, he] at hc; simp at hc
      | fin e =>
        rw [hm, he] at hc
        simp at hc
        obtain ⟨hm0, hem⟩ := hc
        have hratio : 0 < m / e := div_pos_of_neg_neg hm0 (by grind)
        rw [JsNum.fin_div (by grind)]
        rcases hir0 with h | ⟨v, h, hv⟩
        · subst h; left; rfl
        · subst h; right; refine ⟨v * (m / e), rfl, ?_⟩
          have : v * (m / e) ≤ 0 * (m / e) := Rat.mul_le_mul_of_nonneg_right hv (Rat.le_of_lt hratio)
          grind
  unfold lowEventualBG
  simp only
  repeat' split
  all_goals first
    | exact rateOk_self _ _
    | exact neutralTemp_le H _
    | exact rateOk_stb_le H.hM H.hM0 H.hb0 H.hbid (zeroReq b H.hb0)
    | exact rateOk_stb_le H.hM H.hM0 H.hb0 H.hbid (hreq _ hirB)
    | exact rateOk_stb_le H.hM H.hM0 H.hb0 H.hbid (hreq _ (hirA (by assumption)))


/-- The capped insulinReq (lines 1060-1063) is NaN or non-positive when there is
    no room left below `max_iob`. -/
theorem capped_nonPos (ir0 : JsNum) {w : Rat} (hw : w ≤ 0) : NonPos (capInsulinReq ir0 (.fin w)) := by
  unfold capInsulinReq
  split
  · right; exact ⟨w, rfl, hw⟩
  · rename_i hc
    cases ir0 with
    | nan => left; rfl
    | fin v => right; refine ⟨v, rfl, ?_⟩; simp at hc; grind

theorem highTempSet_le {c : Ctx} {M b : Rat} (H : IobHyp c M b) (rT : Result) (rate ir : JsNum)
    (hreq : rate = .nan ∨ ∃ x, rate = .fin x ∧ x ≤ b) :
    RateOk b (highTempSet c rT rate ir) rT.rate := by
  unfold highTempSet
  simp only
  repeat' split
  all_goals first
    | exact rateOk_self _ _
    | exact rateOk_stb_le H.hM H.hM0 H.hb0 H.hbid hreq

theorem highTemp_le {c : Ctx} {M b : Rat} (H : IobHyp c M b) (rT : Result) :
    RateOk b (highTemp c rT) rT.rate := by
  obtain ⟨i, mi, hi, hmi, hle⟩ := H.hiob
  have hroom : c.max_iob - c.iobd.iob.js = .fin (mi - i) := by rw [hi, hmi]; rfl
  unfold highTemp
  simp only
  have hcap := capped_nonPos (JsNum.round ((JsNum.min c.minPredBG c.eventualBG' - c.target_bg) / c.sens) 2)
    (w := mi - i) (by grind)
  rw [← hroom] at hcap
  generalize capInsulinReq (JsNum.round ((JsNum.min c.minPredBG c.eventualBG' - c.target_bg) / c.sens) 2)
    (c.max_iob - c.iobd.iob.js) = ir1 at hcap ⊢
  have hrate := req_le_basal (m := c.p.model) H.hb0 H.hbid hcap
  rw [← H.hb] at hrate
  generalize hs : (if (c.microBolusAllowed && c.enableSMB && c.bg >ʲ c.threshold) = true then
    smbBlock c ({ (rT.addReasonIf (JsNum.round ((JsNum.min c.minPredBG c.eventualBG' - c.target_bg) / c.sens) 2 >ʲ
      c.max_iob - c.iobd.iob.js) ("max_iob " ++ JsFmt.numToString c.max_iob ++ ", ")) with
        insulinReq := some (JsNum.round ir1 3) }) (JsNum.round ir1 3)
    else Sum.inr ({ (rT.addReasonIf (JsNum.round ((JsNum.min c.minPredBG c.eventualBG' - c.target_bg) / c.sens) 2 >ʲ
      c.max_iob - c.iobd.iob.js) ("max_iob " ++ JsFmt.numToString c.max_iob ++ ", ")) with
        insulinReq := some (JsNum.round ir1 3) })) = s
  have hsm := smbBlock_rate H.toDoseHyp
  have hreqM : (roundBasal (c.basal + 2 * ir1) c.p.model >ʲ getMaxSafeBasal c.p) = true →
      (roundBasal (getMaxSafeBasal c.p) c.p.model = .nan ∨
        ∃ x, roundBasal (getMaxSafeBasal c.p) c.p.model = .fin x ∧ x ≤ b) := by
    intro hgt
    right; rw [H.hM, roundBasal_fin]; refine ⟨_, rfl, ?_⟩
    rcases hrate with h0 | ⟨x, hx, hxb⟩
    · rw [h0] at hgt; simp at hgt
    · rw [hx, H.hM] at hgt; simp at hgt
      rw [← H.hbid]; exact rbR_mono _ (by grind)
  cases s with
  | inl res =>
    split at hs
    · have := (hsm _ _).1 res hs
      intro r hr; rcases this r hr with h1 | h1
      · left; simpa using h1
      · right; exact h1
    · cases hs
  | inr rT' =>
    have hr : rT'.rate = rT.rate := by
      split at hs
      · have := (hsm _ _).2 rT' hs; simpa using this
      · injection hs with hs; subst hs; simp
    simp only
    split
    · intro r h
      rcases highTempSet_le H _ _ _ (hreqM (by assumption)) r h with h1 | h1
      · left; rw [← hr]; simpa using h1
      · right; exact h1
    · intro r h
      rcases highTempSet_le H _ _ _ hrate r h with h1 | h1
      · left; rw [← hr]; exact h1
      · right; exact h1

theorem dbDoseRest_le {c : Ctx} {M b : Rat} (H : IobHyp c M b) (rT : Result) :
    RateOk b (dbDose.dbDoseRest c rT) rT.rate := by
  unfold dbDose.dbDoseRest
  simp only
  repeat' split
  all_goals first
    | exact rateOk_self _ _
    | exact rateOk_stb_le H.hM H.hM0 H.hb0 H.hbid (zeroReq b H.hb0)
    | exact neutralTemp_le H _
    | exact lowEventualBG_le H _
    | exact highTemp_le H _

theorem dbDose_le {c : Ctx} {M b : Rat} (H : IobHyp c M b) : RateOk b (dbDose c) c.rT.rate := by
  unfold dbDose
  simp only
  repeat' split
  all_goals first
    | exact rateOk_self _ _
    | exact rateOk_stb_le H.hM H.hM0 H.hb0 H.hbid (zeroReq b H.hb0)
    | exact dbDoseRest_le H _

end LeanAID.Proofs
