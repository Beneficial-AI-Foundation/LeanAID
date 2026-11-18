/-
  LeanAID.Proofs.ReviewFindings — findings and restatements prompted by the
  independent review (docs/LOG.md, "Review fixes").
-/
import LeanAID.Proofs.Hypo
import LeanAID.Spec.ValidCheck

namespace LeanAID.Proofs

open JsNum

/-- The test-file profile of oref0's determine-basal tests. -/
def reviewProfile : Profile :=
  { max_iob := some 2.5, dia := some 3, current_basal := some 0.9, max_daily_basal := some 1.3,
    max_basal := some 3.5, max_bg := some 120, min_bg := some 110, sens := some 40, carb_ratio := some 10 }

/-! ### F-11: undated glucose disables the staleness check -/

/-- A reading without a `date` is never considered stale or from the future:
    `minAgo` is NaN and both comparisons are false (determine-basal.js 149-150, 187). -/
theorem undated_never_stale (now : JsNum) (gs : GlucoseStatus) (h : gs.date = none) :
    cgmStale (gluVals now gs) = false := by
  simp [cgmStale, gluVals, h, DateFmt.timeClip, rnd, JsNum.round]

/-- **F-11.** BG 250 mg/dL and rising, with no `date` on the glucose reading: oref0
    (and the faithful transcription) issues the maximum temp basal, 3.5 U/h for 30
    minutes, however old the reading actually is. With a `date` 60 minutes old the
    same input is refused as stale. -/
theorem undated_glucose_max_rate :
    let base : DBInputs :=
      { glucose_status := some { glucose := some 250, delta := some 5, short_avgdelta := some 5, long_avgdelta := some 5 }
        currenttemp := some { duration := some 0, rate := some 0, temp := some "absolute" },
        iob_data := some (.single { iob := some 0, activity := some 0 }),
        profile := some reviewProfile, autosens_data := some { ratio := some 1 }, meal_data := some {},
        clock := { now := 1795003200000 } }
    (determineBasal base).rate = some 3.5 ∧ (determineBasal base).duration = some 30 ∧
    (determineBasal { base with glucose_status := some { glucose := some 250, delta := some 5, short_avgdelta := some 5, long_avgdelta := some 5, date := some (.fin (1795003200000 - 3600000)) } }).rate = none := by
  decide +kernel

/-! ### R12 restated with hypotheses independent of the implementation -/

theorem timeClip_int (d : Int) : DateFmt.timeClip (.fin (d : Rat)) = .fin (d : Rat) := by
  show JsNum.fin (if (d : Rat) < 0 then -(((-(d : Rat))).floor : Rat) else ((d : Rat).floor : Rat)) = _
  rw [show (-(d : Rat)) = ((-d : Int) : Rat) by push_cast; rfl, Rat.floor_intCast, Rat.floor_intCast]
  split <;> simp

/-- **H5a (R12), with independent hypotheses.** If the glucose reading is an error
    code (BG ≤ 10 or BG = 38), or noise ≥ 3, or the reading is dated and at least
    12.05 minutes old or more than 5.05 minutes in the future, or oref0's flat-data
    condition holds, then oref0 issues no microbolus and never increases insulin.
    (The 0.05-minute margin is oref0's rounding of the age to 0.1 minute.)

    NOT covered: a reading with **no `date`** (or a non-numeric one) is never treated
    as stale (F-11, `undated_glucose_max_rate`), and a NaN `noise` is never treated as
    noisy. Such readings get the full dosing decision. -/
theorem cgm_unreliable_no_increase {inp : DBInputs} {p : Profile} {gs : GlucoseStatus}
    (hp : inp.profile = some p) (hcb : p.current_basal.isSome) (hgs : inp.glucose_status = some gs)
    (hbad : (∃ b : Rat, gs.glucose = some (.fin b) ∧ (b ≤ 10 ∨ b = 38)) ∨
            (∃ n : Rat, gs.noise = some (.fin n) ∧ 3 ≤ n) ∨
            (∃ d : Int, gs.date = some (.fin (d : Rat)) ∧
              ((inp.clock.now - d : Rat) / 60000 ≥ 12 + 1/20 ∨ (inp.clock.now - d : Rat) / 60000 < -5 - 1/20)) ∨
            cgmFlat (gluVals (.fin inp.clock.now) gs) = true) :
    let r := determineBasal inp
    r.units = none ∧
    ((∃ ct, inp.currenttemp = some ct ∧ (ct.rate.js >ʲ profileCurrentBasal p) = true ∧
        r.rate = some (profileCurrentBasal p)) ∨
     r.rate = some 0 ∨
     (r.rate = none ∧ ∀ ct, inp.currenttemp = some ct → (ct.rate.js >ʲ profileCurrentBasal p) = false)) := by
  apply cgmError_no_increase hp hcb hgs
  unfold cgmError
  rcases hbad with ⟨b, hb, h⟩ | ⟨n, hn, h⟩ | ⟨d, hd, h⟩ | h
  · have : cgmBad (gluVals (.fin inp.clock.now) gs) = true := by
      unfold cgmBad gluVals; simp only [hb, Option.js_some, show (10 : JsNum) = .fin 10 from rfl, show (38 : JsNum) = .fin 38 from rfl, show (3 : JsNum) = .fin 3 from rfl, JsNum.le_fin, JsNum.seq_fin, JsNum.ge_fin, decide_eq_true_eq, Bool.or_eq_true]
      rcases h with h | h
      · left; left; exact h
      · left; right; exact h
    simp [this]
  · have : cgmBad (gluVals (.fin inp.clock.now) gs) = true := by
      unfold cgmBad gluVals; simp only [hn, Option.js_some, show (10 : JsNum) = .fin 10 from rfl, show (38 : JsNum) = .fin 38 from rfl, show (3 : JsNum) = .fin 3 from rfl, JsNum.le_fin, JsNum.seq_fin, JsNum.ge_fin, decide_eq_true_eq, Bool.or_eq_true]
      right; exact h
    simp [this]
  · have : cgmStale (gluVals (.fin inp.clock.now) gs) = true := by
      unfold cgmStale gluVals
      simp only [hd, Option.js_some, timeClip_int, JsNum.fin_sub]
      rw [show (60 : JsNum) = .fin 60 from rfl, show (1000 : JsNum) = .fin 1000 from rfl,
        JsNum.fin_div (by decide), JsNum.fin_div (by decide), rnd, rnd_fin]
      have e : ((inp.clock.now : Rat) - (d : Rat)) / 60 / 1000 = ((inp.clock.now : Rat) - d) / 60000 := by grind
      rw [e]
      have hp10 : pow10 1 = 10 := by decide +kernel
      rw [hp10]
      generalize ((inp.clock.now : Rat) - d) / 60000 = a at h ⊢
      have h1 := lt_rts_mul (x := a) (s := 10) (by decide)
      have h2 := rts_mul_le (x := a) (s := 10) (by decide)
      rcases h with h | h
      · simp only [JsNum.ofNat_eq, JsNum.gt_fin, Bool.or_eq_true, decide_eq_true_eq]; left; grind
      · simp only [Bool.or_eq_true, decide_eq_true_eq]
        right; show (JsNum.fin (rts a 10) <ʲ JsNum.fin (-5)) = true
        simp; grind
    simp [this]
  · simp [h]

/-! ### F-12: missing `max_basal` disables the clamp -/

/-- **F-12.** Without `max_basal` and `max_daily_basal`, `maxSafeBasal` is NaN, the
    clamp in `setTempBasal` never fires (comparisons with NaN are false), and oref0
    issues 5.9 U/h for `current_basal` 0.9 (BG 300 and rising). `aid-lean --safe`
    refuses this input (`validInputB` is false). -/
theorem missing_max_basal_no_clamp :
    let inp : DBInputs :=
      { glucose_status := some { glucose := some 300, delta := some 5, short_avgdelta := some 5, long_avgdelta := some 5, date := some (.fin 1795003200000) }
        currenttemp := some { duration := some 0, rate := some 0, temp := some "absolute" },
        iob_data := some (.single { iob := some 0, activity := some 0 }),
        profile := some { reviewProfile with max_basal := none, max_daily_basal := none },
        autosens_data := some { ratio := some 1 }, meal_data := some {}, clock := { now := 1795003200000 } }
    getMaxSafeBasal { reviewProfile with max_basal := none, max_daily_basal := none } = .nan ∧
    (determineBasal inp).rate = some 5.9 ∧ validInputB inp = false := by
  decide +kernel

end LeanAID.Proofs
