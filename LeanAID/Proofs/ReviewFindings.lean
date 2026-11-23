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

/-- Let `now` and `n` be whole-millisecond times with `timeClip(date) = n`, that is,
    `new Date(glucose_status.date)` gives `n`. If the age `a = (now − n)/60000` in minutes
    satisfies `a ≥ 12.05` or `a < −5.05`, then `cgmStale` holds. The margin of 0.05 covers
    oref0's rounding of the age to 0.1 minutes before it compares with 12 and −5. -/
theorem stale_of_clip {now n : Int} {gs : GlucoseStatus}
    (hc : DateFmt.timeClip gs.date.js = .fin (n : Rat))
    (h : ((now - n : Int) : Rat) / 60000 ≥ 12 + 1/20 ∨ ((now - n : Int) : Rat) / 60000 < -5 - 1/20) :
    cgmStale (gluVals (.fin now) gs) = true := by
  unfold cgmStale gluVals
  simp only [hc, JsNum.fin_sub]
  rw [show (60 : JsNum) = .fin 60 from rfl, show (1000 : JsNum) = .fin 1000 from rfl,
    JsNum.fin_div (by decide), JsNum.fin_div (by decide), rnd, rnd_fin]
  have hp10 : pow10 1 = 10 := by decide +kernel
  rw [hp10]
  -- the age in minutes, rounded to 0.1, is monotone in the integer age `z` in ms
  have hz : (now : Rat) - (n : Rat) = ((now - n : Int) : Rat) := by push_cast; rfl
  rw [hz]
  generalize now - n = z at h ⊢
  have mono : ∀ a b : Rat, a ≤ b →
      rts (Binary64.rd (Binary64.rd (Binary64.rd a / 60) / 1000)) 10 ≤
        rts (Binary64.rd (Binary64.rd (Binary64.rd b / 60) / 1000)) 10 := by
    intro a b hab
    apply rts_mono (by decide)
    apply Binary64.rd_mono; apply div_le_div_of_le (by decide)
    apply Binary64.rd_mono; apply div_le_div_of_le (by decide)
    exact Binary64.rd_mono hab
  rcases h with h | h
  · -- z ≥ 723000 ms (12.05 min): rounded age ≥ 12.1
    have hz : ((723000 : Int) : Rat) ≤ (z : Rat) := by
      have : (12 + 1/20 : Rat) * 60000 ≤ (z : Rat) := by
        rw [ge_iff_le, le_div_iff_mul_le (by decide)] at h; exact h
      have e : (12 + 1/20 : Rat) * 60000 = ((723000 : Int) : Rat) := by decide +kernel
      rwa [e] at this
    have := mono _ _ hz
    have k : (12 : Rat) < rts (Binary64.rd (Binary64.rd (Binary64.rd ((723000 : Int) : Rat) / 60) / 1000)) 10 := by
      decide +kernel
    simp only [JsNum.ofNat_eq, JsNum.gt_fin, Bool.or_eq_true, decide_eq_true_eq]; left; grind
  · -- z ≤ -303001 ms (below -5.05 min): rounded age ≤ -5.1
    have hz : (z : Rat) ≤ ((-303001 : Int) : Rat) := by
      have : (z : Rat) < (-5 - 1/20 : Rat) * 60000 := (Rat.div_lt_iff (by decide)).mp h
      have e : (-5 - 1/20 : Rat) * 60000 = ((-303000 : Int) : Rat) := by decide +kernel
      rw [e] at this
      have : z < -303000 := Rat.intCast_lt_intCast.mp this
      exact Rat.intCast_le_intCast.mpr (show z ≤ -303001 by omega)
    have := mono _ _ hz
    have k : rts (Binary64.rd (Binary64.rd (Binary64.rd ((-303001 : Int) : Rat) / 60) / 1000)) 10 < -5 := by
      decide +kernel
    simp only [Bool.or_eq_true]
    right; show (JsNum.fin (rts _ 10) <ʲ JsNum.fin (-5)) = true
    simp; grind

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
      unfold cgmBad gluVals; simp only [hb, Option.js_some, show (10 : JsNum) = .fin 10 from rfl, show (38 : JsNum) = .fin 38 from rfl, show (3 : JsNum) = .fin 3 from rfl, JsNum.le_fin, JsNum.seq_fin, decide_eq_true_eq, Bool.or_eq_true]
      rcases h with h | h
      · left; left; exact h
      · left; right; exact h
    simp [this]
  · have : cgmBad (gluVals (.fin inp.clock.now) gs) = true := by
      unfold cgmBad gluVals; simp only [hn, Option.js_some, show (10 : JsNum) = .fin 10 from rfl, show (38 : JsNum) = .fin 38 from rfl, show (3 : JsNum) = .fin 3 from rfl, JsNum.ge_fin, decide_eq_true_eq, Bool.or_eq_true]
      right; exact h
    simp [this]
  · have : cgmStale (gluVals (.fin inp.clock.now) gs) = true := by
      apply stale_of_clip (n := d) (by simp [hd, Option.js_some, timeClip_int])
      have hz : (inp.clock.now - d : Rat) = ((inp.clock.now - d : Int) : Rat) := by push_cast; rfl
      rwa [hz] at h
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
