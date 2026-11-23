import LeanAID.Time.LowGlucose

/-!
# A patched low-glucose suspend, which deviates from oref0

**This file is not oref0.** `LeanAID.determineBasal` in `LeanAID/Core` is the transcription
of oref0 0.7.1 and stays unchanged. `determineBasalPatched` differs from it in one place:
the duration of the low-glucose zero temp. It is a proposed fix for F-23, and the theorems
below show that the pump model accepts the patched low-glucose command. The theorems about
oref0 are not affected.

**The oref0 code**, `lib/determine-basal/determine-basal.js:912-920` in oref0 0.7.1, with the
reason line shortened:
```
    } else if ( bg < threshold || minGuardBG < threshold ) {
        rT.reason += "minGuardBG " + ...;
        bgUndershoot = target_bg - minGuardBG;
        var worstCaseInsulinReq = bgUndershoot / sens;
        var durationReq = round(60*worstCaseInsulinReq / profile.current_basal);
        durationReq = round(durationReq/30)*30;
        // always set a 30-120m zero temp (oref0-pump-loop will let any longer SMB zero temp run)
        durationReq = Math.min(120,Math.max(30,durationReq));
        return tempBasalFunctions.setTempBasal(0, durationReq, profile, rT, currenttemp);
    }
```
In Lean this is the second branch of `LeanAID.dbDose`, with the duration `lgsDur c`.

**The patch.** After the last line that sets `durationReq`, a NaN duration becomes 30:
```
        durationReq = Math.min(120,Math.max(30,durationReq));
        if (isNaN(durationReq)) { durationReq = 30; }   // patch, not in oref0
```

**Why.** If `minGuardBG` is NaN, `Math.max(30, NaN)` is NaN, and oref0 issues rate 0 with a
NaN duration, `"duration": null` in JSON. A pump driver that rejects that command keeps the
temp that was running, so the suspension is lost while BG is low. oref0 reaches a NaN
`minGuardBG` with COB and no positive carbs (F-23, `scripts/probe-lgs-nan.js`). The value 30
is the shortest duration that oref0's own comment allows: "always set a 30-120m zero temp".
The next cycle sees the zero temp and decides again.

The root cause is the unguarded `fractionCarbsLeft = mealCOB / carbs` at line 709. The patch
does not change it, because then the patched predictions would differ from oref0 for these
inputs. A fix in oref0 has to guard both.

**Theorems.**
- `determineBasalPatched_eq`: the patched result equals oref0's result, unless the prelude
  succeeds and the low-glucose duration `lgsDur` is NaN.
- `lgs_patched`: if `inp` satisfies `ValidInput`, the prelude succeeds, BG or `minGuardBG` is below `threshold` and the
  first branch of the dose phase is not taken (`doseFirstBranch`), the patched result issues
  no units, and either sets rate 0 for a whole number of minutes in `[30, 120]`, or issues no
  rate and no duration while `currenttemp` has more than 20 minutes left and a rate that is
  0 if it is a double.
- `lgs_patched_valid`: under the same hypotheses, `validate` of the patched result is not
  `none`, so the pump model accepts it. For oref0 this fails (F-23).
- An example checked by `decide +kernel`: on `f23Input` oref0's result has a NaN duration and
  `validate` rejects it; the patched result is rate 0 for 30 minutes.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Patched

open LeanAID LeanAID.Proofs LeanAID.Time JsNum

/-- The patch: a NaN duration becomes 30 minutes. Other values are unchanged. -/
def patchDur : JsNum → JsNum
  | .nan => 30
  | x => x

/-- `LeanAID.dbDose` with the patched low-glucose duration. Every other branch, including
    the reason strings, is oref0's: it calls `LeanAID.dbDose`. -/
def dbDosePatched (c : Ctx) : Result :=
  if c.bg <ʲ c.threshold && c.iobd.iob.js <ʲ (-c.p.current_basal.js * 20 / 60) && c.minDelta >ʲ 0 &&
      c.minDelta >ʲ c.expectedDelta then dbDose c
  else if c.bg <ʲ c.threshold || c.minGuardBG <ʲ c.threshold then
    let rT := c.rT.addReason ("minGuardBG " ++ convertBgS c.minGuardBG c.p ++ "<" ++ convertBgS c.threshold c.p)
    -- oref0: setTempBasal(0, durationReq, ...) with durationReq = lgsDur c
    setTempBasal 0 (patchDur (lgsDur c)) c.p rT (some c.ct)
  else dbDose c

/-- `LeanAID.determineBasal` with the patched low-glucose duration. -/
def determineBasalPatched (inp : DBInputs) : Result :=
  match dbPrelude inp with
  | .error r => r
  | .ok pre => dbDosePatched (dbPredict inp pre)

/-- `patchDur` changes only NaN. -/
theorem patchDur_of_ne {x : JsNum} (h : x ≠ .nan) : patchDur x = x := by
  cases x with
  | nan => exact absurd rfl h
  | fin _ => rfl

/-- If the low-glucose duration `lgsDur c` is not NaN, then `dbDosePatched c = dbDose c`. -/
theorem dbDosePatched_eq (c : Ctx) (h : lgsDur c ≠ .nan) : dbDosePatched c = dbDose c := by
  unfold dbDosePatched
  split
  · rfl
  · rename_i h1
    split
    · rename_i h2
      rw [patchDur_of_ne h]
      unfold dbDose
      simp only [h1, h2, ↓reduceIte]
      rfl
    · rfl

/-- **The patch changes nothing else.** For every input `inp`, the patched result equals
    oref0's result, or `dbPrelude inp = ok pre` for some `pre` and oref0's low-glucose duration
    `lgsDur (dbPredict inp pre)` is NaN. -/
theorem determineBasalPatched_eq (inp : DBInputs) :
    determineBasalPatched inp = determineBasal inp ∨
    ∃ pre, dbPrelude inp = .ok pre ∧ lgsDur (dbPredict inp pre) = .nan := by
  unfold determineBasalPatched determineBasal
  cases hp : dbPrelude inp with
  | error r => left; rfl
  | ok pre =>
    by_cases hd : lgsDur (dbPredict inp pre) = .nan
    · right; exact ⟨pre, rfl, hd⟩
    · left; exact dbDosePatched_eq _ hd

/-- The patched duration is a whole number of minutes in `[30, 120]`. -/
theorem patchDur_lgsDur (c : Ctx) : ∃ q : Int, patchDur (lgsDur c) = .fin q ∧ 30 ≤ q ∧ q ≤ 120 := by
  rcases lgsDur_cases c with h | ⟨q, hq, h1, h2⟩
  · rw [h]; exact ⟨30, rfl, by decide, by decide⟩
  · rw [hq]; exact ⟨q, rfl, h1, h2⟩

/-- **Low glucose suspend, patched.** Let `inp` be a valid input whose prelude succeeds with
    `pre`, with BG or the predicted `minGuardBG` below `threshold`, and
    `doseFirstBranch pre = false`. Then the patched result issues no units, and either sets
    rate 0 with a whole number of minutes in `[30, 120]`, or issues no rate and no duration
    while `currenttemp` has more than 20 minutes left and a rate that is 0 if it is a
    double. -/
theorem lgs_patched {inp : DBInputs} (hv : ValidInput inp) {pre : Pre} (hpre : dbPrelude inp = .ok pre)
    (hlow : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true)
    (hfirst : doseFirstBranch pre = false) :
    (determineBasalPatched inp).units = none ∧
    (((determineBasalPatched inp).rate = some 0 ∧
        ∃ q : Int, (determineBasalPatched inp).duration = some (.fin q) ∧ 30 ≤ q ∧ q ≤ 120) ∨
     ((determineBasalPatched inp).rate = none ∧ (determineBasalPatched inp).duration = none ∧
       ∃ c ctDur x, inp.currenttemp = some c ∧ c.duration = some (.fin ctDur) ∧ 20 < ctDur ∧
         c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) := by
  obtain ⟨M, cb, hM, hM0, hcb, hcb0, hct, hexc, hlow'⟩ := lgs_setup hv hpre hlow hfirst
  unfold determineBasalPatched
  rw [hpre]
  simp only
  unfold dbDosePatched
  simp only [hexc, hlow', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨q, hq, hq30, hq120⟩ := patchDur_lgsDur (dbPredict inp pre)
  rw [hq]
  obtain ⟨hu, hr⟩ := setTempBasal_zero_lgs (Or.inr ⟨q, rfl, hq30, hq120⟩)
    (rT := (dbPredict inp pre).rT.addReason ("minGuardBG " ++ convertBgS (dbPredict inp pre).minGuardBG (dbPredict inp pre).p ++ "<" ++
      convertBgS (dbPredict inp pre).threshold (dbPredict inp pre).p))
    (ct := some (dbPredict inp pre).ct) hM hM0 hcb hcb0
  refine ⟨by rw [hu]; rfl, ?_⟩
  rcases hr with ⟨hr, hd⟩ | ⟨hr, hd, c, ctDur, x, hc, rest⟩
  · exact Or.inl ⟨hr, q, hd, hq30, hq120⟩
  · exact Or.inr ⟨by rw [hr]; rfl, by rw [hd]; rfl, c, ctDur, x, by rw [hct, hc], rest⟩

/-- **The pump accepts the patched command.** Let `inp` be a valid input whose prelude
    succeeds with `pre`, with BG or the predicted `minGuardBG` below `threshold`, and
    `doseFirstBranch pre = false`. Then `validate` of the patched result is not `none`. -/
theorem lgs_patched_valid {inp : DBInputs} (hv : ValidInput inp) {pre : Pre} (hpre : dbPrelude inp = .ok pre)
    (hlow : (pre.bg <ʲ pre.threshold) = true ∨ ((dbPredict inp pre).minGuardBG <ʲ pre.threshold) = true)
    (hfirst : doseFirstBranch pre = false) :
    validate (determineBasalPatched inp) ≠ none := by
  obtain ⟨hu, h⟩ := lgs_patched hv hpre hlow hfirst
  rcases h with ⟨hr, q, hd, h30, h120⟩ | ⟨hr, hd, -⟩
  · simp [validate, validateTemp, validateBolus, validDuration, hr, hd, hu,
      show (30 : Rat) ≤ q by exact_mod_cast h30, show (q : Rat) ≤ 120 by exact_mod_cast h120]
  · simp [validate, validateTemp, validateBolus, hr, hd, hu]

/-! ### The F-23 input

`f23Input` is the input of case A of `scripts/probe-lgs-nan.js`: BG 60 mg/dL rising
3 mg/dL per 5 minutes, target 100 and threshold 70, `enableUAM`, `mealCOB` 20 and no
`carbs`, zero IOB. The example below checks that `LeanAID.determineBasal` returns rate 0 with
a NaN duration, which `validate` rejects, and that the patched version returns rate 0 for
30 minutes. The probe shows the same NaN duration in Node. -/

/-- The start time of the example, epoch ms. -/
def t0 : Int := 1794970800000

/-- Case A of `scripts/probe-lgs-nan.js`, with the glucose status given directly. -/
def f23Input : DBInputs :=
  { glucose_status := some { glucose := some 60, delta := some 3, short_avgdelta := some 3, long_avgdelta := some 3,
                             date := some (.fin t0) },
    currenttemp := some { duration := some 0, rate := some 0, temp := some "absolute" },
    iob_data := some (.array ((List.range 48).map fun k =>
      if k == 0 then { iob := some 0, activity := some 0, iobWithZeroTemp := some (some 0),
                       lastBolusTime := some (.fin (t0 - 10800000)) }
      else { iob := some 0, activity := some 0, iobWithZeroTemp := some (some 0) })),
    profile := some { current_basal := some 1, max_basal := some 3, max_daily_basal := some 1, max_iob := some 1,
                      sens := some 50, carb_ratio := some 10, min_bg := some 100, max_bg := some 100,
                      enableUAM := some true },
    meal_data := some { mealCOB := some 20 },
    clock := { now := t0 } }

example : (determineBasal f23Input).rate = some 0 ∧ (determineBasal f23Input).duration = some .nan ∧
    validate (determineBasal f23Input) = none ∧
    (determineBasalPatched f23Input).rate = some 0 ∧ (determineBasalPatched f23Input).duration = some 30 := by
  decide +kernel

end LeanAID.Patched
