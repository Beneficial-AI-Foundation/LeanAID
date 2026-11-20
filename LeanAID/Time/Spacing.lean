import LeanAID.Time.IobFacts
import LeanAID.Time.Duration
import LeanAID.Proofs.Headline

/-!
# Spacing of microboluses in real time

oref0 issues a microbolus only when its rounded age of the last bolus,
`round((now − lastBolusTime) / 60000, 1)`, exceeds `SMBInterval` (`microbolus_limits`).
In a legal run, `Legal.bolusSeen` gives `lastBolusTime ≥ t₁` for every earlier accepted bolus
of nonzero units at `t₁`. The rounded age is monotone in the gap (`ageOf_mono`), so the bound
also holds for the real gap.

Throughout, `I` is the `SMBInterval` of `env.profile`. `smbInterval` does not read
`current_basal`, so every cycle sees the same `I`.

**Theorems.**
- `gap_of_age`: if `1 ≤ I < ageOf x`, then `60000·I − 3000 − 2⁻³⁰ < x · (1 + 2⁻⁵⁰)`: a gap of
  `x` ms is more than `I − 0.05` minutes up to double rounding.
- `p5_gap`: in a legal run with `ValidEnv` and `AutosensOk`, let a cycle at `t₂` issue a
  microbolus. Every bolus of nonzero units at `t₁` in the log before the cycle satisfies
  `I < ageOf (t₂ − t₁)` and the bound of `gap_of_age` for `t₂ − t₁`.
- `p5_strict`: under the same hypotheses, `t₁ < t₂`.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Iob LeanAID.Proofs Binary64

/-- oref0's age in minutes of a gap of `x` ms, `round((now − lastBolusTime) / 60000, 1)` in
    doubles (`determine-basal.js:1072`): `x` is the exact difference, and `rd x` is its
    double subtraction. -/
def ageOf (x : Rat) : Rat := rts (rd (rd x / 60000)) 10

theorem ageOf_mono {x y : Rat} (h : x ≤ y) : ageOf x ≤ ageOf y := by
  unfold ageOf
  apply rts_mono (by decide)
  apply rd_mono
  exact div_le_div_of_le (by decide) (rd_mono h)

theorem age_fin (t : Int) (L : Rat) :
    JsNum.round ((JsNum.fin t - JsNum.fin L) / 60000) 1 = .fin (ageOf (t - L)) := by
  show JsNum.round (JsNum.fin (rd ((t : Rat) - L)) / JsNum.fin 60000) 1 = _
  rw [JsNum.fin_div (by decide)]
  have h10 : JsNum.pow10 1 = 10 := by simp [JsNum.pow10]
  unfold JsNum.round
  rw [h10]
  show roundToScale (JsNum.fin (rd (rd ((t : Rat) - L) / 60000))) 10 = _
  rw [roundToScale_fin _ (by decide)]
  rfl

/-- If `1 ≤ I` and `I < ageOf x`, then `60000·I − 3000 − 2⁻³⁰ < x · (1 + 2⁻⁵⁰)`: a gap of `x`
    ms whose rounded age exceeds `I` minutes is more than `I − 0.05` minutes, up to double
    rounding. -/
theorem gap_of_age {x I : Rat} (hI : 1 ≤ I) (h : I < ageOf x) :
    60000 * I - 3000 - 1 / 2 ^ 30 < x * (1 + 1 / 2 ^ 50) := by
  by_cases hx : x < 0
  · exfalso
    have a1 : rd x ≤ 0 := rd_nonpos (Rat.le_of_lt hx)
    have a2 : ageOf x ≤ 0 := rts_nonpos (by decide) (rd_nonpos (show rd x / 60000 ≤ 0 by grind))
    grind
  · unfold ageOf rts at h
    have ht := tiny_le
    have ht0 := Rat.le_of_lt tiny_pos
    have hx0 : 0 ≤ x := Rat.not_lt.mp hx
    have c1 := (rd_close hx0).2
    have p1 : 0 ≤ rd x := rd_nonneg hx0
    have q1 : 0 ≤ rd x / 60000 := div_nonneg' (by decide) p1
    have c2 := (rd_close q1).2
    have p2 : 0 ≤ rd (rd x / 60000) := rd_nonneg q1
    have q2 : 0 ≤ rd (rd x / 60000) * 10 := by grind
    have c3 := (rd_close q2).2
    have p3 : 0 ≤ rd (rd (rd x / 60000) * 10) := rd_nonneg q2
    have k1 := roundInt_le (rd (rd (rd x / 60000) * 10))
    have k0 : 0 ≤ JsNum.roundInt (rd (rd (rd x / 60000) * 10)) := roundInt_nonneg p3
    have q4 : 0 ≤ ((JsNum.roundInt (rd (rd (rd x / 60000) * 10)) : Int) : Rat) / 10 :=
      div_nonneg' (by decide) (by exact_mod_cast k0)
    have c4 := (rd_close q4).2
    grind

theorem smbInterval_ge {p : Profile} {I : Rat} (h : smbInterval p = .fin I) : 1 ≤ I := by
  unfold smbInterval at h
  split at h
  · cases hx : p.SMBInterval.js with
    | nan => rw [hx] at h; simp [JsNum.max, JsNum.min] at h
    | fin x =>
      rw [hx] at h
      simp only [JsNum.max, JsNum.min] at h
      have := JsNum.fin.inj h
      subst this
      split <;> split <;> grind
  · have := JsNum.fin.inj h; subst this; decide

theorem smbInterval_profileAt (env : Env) (t : Int) :
    smbInterval (env.profileAt t) = smbInterval env.profile := rfl

theorem iobOut_ticks (env : Env) (s : PState) (t : Int) (a : Option Autosens) :
    ∃ x y rest, (iobOut env s t a).ticks = x :: y :: rest := ⟨_, _, _, rfl⟩

/-- In a legal cycle whose prelude succeeds with `pre`, the `lastBolusTime` that the
    controller reads is the one of `iobOut`. -/
theorem prelude_lastBolusTime {env : Env} {t : Int} {s : PState} {inp : DBInputs} {res : Result}
    (hc : LegalCycle env t s inp res) {pre : Pre} (hpre : dbPrelude inp = .ok pre) :
    pre.iobd.lastBolusTime = some (iobOut env s t inp.autosens_data).lastBolusTime := by
  obtain ⟨p, g, mm, io, ct, meal, -, -, -, hio, -, -, -, -, hiobd, -⟩ := prelude_ok hpre
  rw [hiobd]
  obtain ⟨x, y, rest, hticks⟩ := iobOut_ticks env s t inp.autosens_data
  unfold stIob at hio
  rw [hc.iob] at hio
  simp only [iobInputOf, hticks, List.zipIdx_cons, List.map_cons] at hio
  split at hio
  · cases hio
  · cases hio; rfl

/-- **Spacing of microboluses.** Let `r` be a legal run with `ValidEnv env`,
    `AutosensOk env r` and `smbInterval env.profile = .fin I`, let `c` be a cycle of `r` whose
    result has finite units, and let `bolus t₁ u₁` with `u₁ ≠ 0` be in `c.pre.log`. Then
    `I < ageOf (c.time − t₁)` and `60000·I − 3000 − 2⁻³⁰ < (c.time − t₁) · (1 + 2⁻⁵⁰)`: the
    gap exceeds `I − 0.05` minutes up to double rounding. -/
theorem p5_gap {env : Env} {r : Run Event} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) {c : CycleAt} (hc : c ∈ cycles env r) {u : Rat}
    (hu : c.res.units = some (.fin u)) {t1 : Int} {u1 : Rat} {smb : Bool}
    (hb : Action.bolus t1 u1 smb ∈ c.pre.log) (hu1 : u1 ≠ 0) {I : Rat}
    (hI : smbInterval env.profile = .fin I) :
    I < ageOf (c.time - t1) ∧
      60000 * I - 3000 - 1 / 2 ^ 30 < ((c.time - t1 : Int) : Rat) * (1 + 1 / 2 ^ 50) := by
  have hv := validRun_of hl he ha c hc
  have hlc := hl.cycle c hc
  rw [hlc.result] at hu
  obtain ⟨pre, hpre, hlim⟩ := microbolus_limits hv hu
  simp only at hlim
  have hage := hlim.2.2.2
  obtain ⟨p, g, mm, io, ct, meal, h1, -, -, -, -, -, hpp, -⟩ := prelude_ok hpre
  have hp : p = env.profileAt c.time := by
    have := stProfile_ok h1; rw [hlc.profile] at this; exact (Option.some.inj this).symm
  have hlbt := prelude_lastBolusTime hlc hpre
  obtain ⟨y, hy, hty⟩ := hl.bolusSeen hc hb hu1
  have hI' : smbInterval pre.p = .fin I := by rw [hpp, hp, smbInterval_profileAt, hI]
  have hA : lastBolusAge (dbPredict c.inp pre) = .fin (ageOf (c.time - y)) := by
    show JsNum.round ((JsNum.fin c.inp.clock.now - pre.iobd.lastBolusTime.js) / 60000) 1 = _
    rw [hlbt, hy, hlc.now]
    exact age_fin c.time y
  rw [hA, hI'] at hage
  have hlt : I < ageOf (c.time - y) := by simpa using hage
  have hmono : ageOf ((c.time : Rat) - y) ≤ ageOf ((c.time - t1 : Int) : Rat) := by
    apply ageOf_mono; push_cast; grind
  have h1' : I < ageOf ((c.time - t1 : Int) : Rat) := by grind
  refine ⟨by simpa using h1', gap_of_age (smbInterval_ge hI) h1'⟩

/-- Under the hypotheses of `p5_gap`, `t₁ < c.time`: a bolus of nonzero units in the log
    before a cycle that issues a microbolus is strictly earlier than the cycle, also when it
    was logged earlier in the same step. -/
theorem p5_strict {env : Env} {r : Run Event} (hl : Legal env r) (he : ValidEnv env)
    (ha : AutosensOk env r) {c : CycleAt} (hc : c ∈ cycles env r) {u : Rat}
    (hu : c.res.units = some (.fin u)) {t1 : Int} {u1 : Rat} {smb : Bool}
    (hb : Action.bolus t1 u1 smb ∈ c.pre.log) (hu1 : u1 ≠ 0) {I : Rat}
    (hI : smbInterval env.profile = .fin I) : t1 < c.time := by
  have h := (p5_gap hl he ha hc hu hb hu1 hI).2
  have h1 := smbInterval_ge hI
  have hcast : ((c.time - t1 : Int) : Rat) ≤ 0 ∨ t1 < c.time := by
    by_cases h' : t1 < c.time
    · exact Or.inr h'
    · left; have : c.time - t1 ≤ 0 := by omega
      exact_mod_cast this
  rcases hcast with h0 | h0
  · exfalso
    have := Rat.mul_le_mul_of_nonneg_right h0 (show (0 : Rat) ≤ 1 + 1 / 2 ^ 50 by decide +kernel)
    rw [Rat.zero_mul] at this
    grind
  · exact h0

end LeanAID.Time
