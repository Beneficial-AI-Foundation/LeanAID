import LeanAID.Time.Delivery
import LeanAID.Proofs.ValidCheck

/-!
# Checkable configuration hypotheses

The run theorems assume `ValidEnv env`, `RateCap env B` and the schedule cap

```text
∀ k, env.sched k ≤ B.
```

Each quantifies over all times. This file derives them from `ValidSchedule env`, a Boolean
condition on the entries of `env.profile.basalprofile` and on the other profile fields, which
`decide` checks on a concrete profile.

`basalLookup` returns `none` or the value `lookupRate e = round(1000 · e.rate) / 1000` for some
entry `e` of the schedule. It returns `none` when the schedule is empty or the last entry after
sorting by `i` has rate 0 (F-22). `ValidSchedule env` states that the schedule is not empty and
that, for every entry `e`, the profile with `current_basal := lookupRate e` passes
`validProfileB`. A rate-0 entry fails that check, so `basalLookup` never returns `none` under
`ValidSchedule`.

**Theorems.**
- `basalLookup_some`, `basalLookup_none`, `basalLookup_last_zero`: what `basalLookup`
  returns.
- `validEnv_of_schedule`: `ValidSchedule env` implies `ValidEnv env`.
- `rateCap_of_schedule`, `sched_le_of_schedule`: under `ValidSchedule env`, `scheduleCap env`
  satisfies `RateCap` and the schedule cap.
- `smbMaxBolus_sched`: under `ValidSchedule env` and `SmbMinutesOk env`
  (`maxSMBBasalMinutes` absent or finite), `smbMaxBolus` of every context whose profile is
  `env.profileAt t` is finite and at most `smbCapOf env`, the one-decimal rounding of
  `(largest schedule rate) · max(30, maxSMBBasalMinutes, maxUAMSMBBasalMinutes) / 60` in
  double arithmetic.
- `autosensOk_of_clamped`: `ValidEnv` and a ratio at most `autosens_max`
  (`AutosensClamped`) imply `AutosensOk`.
- The concrete profile `envS` passes `ValidSchedule` by `decide +kernel`, and `envZ`, whose
  last rate is 0, fails it.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Proofs LeanAID.Iob JsNum

/-! ### What `basalLookup` returns -/

/-- The value `basalLookup` returns when it picks the entry `e`: `round(1000 · e.rate) / 1000`
    in JavaScript arithmetic, with `round` oref0's `Math.round`. -/
def lookupRate (e : BasalEntry) : JsNum := mathRound (e.rate * 1000) / 1000

theorem find_mem (data : Array BasalEntry) (b0 nm : JsNum) (hb0 : ∃ e ∈ data, e.rate = b0) :
    ∀ fuel i, ∃ e ∈ data, e.rate = basalLookup.find data b0 nm i fuel
  | 0, i => by simpa [basalLookup.find] using hb0
  | fuel + 1, i => by
    unfold basalLookup.find
    split
    · rename_i hi
      split
      · refine ⟨data[i], Array.getElem_mem _, ?_⟩
        rw [getElem!_pos data i (by omega)]
      · exact find_mem data b0 nm hb0 fuel (i + 1)
    · exact hb0

/-- When `basalLookup` returns a value, it is `lookupRate e` for an entry `e` of the
    schedule. -/
theorem basalLookup_some {l : List BasalEntry} {now : JsNum} {tz : Int} {v : JsNum}
    (h : basalLookup l now tz = some v) : ∃ e ∈ l, v = lookupRate e := by
  unfold basalLookup at h
  simp only at h
  split at h
  · cases h
  · rename_i hsz
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      have hb0 : ∃ e ∈ (sortByKey (fun e => e.i.js) l).toArray,
          e.rate = ((sortByKey (fun e => e.i.js) l).toArray)[(sortByKey (fun e => e.i.js) l).toArray.size - 1].rate :=
        ⟨_, Array.getElem_mem _, rfl⟩
      obtain ⟨e, he, hr⟩ := find_mem _ _ _ hb0 _ 0
      refine ⟨e, ?_, by rw [lookupRate, hr]⟩
      have : e ∈ sortByKey (fun e => e.i.js) l := by simpa using he
      exact (mem_sortByKey _ _ _).mp this

/-- If `basalLookup l now tz = none`, then `l` is empty or some entry of `l` has rate 0. -/
theorem basalLookup_none {l : List BasalEntry} {now : JsNum} {tz : Int}
    (h : basalLookup l now tz = none) : l = [] ∨ ∃ e ∈ l, (e.rate =ʲ 0) = true := by
  unfold basalLookup at h
  simp only at h
  split at h
  · rename_i hsz
    left
    have : (sortByKey (fun e => e.i.js) l).length = 0 := by simpa using hsz
    rw [length_sortByKey] at this
    exact List.eq_nil_of_length_eq_zero this
  · rename_i hsz
    split at h
    · rename_i hz
      right
      refine ⟨_, ?_, hz⟩
      have : ((sortByKey (fun e => e.i.js) l).toArray)[(sortByKey (fun e => e.i.js) l).toArray.size - 1]
          ∈ sortByKey (fun e => e.i.js) l := by
        simp
      exact (mem_sortByKey _ _ _).mp this
    · cases h

/-- Let `e` be the last entry of the schedule `l` after sorting by `i`. If `e` has rate 0,
    then `basalLookup l now tz = none` at every time `now`, as in
    `lib/profile/basal.js:14-19` (F-22). -/
theorem basalLookup_last_zero {l : List BasalEntry} {now : JsNum} {tz : Int} {e : BasalEntry}
    (hl : (sortByKey (fun e => e.i.js) l).getLast? = some e) (hz : (e.rate =ʲ 0) = true) :
    basalLookup l now tz = none := by
  unfold basalLookup
  simp only
  split
  · rfl
  · have : ((sortByKey (fun e => e.i.js) l).toArray)[(sortByKey (fun e => e.i.js) l).toArray.size - 1] = e := by
      rw [List.getLast?_eq_getElem?] at hl
      simp only [List.getElem?_eq_some_iff] at hl
      obtain ⟨_, hl⟩ := hl
      simpa using hl
    rw [this, hz]; rfl

theorem lookupRate_of_zero {e : BasalEntry} (h : (e.rate =ʲ 0) = true) : lookupRate e = .fin 0 := by
  cases hr : e.rate with
  | nan => rw [hr] at h; cases h
  | fin x =>
    rw [hr] at h
    simp only [JsNum.seq, decide_eq_true_eq] at h
    have hx : x = 0 := by
      have := h; revert this; show (x = (OfNat.ofNat 0 : Rat)) → x = 0; exact id
    subst hx
    unfold lookupRate; rw [hr]; decide +kernel

/-! ### The schedule condition -/

/-- The profile a cycle sees when `basalLookup` picks the entry `e`. -/
def entryProfile (env : Env) (e : BasalEntry) : Profile :=
  { env.profile with current_basal := some (lookupRate e) }

/-- The schedule is not empty, and for every entry `e` the profile with
    `current_basal := lookupRate e` passes `validProfileB`. -/
def scheduleOk (env : Env) : Bool :=
  !env.profile.basalprofile.isEmpty && env.profile.basalprofile.all (fun e => validProfileB (entryProfile env e))

/-- The schedule is not empty, and for every entry `e` the profile `entryProfile env e` passes
    `validProfileB` (`scheduleOk env = true`). The condition is decidable, so `decide` checks
    it on a concrete profile. -/
def ValidSchedule (env : Env) : Prop := scheduleOk env = true

instance (env : Env) : Decidable (ValidSchedule env) := inferInstanceAs (Decidable (_ = true))

theorem validSchedule_entry {env : Env} (h : ValidSchedule env) {e : BasalEntry}
    (he : e ∈ env.profile.basalprofile) : ValidProfile (entryProfile env e) := by
  unfold ValidSchedule scheduleOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact validProfileB_sound (h.2 e he)

/-- Under `ValidSchedule`, the schedule lookup at every time gives `lookupRate e` for an
    entry `e`. -/
theorem schedJs_entry {env : Env} (h : ValidSchedule env) (t : Int) :
    ∃ e ∈ env.profile.basalprofile, env.schedJs t = some (lookupRate e) := by
  unfold Env.schedJs
  cases hl : basalLookup env.profile.basalprofile (.fin t) env.tz with
  | some v =>
    obtain ⟨e, he, hv⟩ := basalLookup_some hl
    exact ⟨e, he, by rw [hv]⟩
  | none =>
    exfalso
    rcases basalLookup_none hl with h0 | ⟨e, he, hz⟩
    · unfold ValidSchedule scheduleOk at h
      rw [h0] at h; cases h
    · obtain ⟨cb, hcb, hpos⟩ := (validSchedule_entry h he).current_basal
      simp only [entryProfile, lookupRate_of_zero hz, Option.some.injEq, JsNum.fin.injEq] at hcb
      subst hcb
      exact absurd hpos (by decide)

theorem profileAt_entry {env : Env} (h : ValidSchedule env) (t : Int) :
    ∃ e ∈ env.profile.basalprofile, env.profileAt t = entryProfile env e := by
  obtain ⟨e, he, hs⟩ := schedJs_entry h t
  exact ⟨e, he, by unfold Env.profileAt entryProfile; rw [hs]⟩

/-- **`ValidEnv` from a checkable condition.** -/
theorem validEnv_of_schedule {env : Env} (h : ValidSchedule env) : ValidEnv env := by
  intro t
  obtain ⟨e, he, hp⟩ := profileAt_entry h t
  rw [hp]
  exact validSchedule_entry h he

/-! ### A rate bound computed from the entries -/

/-- The number `x`, or 0 for NaN. -/
def finOr0 : JsNum → Rat
  | .fin x => x
  | .nan => 0

/-- For the entry `e`, the larger of `round_basal(M)` and `s`, where `M` is `maxSafeBasal` of
    `entryProfile env e`, rounded with the pump model of `env.profile`, and `s = lookupRate e`.
    A NaN `M` or `s` counts as 0. -/
def entryCap (env : Env) (e : BasalEntry) : Rat :=
  let m := match getMaxSafeBasal (entryProfile env e) with
    | .fin M => rbR M env.profile.model
    | .nan => 0
  let s := finOr0 (lookupRate e)
  if m ≤ s then s else m

/-- The maximum of 0 and `entryCap env e` over the entries `e` of the schedule. -/
def scheduleCap (env : Env) : Rat :=
  env.profile.basalprofile.foldr (fun e b => if entryCap env e ≤ b then b else entryCap env e) 0

theorem entryCap_le_foldr (env : Env) {e : BasalEntry} :
    ∀ {l : List BasalEntry}, e ∈ l →
      entryCap env e ≤ l.foldr (fun e b => if entryCap env e ≤ b then b else entryCap env e) 0
  | [], h => by cases h
  | x :: l, h => by
    simp only [List.foldr]
    rcases List.mem_cons.mp h with rfl | h
    · split <;> grind
    · have := entryCap_le_foldr env h
      split <;> grind

theorem entryCap_le {env : Env} {e : BasalEntry} (he : e ∈ env.profile.basalprofile) :
    entryCap env e ≤ scheduleCap env := entryCap_le_foldr env he

/-- If `ValidSchedule env`, then `RateCap env (scheduleCap env)`: at every time `t`, every
    finite `maxSafeBasal` value `M` of `env.profileAt t` satisfies
    `round_basal(M) ≤ scheduleCap env`. -/
theorem rateCap_of_schedule {env : Env} (h : ValidSchedule env) : RateCap env (scheduleCap env) := by
  intro t M hM
  obtain ⟨e, he, hp⟩ := profileAt_entry h t
  rw [hp] at hM
  have h1 := entryCap_le he
  have h2 : rbR M env.profile.model ≤ entryCap env e := by
    unfold entryCap; simp only [hM]; split <;> grind
  exact Rat.le_trans h2 h1

/-- If `ValidSchedule env`, then `env.sched k ≤ scheduleCap env` at every time `k`. -/
theorem sched_le_of_schedule {env : Env} (h : ValidSchedule env) (k : Int) : env.sched k ≤ scheduleCap env := by
  obtain ⟨e, he, hs⟩ := schedJs_entry h k
  have h1 := entryCap_le he
  have h2 : env.sched k ≤ entryCap env e := by
    unfold Env.sched; rw [hs]
    unfold entryCap
    cases hl : lookupRate e with
    | fin x => simp only [finOr0]; split <;> grind
    | nan =>
      obtain ⟨cb, hcb, -⟩ := (validSchedule_entry h he).current_basal
      simp [entryProfile, hl] at hcb
  exact Rat.le_trans h2 h1

/-! ### A microbolus cap computed from the profile

`smbMaxBolus` (determine-basal.js lines 1078-1095) is, in every branch,
`round(current_basal · m / 60, 1)` in double arithmetic, with `m` one of `30`,
`maxSMBBasalMinutes` and `maxUAMSMBBasalMinutes` (the last only when it is truthy, so
finite). IOB and COB only choose the branch. Under `ValidSchedule`, `current_basal` is
`lookupRate e` for an entry `e`, and every rounding step is monotone, so the value is at most
the same expression with the largest schedule rate and the largest of the three minute
values. -/

/-- The value `maxSMBBasalMinutes` may take: absent, or a finite number. -/
def minutesOk : Option JsNum → Bool
  | none => true
  | some (.fin _) => true
  | some .nan => false

/-- `maxSMBBasalMinutes` of `env.profile` is absent or a finite number. A NaN value would make
    `smbMaxBolus` NaN. `maxUAMSMBBasalMinutes` needs no condition: `smbMaxBolus` reads it only
    when it is truthy, and then it is finite. -/
def SmbMinutesOk (env : Env) : Prop := minutesOk env.profile.maxSMBBasalMinutes = true

instance (env : Env) : Decidable (SmbMinutesOk env) := inferInstanceAs (Decidable (_ = true))

/-- The largest of `30`, `maxSMBBasalMinutes` and `maxUAMSMBBasalMinutes` of `p`, where a
    missing or NaN field counts as 0. -/
def minutesCap (p : Profile) : Rat :=
  let a := finOr0 p.maxSMBBasalMinutes.js
  let b := finOr0 p.maxUAMSMBBasalMinutes.js
  let ab := if a ≤ b then b else a
  if ab ≤ 30 then 30 else ab

theorem minutesCap_30 (p : Profile) : 30 ≤ minutesCap p := by
  unfold minutesCap; simp only; split <;> split <;> grind

theorem minutesCap_smb (p : Profile) : finOr0 p.maxSMBBasalMinutes.js ≤ minutesCap p := by
  unfold minutesCap; simp only; split <;> split <;> grind

theorem minutesCap_uam (p : Profile) : finOr0 p.maxUAMSMBBasalMinutes.js ≤ minutesCap p := by
  unfold minutesCap; simp only; split <;> split <;> grind

/-- The maximum of 0 and `lookupRate e` over the entries `e` of the schedule, a NaN rate
    counting as 0. -/
def maxRate (env : Env) : Rat :=
  env.profile.basalprofile.foldr (fun e b => if finOr0 (lookupRate e) ≤ b then b else finOr0 (lookupRate e)) 0

theorem rate_le_foldr {e : BasalEntry} :
    ∀ {l : List BasalEntry}, e ∈ l →
      finOr0 (lookupRate e) ≤
        l.foldr (fun e b => if finOr0 (lookupRate e) ≤ b then b else finOr0 (lookupRate e)) 0
  | [], h => by cases h
  | x :: l, h => by
    simp only [List.foldr]
    rcases List.mem_cons.mp h with rfl | h
    · split <;> grind
    · have := rate_le_foldr h
      split <;> grind

theorem rate_le_maxRate {env : Env} {e : BasalEntry} (he : e ∈ env.profile.basalprofile) :
    finOr0 (lookupRate e) ≤ maxRate env := rate_le_foldr he

/-- The microbolus cap: `round(rd(rd(R · m) / 60), 1)` as the model computes it, with `R`
    the largest schedule rate (`maxRate env`) and `m` the largest of `30`,
    `maxSMBBasalMinutes` and `maxUAMSMBBasalMinutes` (`minutesCap env.profile`). -/
def smbCapOf (env : Env) : Rat :=
  rts (Binary64.rd (Binary64.rd (maxRate env * minutesCap env.profile) / 60)) (pow10 1)

/-- Let `0 ≤ cb ≤ R`, `m ≤ M` and `0 ≤ M`. Then `round(cb · m / 60, 1)` in double arithmetic
    is a finite `v` with `v ≤ rts (rd (rd (R · M) / 60)) 10`. -/
theorem smbRound_le {cb m R M : Rat} (h0 : 0 ≤ cb) (hb : cb ≤ R) (hm : m ≤ M) (hM : 0 ≤ M) :
    ∃ v, rnd (JsNum.fin cb * JsNum.fin m / 60) 1 = .fin v ∧
      v ≤ rts (Binary64.rd (Binary64.rd (R * M) / 60)) (pow10 1) := by
  refine ⟨rts (Binary64.rd (Binary64.rd (cb * m) / 60)) (pow10 1), ?_, ?_⟩
  · show JsNum.round (JsNum.div (JsNum.mul (.fin cb) (.fin m)) (.fin 60)) 1 = _
    simp only [JsNum.mul, JsNum.div, show (60 : Rat) ≠ 0 by decide, ↓reduceIte]
    exact rnd_fin _ _
  · apply rts_mono (pow10_pos 1)
    apply Binary64.rd_mono
    apply div_le_div_of_le (by decide)
    apply Binary64.rd_mono
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hm h0) (Rat.mul_le_mul_of_nonneg_right hb hM)

/-- Let `c` be a context whose profile has `current_basal = some (.fin cb)` with
    `0 ≤ cb ≤ R`, and whose `maxSMBBasalMinutes` is absent or finite. Then
    `smbMaxBolus c` is a finite `v` with `v ≤ rts (rd (rd (R · minutesCap c.p) / 60)) 10`,
    whatever the IOB and COB of `c`. -/
theorem smbMaxBolus_le {c : Ctx} {cb R : Rat} (hcb : c.p.current_basal = some (.fin cb))
    (h0 : 0 ≤ cb) (hb : cb ≤ R) (hm : minutesOk c.p.maxSMBBasalMinutes = true) :
    ∃ v, smbMaxBolus c = .fin v ∧
      v ≤ rts (Binary64.rd (Binary64.rd (R * minutesCap c.p) / 60)) (pow10 1) := by
  have hM := minutesCap_30 c.p
  have hM0 : (0 : Rat) ≤ minutesCap c.p := Rat.le_trans (by decide) hM
  have h30 := smbRound_le h0 hb hM hM0
  have hmle := minutesCap_smb c.p
  have hule := minutesCap_uam c.p
  unfold smbMaxBolus
  dsimp only
  rw [hcb]
  cases hx : c.p.maxSMBBasalMinutes with
  | none => simp only [Option.isNone_none, ↓reduceIte]; exact h30
  | some x =>
    cases x with
    | nan => rw [hx] at hm; simp [minutesOk] at hm
    | fin m =>
      rw [hx] at hmle
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
      split
      · cases hu : c.p.maxUAMSMBBasalMinutes with
        | none => simp only [Option.truthyN, Bool.false_eq_true, ↓reduceIte]; exact h30
        | some y =>
          cases y with
          | nan => simp only [Option.truthyN, JsNum.truthy, Bool.false_eq_true, ↓reduceIte]; exact h30
          | fin u =>
            rw [hu] at hule
            split
            · exact smbRound_le h0 hb hule hM0
            · exact h30
      · exact smbRound_le h0 hb hmle hM0

/-- Let `ValidSchedule env` and `SmbMinutesOk env` hold, and let `c` be a context whose
    profile is `env.profileAt t` for some time `t`. Then `smbMaxBolus c` is a finite `v` with
    `v ≤ smbCapOf env`. -/
theorem smbMaxBolus_sched {env : Env} (h : ValidSchedule env) (hm : SmbMinutesOk env) {t : Int}
    {c : Ctx} (hp : c.p = env.profileAt t) : ∃ v, smbMaxBolus c = .fin v ∧ v ≤ smbCapOf env := by
  obtain ⟨e, he, hpe⟩ := profileAt_entry h t
  rw [hpe] at hp
  obtain ⟨cb, hcb, hpos⟩ := (validSchedule_entry h he).current_basal
  have hl : lookupRate e = .fin cb := by
    simp only [entryProfile, Option.some.injEq] at hcb; exact hcb
  have hcb' : c.p.current_basal = some (.fin cb) := by rw [hp, ← hl]; rfl
  have hb : cb ≤ maxRate env := by
    have := rate_le_maxRate he; rw [hl] at this; exact this
  have hm' : minutesOk c.p.maxSMBBasalMinutes = true := by rw [hp]; exact hm
  have hmc : minutesCap c.p = minutesCap env.profile := by rw [hp]; rfl
  obtain ⟨v, hv, hle⟩ := smbMaxBolus_le hcb' (Rat.le_of_lt hpos) hb hm'
  rw [hmc] at hle
  exact ⟨v, hv, hle⟩

/-! ### The autosens ratio bounded by `autosens_max` -/

/-- The autosens ratio of every cycle, when autosens data is given, is a positive number
    at most the profile's `autosens_max`, which is set to a number. oref0's `autosens.js`
    clamps the ratio to `autosens_max` (line 410) and then rounds it to two decimals
    (line 416). That code is not transcribed, so this stays a hypothesis on the run. -/
def AutosensClamped (env : Env) (r : Run Event) : Prop :=
  ∀ c ∈ cycles env r, ∀ a, c.inp.autosens_data = some a →
    ∃ q amax : Rat, a.ratio = some (.fin q) ∧ 0 < q ∧
      env.profile.autosens_max = some (.fin amax) ∧ q ≤ amax

/-- **`AutosensOk` from the clamp.** If `ValidEnv env` and `AutosensClamped env r`, then
    `AutosensOk env r`. The reason is V5 of `ValidProfile`:
    `current_basal · autosens_max ≤ maxSafeBasal`, and the ratio is at most `autosens_max`. -/
theorem autosensOk_of_clamped {env : Env} {r : Run Event} (he : ValidEnv env)
    (h : AutosensClamped env r) : AutosensOk env r := by
  intro c hc a ha
  obtain ⟨q, amax, hq, hq0, hamax, hle⟩ := h c hc a ha
  refine ⟨q, hq, hq0, ?_⟩
  intro cb M hcb hM
  have vp := he c.time
  have hamax' : (env.profileAt c.time).autosens_max = some (.fin amax) := hamax
  obtain ⟨-, -, hV5⟩ := vp.autosens_max amax hamax'
  obtain ⟨cb', hcb', hpos⟩ := vp.current_basal
  rw [hcb] at hcb'; cases hcb'
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt hpos)) (hV5 cb M hcb hM)

/-! ### A concrete profile

`envS` has the profile of `Examples.staleInput` without `current_basal`, with
`autosens_max = 1.2` and a schedule of 1 U/h from midnight and 0.85 U/h from 6:00.
The kernel checks `ValidSchedule envS` and computes `scheduleCap envS = 3`, which is
`max_basal`, and `smbCapOf envS = 0.5`. `envM`, with `maxSMBBasalMinutes = 90`, has
`smbCapOf envM = 1.5`. `envZ` has the same profile with last rate 0. It fails the check, and its
schedule lookup gives `none` at the three times checked. -/

/-- The environment whose profile has 1 U/h from 0:00 and 0.85 U/h from 6:00. -/
def envS : Env :=
  { profile := { max_basal := some 3, max_daily_basal := some 1, max_iob := some 1, sens := some 50,
                 carb_ratio := some 10, min_bg := some 100, max_bg := some 100, autosens_max := some 1.2,
                 basalprofile := [{ i := some 0, minutes := 0, rate := 1 },
                                  { i := some 1, minutes := 360, rate := 0.85 }] } }

example : ValidSchedule envS ∧ scheduleCap envS = 3 := by decide +kernel

/-- `envS` with rate 0 from 6:00. -/
def envZ : Env :=
  { profile := { envS.profile with basalprofile := [{ i := some 0, minutes := 0, rate := 1 },
                                                    { i := some 1, minutes := 360, rate := 0 }] } }

example : ¬ ValidSchedule envZ := by decide +kernel

/-- `envS` with `maxSMBBasalMinutes = 90`. -/
def envM : Env := { envS with profile := { envS.profile with maxSMBBasalMinutes := some 90 } }

/-- The microbolus cap of `envS` is `round(1 · 30 / 60, 1) = 0.5` U, and that of `envM` is
    `round(1 · 90 / 60, 1) = 1.5` U. -/
example : SmbMinutesOk envS ∧ smbCapOf envS = 1 / 2 ∧
    ValidSchedule envM ∧ SmbMinutesOk envM ∧ smbCapOf envM = 3 / 2 := by decide +kernel

/-- `basalLookup` gives no rate for `envZ` at 0:00, 12:00 and 19:00 UTC, as oref0 does
    (`scripts/probe-basal-zero.js`). -/
example : ∀ t ∈ [0, 1795003200000, 1795003200000 + 7 * 3600000], envZ.schedJs t = none := by
  decide +kernel

end LeanAID.Time
