import LeanAID.Time.Duration

/-!
# A dated, fresh glucose status behind every insulin increase

A single call to `determineBasal` treats a status without a date as never stale (F-11).
Freshness therefore needs a property of the run: a cycle sees the status
`Glucose.getLastGlucose (entries s)`, and `entries` takes each entry's date from
`Reading.recorded`.

**Hypotheses on the run `r`.**
- `DatedReadings r`: every reading has `recorded = some x` with `x` finite and `x > 0`.
- `DoubleDates r`: every recorded date is a positive double, `rd(x) = x`. It implies
  `DatedReadings r` (`DoubleDates.dated`).
- `RecordedNear δ r`: every recorded date is within `δ` ms of the reading's `trueTime`.
- `SpacedReadings g r`: along the run, each reading's recorded date is at least `g` ms
  after that of every earlier reading.
- `HeadSpaced l`, a condition on the readings `l` that one cycle sees, newest first: every
  reading after the newest one with a truthy value is recorded at least 2.5 min before it.

**Main results.** A cycle at time `t` increases insulin (`Increases`) when it issues a
microbolus or a rate above `profileCurrentBasal`.
- `getLastGlucose_dated`: if all entry dates are positive and finite, the status date is a
  finite `d ≥ 0`.
- `getLastGlucose_date_between`: if all entry dates are positive doubles, `d` lies between
  the dates of two entries. The theorem does not say that these two entries were averaged
  into `d`. The fold averages its running date with an entry whose rounded distance from it
  is in `(−2, 2.5)` min. The running date can drift, so a chain of averages can span more
  than 2.5 min.
- `p1_dated`: in a legal run with `ValidEnv` and `DatedReadings`, every cycle that increases
  insulin has a status with a finite date `d ≥ 0` and `−5.05 min ≤ t − ⌊d⌋ < 12.05 min`.
- `p1_true_age`: in a legal run with `ValidEnv`, `DoubleDates` and `RecordedNear δ`, every
  cycle that increases insulin sees a reading with true age below `12.05 min + δ` and a
  reading with true age above `−5.05 min − 1 ms − δ`. The two readings can differ.
- `getLastGlucose_date_first`: if all entry dates are finite and every entry after the first
  kept entry, the first with a truthy `glucose` or `sgv`, is at least 2.5 min older than it,
  the status date is the date of that entry.
- `SpacedReadings.headSpaced`: `SpacedReadings g r` with `g ≥ 2.5 min` gives `HeadSpaced`
  for the readings of every cycle of `r`.
- `p1_true_age_head`: in a legal run with `ValidEnv`, `DatedReadings` and `RecordedNear δ`,
  every cycle that increases insulin and whose readings are `HeadSpaced` sees a newest
  reading with a truthy value whose true age lies in `(−5.05 min − 1 ms − δ, 12.05 min + δ)`.

`p1_dated` does not need `AutosensOk`. Its stale check is `stale_of_clip`, the lemma behind
`cgm_unreliable_no_increase`, applied to `⌊d⌋` because oref0 floors the date.

**Limitations.** The run model's entries carry only a value and a recorded date: no `sgv`,
device, noise or type. The theorems therefore do not cover general Nightscout input. Dates
are rounded by `Binary64.rd`, which has no overflow, and the TimeClip limit of
8.64 · 10¹⁵ ms is not modelled.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time
open LeanAID LeanAID.Proofs JsNum

/-- If `P b` holds and `P b' → P (f b' a)` for every `b'` and every `a ∈ l`, then
    `P (l.foldl f b)`. -/
theorem foldl_inv {α β : Type} (f : β → α → β) (P : β → Prop) :
    ∀ (l : List α) (b : β), P b → (∀ b, ∀ a ∈ l, P b → P (f b a)) → P (l.foldl f b)
  | [], _, hb, _ => hb
  | a :: l, b, hb, h => foldl_inv f P l (f b a) (h b a (by simp) hb) (fun b' a' ha' => h b' a' (by simp [ha']))

/-- The state of the fold of `getLastGlucose`: glucose, date, the three delta arrays, the
    calibration index and the stop flag. -/
abbrev GlSt := JsNum × JsNum × Array JsNum × Array JsNum × Array JsNum × Nat × Bool

/-- The fold step of `getLastGlucose`, glucose-get-last.js lines 26-64, where `now` is the
    first entry with a truthy `glucose` or `sgv`. -/
def glStep (now : Glucose.Entry) : GlSt → Glucose.Entry × Nat → GlSt :=
  fun st (e, k) =>
      let (g, nd, ld, sd, lgd, lc, stop) := st
      if stop then st
      else if e.type_ == some "cal" then (g, nd, ld, sd, lgd, k + 1, true)
      else if e.glucose.js >ʲ 38 && e.device == now.device then
        let thenDate := Glucose.getDateFromEntry e
        let minutesago := mathRound ((nd - thenDate) / (1000 * 60))
        let change := g - e.glucose.js
        let avgdelta := change / minutesago * 5
        if (-2 : JsNum) <ʲ minutesago && minutesago <ʲ 2.5 then
          ((g + e.glucose.js) / 2, (nd + thenDate) / 2, ld, sd, lgd, lc, stop)
        else if (2.5 : JsNum) <ʲ minutesago && minutesago <ʲ 17.5 then
          let ld := if (2.5 : JsNum) <ʲ minutesago && minutesago <ʲ 7.5 then ld.push avgdelta else ld
          (g, nd, ld, sd.push avgdelta, lgd, lc, stop)
        else if (17.5 : JsNum) <ʲ minutesago && minutesago <ʲ 42.5 then
          (g, nd, ld, sd, lgd.push avgdelta, lc, stop)
        else st
      else st

/-- A step of the fold keeps the date, or averages it with the entry's date when the
    rounded distance between them is in `(−2, 2.5)` minutes. -/
theorem glStep_date (now : Glucose.Entry) (st : GlSt) (x : Glucose.Entry × Nat) :
    (glStep now st x).2.1 = st.2.1 ∨
    ((-2 : JsNum) <ʲ mathRound ((st.2.1 - Glucose.getDateFromEntry x.1) / (1000 * 60)) &&
      mathRound ((st.2.1 - Glucose.getDateFromEntry x.1) / (1000 * 60)) <ʲ 2.5) = true ∧
    (glStep now st x).2.1 = (st.2.1 + Glucose.getDateFromEntry x.1) / 2 := by
  obtain ⟨g, nd, ld, sd, lgd, lc, stop⟩ := st
  obtain ⟨e, k⟩ := x
  simp only [glStep]
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr ⟨‹_›, rfl⟩

/-- Let `getLastGlucose data0` return the status `gs`. If `P` holds for the date of every
    entry of `data0` and `P q` implies `P ((q + x) / 2)` for the date `x` of every entry of
    `data0`, then `gs.date = some d` with `P d`. -/
theorem getLastGlucose_date_inv (P : JsNum → Prop) {data0 : List Glucose.Entry} {gs : GlucoseStatus}
    (h : Glucose.getLastGlucose data0 = some gs)
    (h0 : ∀ e ∈ data0, P (Glucose.getDateFromEntry e))
    (hstep : ∀ q, P q → ∀ e ∈ data0, P ((q + Glucose.getDateFromEntry e) / 2)) :
    ∃ d, gs.date = some d ∧ P d := by
  unfold Glucose.getLastGlucose at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  · rename_i now hnow
    simp only [pure, Option.some.injEq] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    -- every entry of the mapped list has the date fields of an entry of `data0`
    have hmem : ∀ e ∈ (List.map (fun o : Glucose.Entry =>
          { glucose := if o.glucose.truthyN = true then o.glucose else o.sgv, sgv := o.sgv, noise := o.noise,
            type_ := o.type_, device := o.device, date := o.date, displayTimeMs := o.displayTimeMs,
            dateStringMs := o.dateStringMs : Glucose.Entry })
          (List.filter (fun o => o.glucose.truthyN || o.sgv.truthyN) data0)),
        ∃ o ∈ data0, Glucose.getDateFromEntry e = Glucose.getDateFromEntry o := by
      intro e he
      simp only [List.mem_map, List.mem_filter] at he
      obtain ⟨o, ⟨ho, -⟩, rfl⟩ := he
      exact ⟨o, ho, rfl⟩
    refine foldl_inv (glStep now) (fun st : GlSt => P st.2.1) _ _ ?_ ?_
    · obtain ⟨o, ho, he⟩ := hmem now (List.mem_of_mem_head? hnow)
      show P (Glucose.getDateFromEntry now)
      rw [he]; exact h0 o ho
    · intro st x hx hP
      have hxm : x.1 ∈ _ := List.mem_of_mem_tail (List.fst_mem_of_mem_zipIdx hx)
      obtain ⟨o, ho, he⟩ := hmem _ hxm
      rcases glStep_date now st x with h | ⟨-, h⟩
      · show P (glStep now st x).2.1; rw [h]; exact hP
      · show P (glStep now st x).2.1; rw [h, he]; exact hstep _ hP o ho

/-- **Dated status.** If every entry of `data0` has a positive finite `date` and
    `getLastGlucose data0` returns `gs`, then `gs.date` is a finite `d ≥ 0`. -/
theorem getLastGlucose_dated {data0 : List Glucose.Entry} {gs : GlucoseStatus}
    (h : Glucose.getLastGlucose data0 = some gs)
    (hd : ∀ e ∈ data0, ∃ x : Rat, e.date = some (.fin x) ∧ 0 < x) :
    ∃ d : Rat, gs.date = some (.fin d) ∧ 0 ≤ d := by
  have hdate : ∀ e ∈ data0, ∃ x : Rat, Glucose.getDateFromEntry e = .fin x ∧ 0 < x := by
    intro e he
    obtain ⟨x, hx, hx0⟩ := hd e he
    refine ⟨x, ?_, hx0⟩
    unfold Glucose.getDateFromEntry
    simp [hx, show x ≠ 0 by grind]
  obtain ⟨q, hq, hP⟩ := getLastGlucose_date_inv (fun q => ∃ d : Rat, q = .fin d ∧ 0 ≤ d) h
    (fun e he => by obtain ⟨x, hx, hx0⟩ := hdate e he; exact ⟨x, hx, Rat.le_of_lt hx0⟩)
    (fun q hq e he => by
      obtain ⟨d, rfl, hd0⟩ := hq
      obtain ⟨x, hx, hx0⟩ := hdate e he
      rw [hx, fin_add, show (2 : JsNum) = .fin 2 from rfl, fin_div (by decide)]
      exact ⟨_, rfl, Binary64.rd_nonneg (div_nonneg' (by decide) (Binary64.rd_nonneg (by grind)))⟩)
  obtain ⟨d, rfl, hd0⟩ := hP
  exact ⟨d, hq, hd0⟩

/-- **Status date between entry dates.** If every entry of `data0` has a `date` `x` that is a
    positive double, `x > 0` and `rd(x) = x`, and `getLastGlucose data0` returns `gs`, then
    `gs.date` is a finite `d` with `x₁ ≤ d ≤ x₂` for the dates `x₁`, `x₂` of two entries of
    `data0`. -/
theorem getLastGlucose_date_between {data0 : List Glucose.Entry} {gs : GlucoseStatus}
    (h : Glucose.getLastGlucose data0 = some gs)
    (hd : ∀ e ∈ data0, ∃ x : Rat, e.date = some (.fin x) ∧ 0 < x ∧ Binary64.rd x = x) :
    ∃ d : Rat, gs.date = some (.fin d) ∧
      (∃ e ∈ data0, ∃ x : Rat, e.date = some (.fin x) ∧ x ≤ d) ∧
      (∃ e ∈ data0, ∃ x : Rat, e.date = some (.fin x) ∧ d ≤ x) := by
  have hdate : ∀ e ∈ data0, ∃ x : Rat, Glucose.getDateFromEntry e = .fin x ∧ e.date = some (.fin x) ∧
      Binary64.rd x = x := by
    intro e he
    obtain ⟨x, hx, hx0, hxd⟩ := hd e he
    refine ⟨x, ?_, hx, hxd⟩
    unfold Glucose.getDateFromEntry
    simp [hx, show x ≠ 0 by grind]
  let P : JsNum → Prop := fun q => ∃ d : Rat, q = .fin d ∧
      (∃ e ∈ data0, ∃ x : Rat, e.date = some (.fin x) ∧ Binary64.rd x = x ∧ x ≤ d) ∧
      (∃ e ∈ data0, ∃ x : Rat, e.date = some (.fin x) ∧ Binary64.rd x = x ∧ d ≤ x)
  obtain ⟨q, hq, hP⟩ := getLastGlucose_date_inv P h
    (fun e he => by
      obtain ⟨x, hx, hxe, hxd⟩ := hdate e he
      exact ⟨x, hx, ⟨e, he, x, hxe, hxd, Rat.le_refl⟩, ⟨e, he, x, hxe, hxd, Rat.le_refl⟩⟩)
    (fun q hq e he => by
      obtain ⟨d, rfl, ⟨e1, he1, x1, hx1, d1, h1⟩, ⟨e2, he2, x2, hx2, d2, h2⟩⟩ := hq
      obtain ⟨x, hx, hxe, hxd⟩ := hdate e he
      rw [hx, fin_add, show (2 : JsNum) = .fin 2 from rfl, fin_div (by decide)]
      refine ⟨_, rfl, ?_, ?_⟩
      · -- lower bound: the smaller of `x1` and `x`
        by_cases hc : x1 ≤ x
        · exact ⟨e1, he1, x1, hx1, d1, Binary64.le_rd_half d1 (by grind)⟩
        · exact ⟨e, he, x, hxe, hxd, Binary64.le_rd_half hxd (by grind)⟩
      · -- upper bound: the larger of `x2` and `x`
        by_cases hc : x ≤ x2
        · exact ⟨e2, he2, x2, hx2, d2, Binary64.rd_half_le d2 (by grind)⟩
        · exact ⟨e, he, x, hxe, hxd, Binary64.rd_half_le hxd (by grind)⟩)
  obtain ⟨d, rfl, ⟨e1, he1, x1, hx1, -, h1⟩, ⟨e2, he2, x2, hx2, -, h2⟩⟩ := hP
  exact ⟨d, hq, ⟨e1, he1, x1, hx1, h1⟩, ⟨e2, he2, x2, hx2, h2⟩⟩

/-! ### How oref0 reads the status date, and a missing status -/

/-- For `d ≥ 0`, `DateFmt.timeClip d = ⌊d⌋`: `new Date(d)` truncates a nonnegative date to
    whole milliseconds. JavaScript also gives an invalid date above 8.64 · 10¹⁵ ms, which
    `DateFmt.timeClip` does not model. -/
theorem timeClip_nonneg {d : Rat} (h : 0 ≤ d) : DateFmt.timeClip (.fin d) = .fin (d.floor : Rat) := by
  simp [DateFmt.timeClip, show ¬ d < 0 by grind]

/-- If the profile `p` has a `current_basal` and there is no glucose status, `determineBasal`
    issues neither a rate nor a microbolus. oref0 stops with an error at the missing date. -/
theorem no_status_no_dose {inp : DBInputs} {p : Profile} (hp : inp.profile = some p)
    (hcb : p.current_basal.isSome) (hgs : inp.glucose_status = none) :
    (determineBasal inp).units = none ∧ (determineBasal inp).rate = none := by
  have hne : p.current_basal ≠ none := by intro h; simp [h] at hcb
  have h1 : stProfile inp = .ok p := by simp [stProfile, hp, hne]
  have h2 : stGlucose inp p = .error (typeError "date") := by simp [stGlucose, hgs]
  unfold determineBasal dbPrelude
  simp [h1, h2, bind, Except.bind, typeError, Result.err]

/-! ### Readings of a run -/

/-- Every reading of the run `r` has a positive finite recorded date. -/
def DatedReadings (r : Run Event) : Prop :=
  ∀ st ∈ r, ∀ rd : Reading, Event.reading rd ∈ st.events → ∃ x : Rat, rd.recorded = some (.fin x) ∧ 0 < x

theorem readings_applyEvent_eq (t : Int) (s : PState) (e : Event) :
    (applyEvent t s e).readings = (match e with | .reading x => x :: s.readings | _ => s.readings) := by
  cases e with
  | reading x => rfl
  | userBolus u => simp only [applyEvent]; split <;> rfl
  | cycle inp res out =>
    cases out with
    | lost => rfl
    | accepted =>
      simp only [applyEvent]
      split
      · rename_i c _
        unfold applyCmd
        cases c.temp <;> cases c.bolus <;> rfl
      · rfl

theorem readings_applyEvent {Q : Reading → Prop} {t : Int} {s : PState} {e : Event}
    (hs : ∀ rd ∈ s.readings, Q rd) (he : ∀ rd, e = .reading rd → Q rd) :
    ∀ rd ∈ (applyEvent t s e).readings, Q rd := by
  rw [readings_applyEvent_eq]
  cases e with
  | reading x =>
    intro rd hrd
    simp only [List.mem_cons] at hrd
    rcases hrd with rfl | hrd
    · exact he _ rfl
    · exact hs _ hrd
  | userBolus u => exact hs
  | cycle inp res out => exact hs

theorem readings_events {Q : Reading → Prop} {t : Int} :
    ∀ {s : PState} {es : List Event}, (∀ rd ∈ s.readings, Q rd) → (∀ rd, Event.reading rd ∈ es → Q rd) →
      (∀ rd ∈ (es.foldl (applyEvent t) s).readings, Q rd) ∧
      ∀ c ∈ cyclesEvents t s es, ∀ rd ∈ c.pre.readings, Q rd
  | _, [], hs, _ => ⟨hs, by simp [cyclesEvents]⟩
  | s, e :: es, hs, he => by
    have hs' := readings_applyEvent (t := t) (e := e) hs (fun rd h => he rd (by subst h; exact List.mem_cons_self))
    have ih := readings_events (t := t) (es := es) hs' (fun rd h => he rd (List.mem_cons_of_mem _ h))
    refine ⟨ih.1, ?_⟩
    intro c hc
    simp only [cyclesEvents, List.mem_append] at hc
    rcases hc with hc | hc
    · cases e with
      | cycle inp res out =>
        simp only [List.mem_singleton] at hc; subst hc; exact hs
      | _ => simp at hc
    · exact ih.2 c hc

theorem readings_cyclesFrom {Q : Reading → Prop} :
    ∀ {s : PState} {r : Run Event}, (∀ rd ∈ s.readings, Q rd) →
      (∀ st ∈ r, ∀ rd, Event.reading rd ∈ st.events → Q rd) →
      ∀ c ∈ cyclesFrom s r, ∀ rd ∈ c.pre.readings, Q rd
  | _, [], _, _, c, hc => by simp [cyclesFrom] at hc
  | s, st :: r, hs, hr, c, hc => by
    have h := readings_events (t := st.time) (es := st.events) hs (hr st (by simp))
    simp only [cyclesFrom, List.mem_append] at hc
    rcases hc with hc | hc
    · exact h.2 c hc
    · exact readings_cyclesFrom h.1 (fun st' h' => hr st' (by simp [h'])) c hc

/-- Every reading that a cycle of `r` sees satisfies `Q` if every reading event of `r` does. -/
theorem readings_cycles {Q : Reading → Prop} {env : Env} {r : Run Event}
    (hr : ∀ st ∈ r, ∀ rd, Event.reading rd ∈ st.events → Q rd) :
    ∀ c ∈ cycles env r, ∀ rd ∈ c.pre.readings, Q rd :=
  readings_cyclesFrom (by simp [Env.init]) hr

/-! ### A cycle that increases insulin sees a dated, fresh status -/

/-- The cycle `c` issues a microbolus or a rate above `profileCurrentBasal` of its profile. -/
def Increases (env : Env) (c : CycleAt) : Prop :=
  c.res.units.isSome ∨
    ∃ x, c.res.rate = some x ∧ (x >ʲ profileCurrentBasal (env.profileAt c.time)) = true

/-- **Fresh status before an increase.** Let `r` be a legal run of `env` with `ValidEnv env`
    and `DatedReadings r`. Then every cycle of `r` at time `t` that issues a microbolus or a
    rate above `profileCurrentBasal` has a glucose status whose date is a finite `d ≥ 0` with
    ```text
    −5.05 min ≤ t − ⌊d⌋ < 12.05 min.
    ```
    -/
theorem p1_dated {env : Env} {r : Run Event} (hl : Legal env r) (he : ValidEnv env)
    (hd : DatedReadings r) :
    ∀ c ∈ cycles env r, Increases env c →
      ∃ gs d, c.inp.glucose_status = some gs ∧ gs.date = some (.fin d) ∧ 0 ≤ d ∧
        (-5 - 1/20 : Rat) ≤ ((c.time - d.floor : Int) : Rat) / 60000 ∧
        ((c.time - d.floor : Int) : Rat) / 60000 < 12 + 1/20 := by
  intro c hc hinc
  have lc := hl.cycle c hc
  have vp := he c.time
  obtain ⟨cb, hcb, -⟩ := vp.current_basal
  have hcbs : (env.profileAt c.time).current_basal.isSome := by simp [hcb]
  obtain ⟨b, hb, hb0⟩ := profileCurrentBasal_nonneg vp
  have hres : c.res = determineBasal c.inp := lc.result
  -- no increase when the result keeps the rate at most the basal and issues no units
  have noinc : c.res.units = none →
      (c.res.rate = some (profileCurrentBasal (env.profileAt c.time)) ∨ c.res.rate = some 0 ∨
        c.res.rate = none) → False := by
    intro hu hr
    rcases hinc with hi | ⟨x, hx, hgt⟩
    · rw [hu] at hi; cases hi
    · rw [hb] at hgt
      rcases hr with hr | hr | hr <;> rw [hr] at hx <;> cases hx
      · rw [hb] at hgt; simp at hgt
      · simp at hgt; grind
  cases hgs : c.inp.glucose_status with
  | none =>
    exfalso
    have := no_status_no_dose lc.profile hcbs hgs
    rw [← hres] at this
    exact noinc this.1 (Or.inr (Or.inr this.2))
  | some gs =>
    have hdat : ∀ e ∈ entries c.pre, ∃ x : Rat, e.date = some (.fin x) ∧ 0 < x := by
      intro e he'
      simp only [entries, List.mem_map] at he'
      obtain ⟨rd, hrd, rfl⟩ := he'
      exact readings_cycles hd c hc rd hrd
    have hgl : Glucose.getLastGlucose (entries c.pre) = some gs := by rw [← lc.glucose, hgs]
    obtain ⟨d, hdd, hd0⟩ := getLastGlucose_dated hgl hdat
    refine ⟨gs, d, rfl, hdd, hd0, ?_⟩
    have hnow := lc.now
    apply Classical.byContradiction
    intro hbad
    have hst : cgmStale (gluVals (.fin c.inp.clock.now) gs) = true := by
      rw [hnow]
      apply stale_of_clip (n := d.floor) (by simp [hdd, Option.js_some, timeClip_nonneg hd0])
      by_cases h1 : ((c.time - d.floor : Int) : Rat) / 60000 < 12 + 1/20
      · right; grind
      · left; grind
    have herr : cgmError (gluVals (.fin c.inp.clock.now) gs) = true := by simp [cgmError, hst]
    obtain ⟨hu, hr⟩ := cgmError_no_increase lc.profile hcbs hgs herr
    rw [← hres] at hu hr
    apply noinc hu
    rcases hr with ⟨ct, -, -, hr⟩ | hr | ⟨hr, -⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hr)

/-! ### Freshness in true time -/

/-- Every reading of `r` has a recorded date that is a positive double. -/
def DoubleDates (r : Run Event) : Prop :=
  ∀ st ∈ r, ∀ rd : Reading, Event.reading rd ∈ st.events →
    ∃ x : Rat, rd.recorded = some (.fin x) ∧ 0 < x ∧ Binary64.rd x = x

/-- Every recorded date of `r` is within `δ` ms of the true time of its reading. -/
def RecordedNear (δ : Rat) (r : Run Event) : Prop :=
  ∀ st ∈ r, ∀ rd : Reading, Event.reading rd ∈ st.events →
    ∀ x : Rat, rd.recorded = some (.fin x) → x - δ ≤ rd.trueTime ∧ (rd.trueTime : Rat) ≤ x + δ

theorem DoubleDates.dated {r : Run Event} (h : DoubleDates r) : DatedReadings r := by
  intro st hst rd hrd
  obtain ⟨x, hx, hx0, -⟩ := h st hst rd hrd
  exact ⟨x, hx, hx0⟩

/-- **Freshness in true time.** Let `r` be a legal run of `env` with `ValidEnv env`,
    `DoubleDates r` and `RecordedNear δ r`. Then every cycle of `r` at time `t` that issues a
    microbolus or a rate above `profileCurrentBasal` sees readings `rd₁` and `rd₂`, possibly
    equal, with
    ```text
    t − rd₁.trueTime < 12.05 min + δ,     t − rd₂.trueTime > −5.05 min − 1 ms − δ.
    ```
    The theorem does not say that `rd₁` or `rd₂` enters the glucose status. The 0.05 min
    comes from rounding the age to 0.1 min, and the 1 ms from oref0 reading the status
    date `d` as `⌊d⌋`. -/
theorem p1_true_age {env : Env} {r : Run Event} {δ : Rat} (hl : Legal env r) (he : ValidEnv env)
    (hw : DoubleDates r) (hδ : RecordedNear δ r) :
    ∀ c ∈ cycles env r, Increases env c →
      (∃ rd ∈ c.pre.readings, (c.time : Rat) - rd.trueTime < 723000 + δ) ∧
      (∃ rd ∈ c.pre.readings, -303000 - 1 - δ < (c.time : Rat) - rd.trueTime) := by
  intro c hc hinc
  obtain ⟨gs, d, hgs, hdd, hd0, hlo, hhi⟩ := p1_dated hl he hw.dated c hc hinc
  have lc := hl.cycle c hc
  have hgl : Glucose.getLastGlucose (entries c.pre) = some gs := by rw [← lc.glucose, hgs]
  have hwc := readings_cycles (env := env) hw c hc
  have hδc := readings_cycles (env := env) hδ c hc
  have hdat : ∀ e ∈ entries c.pre, ∃ x : Rat, e.date = some (.fin x) ∧ 0 < x ∧ Binary64.rd x = x := by
    intro e he'
    simp only [entries, List.mem_map] at he'
    obtain ⟨rd, hrd, rfl⟩ := he'
    exact hwc rd hrd
  obtain ⟨d', hdd', ⟨e1, he1, n1, hn1, h1⟩, ⟨e2, he2, n2, hn2, h2⟩⟩ := getLastGlucose_date_between hgl hdat
  rw [hdd] at hdd'
  cases hdd'
  have hfl := Rat.floor_le d
  have hlt := Rat.lt_floor_add_one d
  have hlo' : (-303000 : Rat) ≤ ((c.time - d.floor : Int) : Rat) := by
    have := (le_div_iff_mul_le (by decide)).mp hlo; grind
  have hhi' : ((c.time - d.floor : Int) : Rat) < 723000 := by
    have := (Rat.div_lt_iff (by decide)).mp hhi; grind
  push_cast at hlo' hhi'
  constructor
  · simp only [entries, List.mem_map] at he2
    obtain ⟨rd, hrd, rfl⟩ := he2
    have := (hδc rd hrd n2 hn2).1
    exact ⟨rd, hrd, by grind⟩
  · simp only [entries, List.mem_map] at he1
    obtain ⟨rd, hrd, rfl⟩ := he1
    have := (hδc rd hrd n1 hn1).2
    exact ⟨rd, hrd, by grind⟩

/-! ### Freshness of the newest reading -/

/-- For dates `a`, `b` with `a ≥ b + 150000` ms, the `minutesago` that `getLastGlucose`
    computes in binary64, `round((a − b) / (1000 · 60))`, is not below 2.5, so the fold does
    not average `b` into `a`. -/
theorem minutesago_not_lt {a b : Rat} (h : b + 150000 ≤ a) :
    (mathRound ((JsNum.fin a - JsNum.fin b) / (1000 * 60)) <ʲ 2.5) = false := by
  have h60 : ((1000 : JsNum) * 60) = .fin 60000 := by
    show JsNum.fin (Binary64.rd (1000 * 60)) = _
    rw [show (1000 * 60 : Rat) = ((60000 : Int) : Rat) by decide +kernel, Binary64.rd_intCast (by decide)]; rfl
  have h25 : (2.5 : JsNum) = .fin (5/2) := by
    show JsNum.fin (Binary64.rd _) = _
    decide +kernel
  rw [h60, h25, fin_sub, fin_div (by decide)]
  have h1 : (150000 : Rat) ≤ Binary64.rd (a - b) := by
    have := Binary64.rd_mono (show ((150000 : Int) : Rat) ≤ a - b by push_cast; grind)
    rwa [Binary64.rd_intCast (by decide)] at this
  have h2 : (5/2 : Rat) ≤ Binary64.rd (Binary64.rd (a - b) / 60000) := by
    have := Binary64.rd_mono (show (5/2 : Rat) ≤ Binary64.rd (a - b) / 60000 by
      rw [le_div_iff_mul_le (by decide)]; grind)
    rwa [show Binary64.rd (5/2) = 5/2 by decide +kernel] at this
  simp only [mathRound, JsNum.lt, decide_eq_false_iff_not, JsNum.roundInt]
  intro hc
  have hlt := Rat.lt_floor_add_one (Binary64.rd (Binary64.rd (a - b) / 60000) + 1/2)
  generalize (Binary64.rd (Binary64.rd (a - b) / 60000) + 1/2).floor = z at hc hlt
  have : (2 : Rat) < (z : Rat) := by grind
  have : (2 : Int) < z := by exact_mod_cast this
  have : (3 : Rat) ≤ (z : Rat) := by exact_mod_cast (show (3 : Int) ≤ z by omega)
  grind

/-- Dropping the leading entries that fail `p` does not change the entries that pass. -/
theorem filter_dropWhile_not {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.dropWhile (fun x => !p x)).filter p = l.filter p
  | [] => rfl
  | a :: l => by
    cases hp : p a
    · simp [hp, filter_dropWhile_not p l]
    · simp [hp]

/-- The first entry left after dropping the entries that fail `p` passes `p`. -/
theorem dropWhile_not_head {α : Type} {p : α → Bool} :
    ∀ {l : List α} {a : α} {rest : List α}, l.dropWhile (fun x => !p x) = a :: rest → p a = true
  | [], _, _, h => by simp at h
  | b :: l, a, rest, h => by
    cases hp : p b
    · simp [hp] at h; exact dropWhile_not_head h
    · simp [hp] at h; obtain ⟨rfl, -⟩ := h; exact hp

/-- **Status date without averaging.** Let `getLastGlucose data0` return `gs`, let
    `getDateFromEntry e` be finite for every entry `e` of `data0`, and let `o` be the first
    entry with a truthy `glucose` or `sgv`. If every entry after `o` in `data0` is dated at
    least 2.5 min before `o`, then `gs.date` is the date of `o`. -/
theorem getLastGlucose_date_first {data0 : List Glucose.Entry} {gs : GlucoseStatus}
    (h : Glucose.getLastGlucose data0 = some gs)
    (hd : ∀ e ∈ data0, ∃ x : Rat, Glucose.getDateFromEntry e = .fin x)
    (hsp : ∀ o rest, data0.dropWhile (fun x => !(x.glucose.truthyN || x.sgv.truthyN)) = o :: rest →
      ∀ e ∈ rest, ∀ xa xb : Rat, Glucose.getDateFromEntry o = .fin xa →
        Glucose.getDateFromEntry e = .fin xb → xb + 150000 ≤ xa) :
    ∃ e, data0.find? (fun o => o.glucose.truthyN || o.sgv.truthyN) = some e ∧
      gs.date = some (Glucose.getDateFromEntry e) := by
  unfold Glucose.getLastGlucose at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  · rename_i now hnow
    simp only [pure, Option.some.injEq] at h
    subst h
    rw [List.head?_map, Option.map_eq_some_iff] at hnow
    obtain ⟨o, ho, rfl⟩ := hnow
    have hfind : data0.find? (fun o => o.glucose.truthyN || o.sgv.truthyN) = some o := by
      rw [← List.head?_filter]; exact ho
    refine ⟨o, hfind, ?_⟩
    obtain ⟨t', ht'⟩ : ∃ t', data0.filter (fun o => o.glucose.truthyN || o.sgv.truthyN) = o :: t' := by
      revert ho
      cases data0.filter (fun o => o.glucose.truthyN || o.sgv.truthyN) with
      | nil => simp
      | cons a t => intro ho; simp at ho; subst ho; exact ⟨t, rfl⟩
    -- the entries after `o` that the fold sees come after `o` in `data0`
    obtain ⟨rest, hdw, hrest⟩ : ∃ rest,
        data0.dropWhile (fun x => !(x.glucose.truthyN || x.sgv.truthyN)) = o :: rest ∧ ∀ o' ∈ t', o' ∈ rest := by
      have hf := filter_dropWhile_not (fun o : Glucose.Entry => o.glucose.truthyN || o.sgv.truthyN) data0
      rw [ht'] at hf
      revert hf
      cases hD : data0.dropWhile (fun x => !(x.glucose.truthyN || x.sgv.truthyN)) with
      | nil => simp
      | cons a rest =>
        have ha := dropWhile_not_head hD
        simp only [List.filter_cons, ha, ite_true, List.cons.injEq]
        rintro ⟨rfl, rfl⟩
        exact ⟨rest, by simp, fun o' h' => (List.mem_filter.mp h').1⟩
    have hsub : ∀ o' ∈ t', o' ∈ data0 := fun o' h' =>
      (List.dropWhile_suffix _).subset (by rw [hdw]; exact List.mem_cons_of_mem _ (hrest o' h'))
    have ho0 : o ∈ data0 := (List.mem_filter.mp (by rw [ht']; simp)).1
    obtain ⟨x0, hx0⟩ := hd o ho0
    simp only [ht', List.map_cons, List.tail_cons, Option.some.injEq]
    rw [hx0]
    refine foldl_inv (glStep _) (fun st : GlSt => st.2.1 = .fin x0) _ _ ?_ ?_
    · show Glucose.getDateFromEntry _ = _
      exact hx0
    · intro st x hx hP
      have hxm := List.fst_mem_of_mem_zipIdx hx
      simp only [List.mem_map] at hxm
      obtain ⟨o', ho', hxo⟩ := hxm
      obtain ⟨x1, hx1⟩ := hd o' (hsub o' ho')
      have hgap := hsp o rest hdw o' (hrest o' ho') x0 x1 hx0 hx1
      have hdx : Glucose.getDateFromEntry x.1 = .fin x1 := by rw [← hxo]; exact hx1
      have hno := minutesago_not_lt hgap
      rcases glStep_date _ st x with h | ⟨hc, -⟩
      · show (glStep _ st x).2.1 = _; rw [h]; exact hP
      · rw [hP, hdx, hno] at hc; simp at hc

/-- The reading of an event, if it is one. -/
def Event.reading? : Event → Option Reading
  | .reading x => some x
  | _ => none

/-- The readings of the run `r`, in the order of their events. -/
def readingsOf (r : Run Event) : List Reading :=
  r.flatMap fun st => st.events.filterMap Event.reading?

/-- The recorded dates of the readings of `r` increase by at least `g` ms from each
    reading to every later one. -/
def SpacedReadings (g : Rat) (r : Run Event) : Prop :=
  (readingsOf r).Pairwise fun a b =>
    ∀ xa xb : Rat, a.recorded = some (.fin xa) → b.recorded = some (.fin xb) → xa + g ≤ xb

/-- The readings after the events `es`: those of `es`, newest first, before those of `s`. -/
theorem readings_events_eq (t : Int) :
    ∀ (s : PState) (es : List Event),
      (es.foldl (applyEvent t) s).readings = (es.filterMap Event.reading?).reverse ++ s.readings
  | _, [] => rfl
  | s, e :: es => by
    rw [List.foldl_cons, readings_events_eq t _ es, readings_applyEvent_eq]
    cases e <;> simp [Event.reading?, List.filterMap_cons]

/-- The readings a cycle sees are a suffix of the readings after the events. -/
theorem readings_cyclesEvents_suffix {t : Int} :
    ∀ {s : PState} {es : List Event}, ∀ c ∈ cyclesEvents t s es,
      c.pre.readings <:+ (es.filterMap Event.reading?).reverse ++ s.readings
  | _, [], c, hc => by simp [cyclesEvents] at hc
  | s, e :: es, c, hc => by
    simp only [cyclesEvents, List.mem_append] at hc
    rcases hc with hc | hc
    · cases e with
      | cycle inp res out =>
        simp only [List.mem_singleton] at hc; subst hc
        exact List.suffix_append _ _
      | _ => simp at hc
    · have := readings_cyclesEvents_suffix c hc
      rw [readings_applyEvent_eq] at this
      cases e <;> simpa [Event.reading?, List.filterMap_cons] using this

/-- The readings a cycle sees are a suffix of the readings after the run. -/
theorem readings_cyclesFrom_suffix :
    ∀ {s : PState} {r : Run Event}, ∀ c ∈ cyclesFrom s r,
      c.pre.readings <:+ (readingsOf r).reverse ++ s.readings
  | _, [], c, hc => by simp [cyclesFrom] at hc
  | s, st :: r, c, hc => by
    simp only [cyclesFrom, List.mem_append] at hc
    have hst : (readingsOf (st :: r)).reverse ++ s.readings =
        (readingsOf r).reverse ++ (applyStep s st).readings := by
      simp [readingsOf, applyStep, readings_events_eq]
    rw [hst]
    rcases hc with hc | hc
    · have := readings_cyclesEvents_suffix c hc
      rw [← readings_events_eq] at this
      exact this.trans (List.suffix_append _ _)
    · exact readings_cyclesFrom_suffix c hc

/-- The readings that a cycle of `r` sees, newest first, form a sublist of the readings of `r`
    in reverse order. -/
theorem readings_cycles_sublist {env : Env} {r : Run Event} :
    ∀ c ∈ cycles env r, List.Sublist c.pre.readings (readingsOf r).reverse := by
  intro c hc
  have := (readings_cyclesFrom_suffix c hc).sublist
  simpa [Env.init] using this

/-- For readings `l`, newest first, let `rd` be the first reading whose value is truthy, that
    is, neither `0` nor `NaN`. Then every reading after `rd` in `l` has a recorded date at
    least 2.5 min before that of `rd`. Only readings after `rd` can be averaged into the date
    of `getLastGlucose (entries s)`. -/
def HeadSpaced (l : List Reading) : Prop :=
  ∀ rd rest, l.dropWhile (fun x => !x.value.truthy) = rd :: rest →
    ∀ b ∈ rest, ∀ xa xb : Rat, rd.recorded = some (.fin xa) → b.recorded = some (.fin xb) → xb + 150000 ≤ xa

/-- `SpacedReadings g` with `g ≥ 2.5 min` gives `HeadSpaced` for the readings of every cycle. -/
theorem SpacedReadings.headSpaced {env : Env} {r : Run Event} {g : Rat} (hg : 150000 ≤ g)
    (hs : SpacedReadings g r) : ∀ c ∈ cycles env r, HeadSpaced c.pre.readings := by
  intro c hc rd rest hdw b hb xa xb hxa hxb
  -- the spacing, newest first
  have hsp : c.pre.readings.Pairwise fun a b =>
      ∀ xa xb : Rat, a.recorded = some (.fin xa) → b.recorded = some (.fin xb) → xb + g ≤ xa := by
    have := hs.sublist (List.reverse_sublist.mpr (readings_cycles_sublist c hc) |>.trans
      (by simp))
    rw [List.pairwise_reverse] at this
    exact this.imp fun h xa xb ha hb => h xb xa hb ha
  have hsd := hsp.sublist (List.dropWhile_sublist (fun x => !x.value.truthy))
  rw [hdw, List.pairwise_cons] at hsd
  have := hsd.1 b hb xa xb hxa hxb
  grind

/-- **Freshness of the newest reading.** Let `r` be a legal run of `env` with `ValidEnv env`,
    `DatedReadings r` and `RecordedNear δ r`. Let `c` be a cycle of `r` at time `t` that
    issues a microbolus or a rate above `profileCurrentBasal` and whose readings satisfy
    `HeadSpaced`. Then `c` sees a newest reading `rd` with a truthy value, and
    ```text
    −5.05 min − 1 ms − δ < t − rd.trueTime < 12.05 min + δ.
    ```
    Under `HeadSpaced` the status date is the recorded date of `rd`. The slack is 0.05 min
    from rounding the age to 0.1 min, 1 ms from oref0 reading the date `d` as `⌊d⌋`, and `δ`
    from `RecordedNear`. In the run model a reading's value is its only glucose field, so
    `getLastGlucose` drops exactly the readings with value `0` or `NaN`. -/
theorem p1_true_age_head {env : Env} {r : Run Event} {δ : Rat} (hl : Legal env r) (he : ValidEnv env)
    (hd : DatedReadings r) (hδ : RecordedNear δ r) :
    ∀ c ∈ cycles env r, Increases env c → HeadSpaced c.pre.readings →
      ∃ rd, c.pre.readings.find? (fun rd => rd.value.truthy) = some rd ∧
        -303000 - 1 - δ < (c.time : Rat) - rd.trueTime ∧ (c.time : Rat) - rd.trueTime < 723000 + δ := by
  intro c hc hinc hhs
  obtain ⟨gs, d, hgs, hdd, hd0, hlo, hhi⟩ := p1_dated hl he hd c hc hinc
  have lc := hl.cycle c hc
  have hgl : Glucose.getLastGlucose (entries c.pre) = some gs := by rw [← lc.glucose, hgs]
  have hdc := readings_cycles (env := env) hd c hc
  have hδc := readings_cycles (env := env) hδ c hc
  -- the date oref0 reads from the entry of a reading
  have hdate : ∀ rd ∈ c.pre.readings, ∃ x : Rat, rd.recorded = some (.fin x) ∧
      Glucose.getDateFromEntry { glucose := some rd.value, date := rd.recorded } = .fin x := by
    intro rd hrd
    obtain ⟨x, hx, hx0⟩ := hdc rd hrd
    refine ⟨x, hx, ?_⟩
    unfold Glucose.getDateFromEntry
    simp [hx, show x ≠ 0 by grind]
  have hspe : ∀ o rest, (entries c.pre).dropWhile (fun x => !(x.glucose.truthyN || x.sgv.truthyN)) = o :: rest →
      ∀ e ∈ rest, ∀ xa xb : Rat, Glucose.getDateFromEntry o = .fin xa →
        Glucose.getDateFromEntry e = .fin xb → xb + 150000 ≤ xa := by
    intro o rest hdw e he' xa xb hxa hxb
    unfold entries at hdw
    rw [List.dropWhile_map] at hdw
    have hfun : ((fun x : Glucose.Entry => !(x.glucose.truthyN || x.sgv.truthyN)) ∘
        fun r : Reading => ({ glucose := some r.value, date := r.recorded } : Glucose.Entry)) =
        fun x => !x.value.truthy := by
      funext x; simp [Option.truthyN]
    rw [hfun, List.map_eq_cons_iff] at hdw
    obtain ⟨rd, rs, hD, rfl, rfl⟩ := hdw
    simp only [List.mem_map] at he'
    obtain ⟨b, hb, rfl⟩ := he'
    have hrdm : rd ∈ c.pre.readings :=
      (List.dropWhile_suffix _).subset (by rw [hD]; exact List.mem_cons_self)
    have hbm : b ∈ c.pre.readings :=
      (List.dropWhile_suffix _).subset (by rw [hD]; exact List.mem_cons_of_mem _ hb)
    obtain ⟨ya, hya, hya'⟩ := hdate rd hrdm
    obtain ⟨yb, hyb, hyb'⟩ := hdate b hbm
    rw [hya'] at hxa; rw [hyb'] at hxb
    cases hxa; cases hxb
    exact hhs rd rs hD b hb _ _ hya hyb
  have hde : ∀ e ∈ entries c.pre, ∃ x : Rat, Glucose.getDateFromEntry e = .fin x := by
    intro e he'
    simp only [entries, List.mem_map] at he'
    obtain ⟨rd, hrd, rfl⟩ := he'
    obtain ⟨x, -, hx⟩ := hdate rd hrd
    exact ⟨x, hx⟩
  obtain ⟨e, hfind, hgd⟩ := getLastGlucose_date_first hgl hde hspe
  simp only [entries, List.find?_map, Option.map_eq_some_iff] at hfind
  obtain ⟨rd, hrd, rfl⟩ := hfind
  have hrdm : rd ∈ c.pre.readings := List.mem_of_find?_eq_some hrd
  refine ⟨rd, ?_, ?_⟩
  · simpa [Function.comp_def, Option.truthyN] using hrd
  · obtain ⟨x, hx, hxd⟩ := hdate rd hrdm
    rw [hdd, hxd] at hgd
    cases hgd
    have hfl := Rat.floor_le d
    have hlt := Rat.lt_floor_add_one d
    have hlo' : (-303000 : Rat) ≤ ((c.time - d.floor : Int) : Rat) := by
      have := (le_div_iff_mul_le (by decide)).mp hlo; grind
    have hhi' : ((c.time - d.floor : Int) : Rat) < 723000 := by
      have := (Rat.div_lt_iff (by decide)).mp hhi; grind
    push_cast at hlo' hhi'
    have := hδc rd hrdm d hx
    constructor <;> grind

end LeanAID.Time
