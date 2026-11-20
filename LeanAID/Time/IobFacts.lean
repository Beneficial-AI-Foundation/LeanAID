import LeanAID.Time.System
import LeanAID.Proofs.Lifted
import LeanAID.Proofs.ReviewFindings

/-!
# Facts about the IOB input of a cycle

**Setting.** `Iob.generate` on the pump history of a run state, `history env s`: the encoded
accepted actions, newest first, then `env.initHistory`. `calcTempTreatments` is split into
stages, so the kernel can unfold `generate` and facts about its output can be proved.

**Objects.**
- `PlainRec r x`: `r` is a record as `encodeAction` writes it: no nested `bolus`, no
  `created_at`, a timestamp string and the time value `x`.
- `LogOk s t`: the log of `s` is newest first and holds no action after time `t`.

**Theorems.**
- `scanRecords_bolus`, `calcTempTreatments_bolus`: if the history is `pre ++ r :: post`,
  with `r` a plain `Bolus` record at time `tb ≤ now` and every record of `pre` plain with a
  time `≥ tb`, the record scan (history.js lines 257-385) keeps `r`'s bolus, and it is a
  treatment of `calcTempTreatments` with `startedAt = some tb`.
- (a) `bolus_mem_treatments`: under `LogOk s t`, every accepted bolus in the log of `s` is a
  treatment of `calcTempTreatments` on the history of `s` at time `t`, for every zero-temp
  duration `z`. `Legal.logOk`: every cycle of a legal run satisfies `LogOk`.
- (b) `lastBolusTime_ge`, `Legal.bolusSeen`: at every cycle of a legal run, an earlier
  accepted bolus of nonzero units at time `tb` makes the `lastBolusTime` of the cycle's
  `iobOut` finite and at least `tb`.
- (c) `iobRaw_append`: let `p` have the bilinear curve and finite DIA, and let a bolus of `u`
  units be dated at the evaluation time `t`, with `rd u ≠ 0` and `|t − 1| ≤ 2⁵³`. Then
  appending it changes the raw IOB sum at `t` from `x` to the double sum `x + rd(u)`.
  `iobTotal_iob`: the reported IOB is total.js's 3-decimal rounding of the raw sum.
  `Time/IobAccounting.lean` turns this into a numeric bound, with the bolus at its sorted
  position.

`env.initHistory` follows the encoded actions, so it plays no role in these facts.

**Not proved.** (c) for the exponential curves. The treatments of the second call of
`generate`, which runs on the history the first call returns.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

open LeanAID LeanAID.Iob

/-- A record as `encodeAction` writes it: no nested `bolus`, no `created_at`, a timestamp
    string and the time value `x`. -/
structure PlainRec (r : PumpRecord) (x : Int) : Prop where
  bolus : r.bolus = none
  created : r.created_at = none
  ts : r.timestamp.isSome = true
  ms : r.timestampMs = some x

/-- The treatment that history.js makes from a `Bolus` record at time `tb` (line 309). -/
def bolusTreatment (r : PumpRecord) (tb : Int) : Treatment :=
  { insulin := r.amount, date := .fin tb, startedAt := some tb, timestamp := r.timestamp }

theorem scanRecord_mono (nowMs : Int) (z : Option JsNum) (st : ScanState) (i : Nat) :
    ∀ b ∈ st.boluses, b ∈ (scanRecord nowMs z st i).boluses := by
  intro b hb
  unfold scanRecord
  dsimp only
  repeat' split
  all_goals simp [Array.mem_push, hb]

theorem scanRecord_plain {nowMs : Int} {z : Option JsNum} {st : ScanState} {i : Nat} {r : PumpRecord} {x : Int}
    (hr : st.history[i]! = r) (hp : PlainRec r x) :
    (scanRecord nowMs z st i).history = st.history ∧
    ((scanRecord nowMs z st i).lastRecordTime = st.lastRecordTime ∨
      (scanRecord nowMs z st i).lastRecordTime = .fin x) := by
  have hf : recordFields r = r.toPumpFields := by simp [recordFields, hp.bolus]
  have ht : recTime r.toPumpFields nowMs = some x := by
    have := hp.ts
    unfold recTime
    cases h : r.timestamp with
    | none => simp_all
    | some _ => exact hp.ms
  unfold scanRecord
  simp only [hr, hf, hp.created, Option.isSome_none, Bool.false_eq_true, ite_false, ht]
  split
  · exact ⟨rfl, Or.inl rfl⟩
  · split <;> exact ⟨rfl, Or.inr rfl⟩

theorem scanRecord_bolus {nowMs : Int} {z : Option JsNum} {st : ScanState} {i : Nat} {r : PumpRecord}
    {tb L : Int} (hr : st.history[i]! = r) (hp : PlainRec r tb) (hty : r.type_ = some "Bolus")
    (hL : st.lastRecordTime = .fin L) (h1 : tb ≤ L) (h2 : tb ≤ nowMs) :
    bolusTreatment r tb ∈ (scanRecord nowMs z st i).boluses := by
  have hf : recordFields r = r.toPumpFields := by simp [recordFields, hp.bolus]
  have ht : recTime r.toPumpFields nowMs = some tb := by
    have := hp.ts
    unfold recTime
    cases h : r.timestamp with
    | none => simp_all
    | some _ => exact hp.ms
  have hc : classifyRecord st.history i r.toPumpFields nowMs = .bolus (bolusTreatment r tb) := by
    simp [classifyRecord, ht, hty, bolusTreatment, Rat.intCast_lt_intCast, Int.not_lt.mpr h2]
  unfold scanRecord
  simp only [hr, hf, hp.created, Option.isSome_none, Bool.false_eq_true, ite_false, ht, hL, hc]
  simp [Rat.intCast_lt_intCast, Int.not_lt.mpr h1, Array.mem_push]

theorem foldl_scan_mono (nowMs : Int) (z : Option JsNum) :
    ∀ (l : List Nat) (st : ScanState), ∀ b ∈ st.boluses, b ∈ (l.foldl (scanRecord nowMs z) st).boluses
  | [], _, _, hb => hb
  | i :: l, st, b, hb => foldl_scan_mono nowMs z l _ b (scanRecord_mono nowMs z st i b hb)

/-- Over indices of plain records at times `≥ tb`, the scan keeps the history and a
    finite last record time `≥ tb`. -/
theorem foldl_scan_inv (nowMs : Int) (z : Option JsNum) (tb : Int) (H : Array PumpRecord) :
    ∀ (l : List Nat) (st : ScanState), st.history = H →
      (∀ i ∈ l, ∃ x, PlainRec H[i]! x ∧ tb ≤ x) →
      (∃ L : Int, st.lastRecordTime = .fin L ∧ tb ≤ L) →
      (l.foldl (scanRecord nowMs z) st).history = H ∧
        ∃ L : Int, (l.foldl (scanRecord nowMs z) st).lastRecordTime = .fin L ∧ tb ≤ L
  | [], _, hH, _, hL => ⟨hH, hL⟩
  | i :: l, st, hH, hl, ⟨L, hL, htL⟩ => by
    obtain ⟨x, hx, htx⟩ := hl i (by simp)
    obtain ⟨h1, h2⟩ := scanRecord_plain (nowMs := nowMs) (z := z) (st := st) (i := i) (by rw [hH]) hx
    apply foldl_scan_inv nowMs z tb H l _ (h1.trans hH) (fun j hj => hl j (by simp [hj]))
    rcases h2 with h2 | h2
    · exact ⟨L, h2.trans hL, htL⟩
    · exact ⟨x, h2, htx⟩

theorem getElem!_append_left {pre post : List PumpRecord} {i : Nat} (h : i < pre.length) :
    (pre ++ post).toArray[i]! = pre[i] := by
  rw [getElem!_pos (pre ++ post).toArray i (by simp; omega)]
  simp [List.getElem_append_left h]

theorem getElem!_append_mid {pre post : List PumpRecord} {r : PumpRecord} :
    (pre ++ r :: post).toArray[pre.length]! = r := by
  rw [getElem!_pos (pre ++ r :: post).toArray pre.length (by simp)]
  simp

/-- **The record scan keeps a bolus.** Let the history be `pre ++ r :: post`, where `r` is a
    plain `Bolus` record at time `tb ≤ nowMs` and every record of `pre` is plain with a time
    `≥ tb`. Then the record scan of history.js lines 257-385 adds `bolusTreatment r tb` to
    its boluses. -/
theorem scanRecords_bolus (nowMs : Int) (z : Option JsNum) (pre post : List PumpRecord)
    (r : PumpRecord) (tb : Int) (hpre : ∀ q ∈ pre, ∃ x, PlainRec q x ∧ tb ≤ x)
    (hp : PlainRec r tb) (hty : r.type_ = some "Bolus") (hnow : tb ≤ nowMs) :
    bolusTreatment r tb ∈ (scanRecords nowMs z (pre ++ r :: post).toArray).boluses := by
  unfold scanRecords
  have hr : List.range (pre ++ r :: post).toArray.size =
      List.range pre.length ++ pre.length :: List.range' (pre.length + 1) post.length := by
    simp only [List.size_toArray, List.length_append, List.length_cons]
    rw [List.range_eq_range', List.range_eq_range', show pre.length + (post.length + 1) =
      pre.length + (1 + post.length) by omega, ← List.range'_append_1]
    simp [List.range'_succ, Nat.add_comm]
  rw [hr, List.foldl_append, List.foldl_cons]
  obtain ⟨hH, L, hL, htL⟩ := foldl_scan_inv nowMs z tb (pre ++ r :: post).toArray (List.range pre.length)
    { history := (pre ++ r :: post).toArray, lastRecordTime := .fin nowMs } rfl
    (fun i hi => by
      have hi' : i < pre.length := List.mem_range.mp hi
      rw [getElem!_append_left hi']
      exact hpre _ (List.getElem_mem hi'))
    ⟨nowMs, rfl, hnow⟩
  apply foldl_scan_mono
  exact scanRecord_bolus (by rw [hH]; exact getElem!_append_mid) hp hty hL htL hnow

theorem foldl_push_mono {β : Type} (f : β → Treatment) :
    ∀ (l : List β) (acc : Array Treatment), ∀ b ∈ acc, b ∈ l.foldl (fun acc k => acc.push (f k)) acc
  | [], _, _, hb => hb
  | k :: l, acc, b, hb => foldl_push_mono f l _ b (by simp [Array.mem_push, hb])

/-- The micro-bolus stage (lines 486-564) only appends. -/
theorem tempBolusesOf_mono (inp : HistoryInputs) (sh : List TempEvent) (acc : Array Treatment) :
    ∀ b ∈ acc, b ∈ tempBolusesOf inp sh acc := by
  unfold tempBolusesOf
  induction sh generalizing acc with
  | nil => intro b hb; exact hb
  | cons item sh ih =>
    intro b hb
    simp only [List.foldl_cons]
    apply ih
    split
    · split
      · exact foldl_push_mono _ _ _ b hb
      · exact hb
    · exact hb

/-- The treatments of `calcTempTreatments` are the sorted scan boluses and micro-boluses
    and the temps. -/
theorem calcTempTreatments_treatments (inp : HistoryInputs) (z : Option JsNum) :
    ∃ sh ts, (calcTempTreatments inp z).treatments = sortByKey (·.date)
      ((tempBolusesOf inp sh (scanRecords inp.clockMs z (inp.history ++ inp.history24.getD []).toArray).boluses).toList ++ ts) :=
  ⟨_, _, rfl⟩

/-- **A bolus record reaches the treatments.** Let `inp.history`, followed by
    `inp.history24` if present, be `pre ++ r :: post`, where `r` is a plain `Bolus` record at
    time `tb ≤ inp.clockMs` and every record of `pre` is plain with a time `≥ tb`. Then for
    every `z`, the treatments of `calcTempTreatments inp z` contain `bolusTreatment r tb`,
    which has `startedAt = some tb`. -/
theorem calcTempTreatments_bolus (inp : HistoryInputs) (z : Option JsNum) (pre post : List PumpRecord)
    (r : PumpRecord) (tb : Int) (hh : inp.history ++ inp.history24.getD [] = pre ++ r :: post)
    (hpre : ∀ q ∈ pre, ∃ x, PlainRec q x ∧ tb ≤ x)
    (hp : PlainRec r tb) (hty : r.type_ = some "Bolus") (hnow : tb ≤ inp.clockMs) :
    bolusTreatment r tb ∈ (calcTempTreatments inp z).treatments := by
  obtain ⟨sh, ts, h⟩ := calcTempTreatments_treatments inp z
  rw [h, mem_sortByKey, List.mem_append]
  left
  rw [Array.mem_toList_iff]
  apply tempBolusesOf_mono
  rw [hh]
  exact scanRecords_bolus inp.clockMs z pre post r tb hpre hp hty hnow

/-! ### `lastBolusTime` -/

theorem lastStep_fst (acc : JsNum × LastTempOut) (t : Treatment) :
    (lastStep acc t).1 = if t.insulin.truthyN && t.startedAt.isSome then
      JsNum.max acc.1 (.fin t.startedAt.get!) else acc.1 := by
  unfold lastStep
  dsimp only
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- The scan for `lastBolusTime` keeps a finite value and never lowers it. -/
theorem foldl_lastStep_ge (c : Rat) :
    ∀ (ts : List Treatment) (acc : JsNum × LastTempOut), (∃ y, acc.1 = .fin y ∧ c ≤ y) →
      ∃ y, (ts.foldl lastStep acc).1 = .fin y ∧ c ≤ y
  | [], _, h => h
  | t :: ts, acc, ⟨y, hy, hcy⟩ => by
    rw [List.foldl_cons]
    apply foldl_lastStep_ge c ts
    rw [lastStep_fst, hy]
    split
    · refine ⟨_, rfl, ?_⟩
      split
      · exact Rat.le_trans hcy ‹_›
      · exact hcy
    · exact ⟨y, rfl, hcy⟩

/-- If `ts` contains a treatment with truthy insulin and `startedAt = some tb`, the
    `lastBolusTime` scan over `ts` from a finite value ends at a finite value `≥ tb`. -/
theorem foldl_lastStep_bolus (tb : Int) :
    ∀ (ts : List Treatment) (acc : JsNum × LastTempOut) (t : Treatment), t ∈ ts →
      t.insulin.truthyN = true → t.startedAt = some tb → (∃ y : Rat, acc.1 = .fin y) →
      ∃ y, (ts.foldl lastStep acc).1 = .fin y ∧ (tb : Rat) ≤ y
  | [], _, _, h, _, _, _ => by simp at h
  | t' :: ts, acc, t, hmem, hins, hst, ⟨y, hy⟩ => by
    rcases List.mem_cons.mp hmem with h | h
    · subst h
      rw [List.foldl_cons]
      apply foldl_lastStep_ge _ ts
      rw [lastStep_fst, hy, hins, hst]
      refine ⟨if y ≤ (tb : Rat) then (tb : Rat) else y, by simp [JsNum.max]; rfl, ?_⟩
      by_cases hyt : y ≤ (tb : Rat)
      · simp only [hyt, ite_true]; exact Rat.le_refl
      · simp only [hyt, ite_false]; exact Rat.le_of_lt (Rat.not_le.mp hyt)
    · rw [List.foldl_cons]
      apply foldl_lastStep_bolus tb ts _ t h hins hst
      rw [lastStep_fst, hy]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨y, rfl⟩

theorem generate_lastBolusTime (inp : HistoryInputs) (b : Bool) :
    (generate inp b).lastBolusTime =
      ((calcTempTreatments inp none).treatments.foldl lastStep ((0 : JsNum), ({ date := 0 } : LastTempOut))).1 :=
  rfl

/-! ### The history of a run -/

/-- The time of an accepted action. -/
def Action.time : Action → Int
  | .temp t _ _ => t
  | .bolus t _ _ => t

/-- The log of state `s` is newest first and holds no action after time `t`. -/
def LogOk (s : PState) (t : Int) : Prop :=
  s.log.Pairwise (fun a b => b.time ≤ a.time) ∧ ∀ a ∈ s.log, a.time ≤ t

theorem encodeAction_plain (a : Action) : ∀ q ∈ encodeAction a, PlainRec q a.time := by
  intro q hq
  cases a <;> simp only [encodeAction, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    (try rcases hq with rfl | rfl) <;> (try subst hq) <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The treatment of an accepted bolus of `u` units at time `tb`. -/
def bolusOf (tb : Int) (u : Rat) : Treatment :=
  { insulin := some (.fin u), date := .fin tb, startedAt := some tb, timestamp := some (toString tb) }

/-- The history inputs of `iobOut env s t auto`. -/
def iobInputs (env : Env) (s : PState) (t : Int) (auto : Option Autosens) : HistoryInputs :=
  { history := history env s, profile := env.profileAt t, autosens := auto, clockMs := t, tzOffsetMin := env.tz }

theorem iobOut_eq (env : Env) (s : PState) (t : Int) (auto : Option Autosens) :
    iobOut env s t auto = generate (iobInputs env s t auto) := rfl

/-- **(a) An accepted bolus is in the treatments.** Let `LogOk s t` hold. Then every accepted
    bolus `Action.bolus tb u smb` in the log of `s` gives a treatment `bolusOf tb u` of
    `calcTempTreatments (iobInputs env s t auto) z`, for every `z`. With `z = none` this is
    the first call of `generate`; its second call runs on the history the first returns,
    which this theorem does not cover. -/
theorem bolus_mem_treatments {env : Env} {s : PState} {t : Int} (auto : Option Autosens)
    (z : Option JsNum) (hs : LogOk s t) {tb : Int} {u : Rat} {smb : Bool}
    (hb : Action.bolus tb u smb ∈ s.log) :
    bolusOf tb u ∈ (calcTempTreatments (iobInputs env s t auto) z).treatments := by
  obtain ⟨L1, L2, hlog⟩ := List.append_of_mem hb
  have hpw := hs.1
  rw [hlog, List.pairwise_append] at hpw
  have hr := calcTempTreatments_bolus (iobInputs env s t auto) z (L1.flatMap encodeAction)
    (L2.flatMap encodeAction ++ env.initHistory)
    { type_ := some "Bolus", amount := some (.fin u), timestamp := some (toString tb), timestampMs := some tb } tb
    (by simp [iobInputs, history, hlog, encodeAction])
    (fun q hq => by
      obtain ⟨a, ha, hqa⟩ := List.mem_flatMap.mp hq
      exact ⟨a.time, encodeAction_plain a q hqa, hpw.2.2 a ha (.bolus tb u smb) (by simp)⟩)
    ⟨rfl, rfl, rfl, rfl⟩ rfl (hs.2 _ hb)
  exact hr

/-- **(b) An accepted bolus bounds `lastBolusTime`.** Let `LogOk s t` hold and let the log of
    `s` hold an accepted bolus of `u ≠ 0` units at time `tb`. Then the `lastBolusTime` of
    `iobOut env s t auto` is finite and at least `tb`. -/
theorem lastBolusTime_ge {env : Env} {s : PState} {t : Int} (auto : Option Autosens)
    (hs : LogOk s t) {tb : Int} {u : Rat} {smb : Bool} (hb : Action.bolus tb u smb ∈ s.log) (hu : u ≠ 0) :
    ∃ y : Rat, (iobOut env s t auto).lastBolusTime = .fin y ∧ (tb : Rat) ≤ y := by
  rw [iobOut_eq, generate_lastBolusTime]
  exact foldl_lastStep_bolus tb _ _ _ (bolus_mem_treatments auto none hs hb)
    (by simp [bolusOf, Option.truthyN, JsNum.truthy, hu]) rfl ⟨0, rfl⟩

/-! ### The log of a legal run -/

theorem applyCmd_log (t : Int) (s : PState) (c : Cmd) :
    ∃ new, (applyCmd t s c).log = new ++ s.log ∧ ∀ a ∈ new, a.time = t := by
  unfold applyCmd
  rcases c with ⟨tmp, bol⟩
  cases tmp with
  | none =>
    cases bol with
    | none => exact ⟨[], rfl, by simp⟩
    | some u => exact ⟨[.bolus t u true], rfl, by simp [Action.time]⟩
  | some rd =>
    cases bol with
    | none => exact ⟨[.temp t rd.1 rd.2], rfl, by simp [Action.time]⟩
    | some u => exact ⟨[.bolus t u true, .temp t rd.1 rd.2], rfl, by simp [Action.time]⟩

theorem applyEvent_log (t : Int) (s : PState) (e : Event) :
    ∃ new, (applyEvent t s e).log = new ++ s.log ∧ ∀ a ∈ new, a.time = t := by
  cases e with
  | reading r => exact ⟨[], rfl, by simp⟩
  | userBolus u =>
    by_cases hu : 0 < u
    · exact ⟨[.bolus t u false], by simp [applyEvent, hu], by simp [Action.time]⟩
    · exact ⟨[], by simp [applyEvent, hu], by simp⟩
  | cycle inp res out =>
    unfold applyEvent
    cases out with
    | lost => exact ⟨[], rfl, by simp⟩
    | accepted =>
      dsimp only
      split
      · exact applyCmd_log t s _
      · exact ⟨[], rfl, by simp⟩

theorem logOk_applyEvent {t : Int} {s : PState} (e : Event) (h : LogOk s t) : LogOk (applyEvent t s e) t := by
  obtain ⟨new, hnew, ht⟩ := applyEvent_log t s e
  unfold LogOk
  rw [hnew, List.pairwise_append]
  refine ⟨⟨?_, h.1, fun a ha b hb => by rw [ht a ha]; exact h.2 b hb⟩, ?_⟩
  · exact List.pairwise_of_forall_mem_list (fun a ha b hb => by rw [ht a ha, ht b hb]; exact Int.le_refl t)
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rw [ht a ha]; exact Int.le_refl t
    · exact h.2 a ha

theorem logOk_mono {s : PState} {t t' : Int} (h : LogOk s t) (htt : t ≤ t') : LogOk s t' :=
  ⟨h.1, fun a ha => Int.le_trans (h.2 a ha) htt⟩

theorem logOk_foldl {t : Int} : ∀ (es : List Event) (s : PState), LogOk s t →
    LogOk (es.foldl (applyEvent t) s) t
  | [], _, h => h
  | e :: es, _, h => logOk_foldl es _ (logOk_applyEvent e h)

theorem logOk_cyclesEvents {t : Int} : ∀ (s : PState) (es : List Event), LogOk s t →
    ∀ c ∈ cyclesEvents t s es, LogOk c.pre c.time
  | _, [], _, c, hc => by simp [cyclesEvents] at hc
  | s, e :: es, h, c, hc => by
    simp only [cyclesEvents, List.mem_append] at hc
    rcases hc with hc | hc
    · cases e with
      | cycle inp res out =>
        simp only [List.mem_singleton] at hc; subst hc; exact h
      | _ => simp at hc
    · exact logOk_cyclesEvents _ es (logOk_applyEvent e h) c hc

theorem logOk_cyclesFrom : ∀ (s : PState) (r : Run Event), Increasing r → (∀ st ∈ r, LogOk s st.time) →
    ∀ c ∈ cyclesFrom s r, LogOk c.pre c.time
  | _s, [], _, _, c, hc => by simp [cyclesFrom] at hc
  | s, st :: r, hinc, h, c, hc => by
    simp only [cyclesFrom, List.mem_append] at hc
    have hst : LogOk s st.time := h st (by simp)
    rcases hc with hc | hc
    · exact logOk_cyclesEvents s st.events hst c hc
    · have hinc' : Increasing (st :: r) := hinc
      unfold Increasing at hinc'
      rw [List.pairwise_cons] at hinc'
      refine logOk_cyclesFrom _ r hinc'.2 (fun st' hst' => ?_) c hc
      exact logOk_mono (logOk_foldl st.events s hst) (Int.le_of_lt (hinc'.1 st' hst'))

/-- In a legal run, the log before every cycle is newest first and holds no action after
    the cycle. -/
theorem Legal.logOk {env : Env} {r : Run Event} (hl : Legal env r) :
    ∀ c ∈ cycles env r, LogOk c.pre c.time :=
  logOk_cyclesFrom env.init r hl.increasing (fun _ _ => ⟨List.Pairwise.nil, by simp [Env.init]⟩)

/-- **(b) for runs.** Let `c` be a cycle of a legal run whose prior log holds an accepted
    bolus of `u ≠ 0` units at time `tb`. Then the `lastBolusTime` of
    `iobOut env c.pre c.time c.inp.autosens_data`, from which the cycle's `iob_data` input
    is built, is finite and at least `tb`. -/
theorem Legal.bolusSeen {env : Env} {r : Run Event} (hl : Legal env r)
    {c : CycleAt} (hc : c ∈ cycles env r) {tb : Int} {u : Rat} {smb : Bool}
    (hb : Action.bolus tb u smb ∈ c.pre.log) (hu : u ≠ 0) :
    ∃ y : Rat, (iobOut env c.pre c.time c.inp.autosens_data).lastBolusTime = .fin y ∧ (tb : Rat) ≤ y :=
  lastBolusTime_ge _ (hl.logOk c hc) hb hu

/-! ### (c) Frozen accounting on `iobTotal`

A bolus dated at the evaluation time `t` has `minsAgo = 0`, and on the bilinear curve its
IOB contribution is exactly `rd u` (`bilinear_at_zero`). The exponential curves are not
covered. The bolus is appended at the end of the treatments: `iobTotal` adds in list
order, and double addition is not associative. -/

section
open Binary64 LeanAID.Proofs

theorem minsAgo_self (t : Int) :
    JsNum.mathRound ((JsNum.fin t - DateFmt.timeClip (.fin t)) / 1000 / 60) = 0 := by
  rw [timeClip_int]
  show JsNum.mathRound ((JsNum.fin (rd ((t : Rat) - t))) / 1000 / 60) = 0
  simp only [Rat.sub_self, rd_zero]
  decide +kernel

theorem dia_ago_lt {t : Int} {d : Rat} (hd : 3 ≤ d) (ht : (t - 1).natAbs ≤ 2 ^ 53) :
    (JsNum.fin t >ʲ (JsNum.fin t - JsNum.fin d * 60 * 60 * 1000)) = true := by
  show decide (rd ((t : Rat) - rd (rd (rd (d * 60) * 60) * 1000)) < t) = true
  have h1 : ((180 : Int) : Rat) ≤ rd (d * 60) := int_le_rd (by decide) (by simp; grind)
  have h2 : ((10800 : Int) : Rat) ≤ rd (rd (d * 60) * 60) := int_le_rd (by decide) (by simp at h1 ⊢; grind)
  have h3 : ((1 : Int) : Rat) ≤ rd (rd (rd (d * 60) * 60) * 1000) := int_le_rd (by decide) (by simp at h2 ⊢; grind)
  have h4 : rd ((t : Rat) - rd (rd (rd (d * 60) * 60) * 1000)) ≤ ((t - 1 : Int) : Rat) :=
    rd_le_int ht (by simp at h3 ⊢; grind)
  simp at h4 ⊢
  grind

theorem iobStep_bolus (p : Profile) (t : Int) (d : Rat) (peak : JsNum) (acc : IobAcc) (b : Treatment) (u : Rat)
    (hi : b.insulin = some (.fin u)) (hdate : b.date = .fin t)
    (hd : 3 ≤ d) (ht : (t - 1).natAbs ≤ 2 ^ 53) (hu : rd u ≠ 0) :
    (iobStep p t "bilinear" (.fin d) peak acc b).1 = acc.1 + .fin (rd u) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := acc
  have hu0 : u ≠ 0 := by intro h; subst h; simp at hu
  have hle : (b.date ≤ʲ JsNum.fin t) = true := by rw [hdate]; simp
  have hgt : (b.date >ʲ JsNum.fin t - JsNum.fin d * 60 * 60 * 1000) = true := by
    rw [hdate]; exact dia_ago_lt hd ht
  have htr : b.insulin.truthyN = true := by simp [hi, Option.truthyN, JsNum.truthy, hu0]
  have hcalc : iobCalc b t "bilinear" (.fin d) peak p = some (iobCalcBilinear (.fin u) 0 (.fin d)) := by
    unfold iobCalc
    simp [hdate, minsAgo_self, hi, Option.truthyN, JsNum.truthy, hu0, Option.js, JsNum.ofOpt]
  have hr : (JsNum.fin (rd u)).truthy = true := by simp [JsNum.truthy, hu]
  unfold iobStep
  simp only [hle, ite_true, hgt, hcalc, bilinear_at_zero u d (by grind), hr]
  split <;> (try split) <;> rfl

/-- Let the curve of `p` be bilinear with DIA `d`, and let `b` be a treatment of `u` units
    dated `t`, with `rd u ≠ 0` and `|t − 1| ≤ 2⁵³`. Then appending `b` to `T` changes the raw
    IOB sum at `t` by one double addition of `rd u`:
    ```text
    iobRaw(T ++ [b], p, t).iob = iobRaw(T, p, t).iob + rd(u)
    ```
    -/
theorem iobRaw_append (T : List Treatment) (p : Profile) (t : Int) (b : Treatment) (u d : Rat)
    (hc : (curveSetup p).1 = "bilinear") (hdia : (curveSetup p).2.1 = .fin d)
    (hi : b.insulin = some (.fin u)) (hdate : b.date = .fin t)
    (ht : (t - 1).natAbs ≤ 2 ^ 53) (hu : rd u ≠ 0) :
    (iobRaw (T ++ [b]) p t).1 = (iobRaw T p t).1 + .fin (rd u) := by
  unfold iobRaw
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hc, hdia]
  exact iobStep_bolus p t d _ _ b u hi hdate (curveSetup_dia p hdia).1 ht hu

theorem iobTotal_iob (T : List Treatment) (p : Profile) (t : Int) :
    (iobTotal T p t).iob = JsNum.mathRound ((iobRaw T p t).1 * 1000) / 1000 := rfl

end

end LeanAID.Time
