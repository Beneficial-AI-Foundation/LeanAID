import LeanAID.Fixed.SplitTimespan
import LeanAID.Proofs.SplitTimespan

/-!
# F-24: theorems about the fixed `splitTimespan`

* `generateW_splitTimespan`: the parametrized IOB pipeline with oref0's `splitTimespan` is
  the transcription `LeanAID.Iob.generate` (by `rfl`).
* `generateF24_eq` (**nothing else changed**): if oref0's `splitTimespan` drops no piece of
  any temp it splits (`¬ TriggerF24`), the fixed IOB equals oref0's.
* `splitTimespanF24_tiles` (**the fix works**): the pieces of the fixed `splitTimespan` tile
  the temp. Each piece is kept or replaced by the two parts of a split, and
  `splitOne_parts` says what the two parts are: the first starts where the piece starts and
  lasts `d₁`, the second starts `d₁` minutes later and lasts `d − d₁`.
* `splitPassF24_eq_splitPassFixed`: the fixed pass is `Q6.splitPassFixed` of
  `LeanAID/Proofs/SplitTimespan.lean`, so `q6_fixed_keeps` is an example of this fix.
-/

namespace LeanAID.Fixed

open LeanAID LeanAID.Iob JsNum

/-! ### The parametrized pipeline is the transcription -/

theorem splitStageW_splitTimespan (inp : HistoryInputs) (thO : Array TempEvent) (suspends : List Suspend)
    (firstResumeMs : Option Int) (suspendedPrior currentlySuspended : Bool) (lastSuspendTime : Option String) :
    splitStageW splitTimespan inp thO suspends firstResumeMs suspendedPrior currentlySuspended lastSuspendTime =
      splitStage inp thO suspends firstResumeMs suspendedPrior currentlySuspended lastSuspendTime := by
  unfold splitStageW splitStage suspendZeros
  rfl

theorem calcTempTreatmentsW_splitTimespan (inp : HistoryInputs) (z : Option JsNum) :
    calcTempTreatmentsW splitTimespan inp z = calcTempTreatments inp z := by
  unfold calcTempTreatmentsW calcTempTreatments preSplit
  simp only [splitStageW_splitTimespan]

/-- With oref0's `splitTimespan`, the parametrized pipeline is `LeanAID.Iob.generate`. -/
theorem generateW_splitTimespan (inp : HistoryInputs) (c : Bool) :
    generateW splitTimespan inp c = generate inp c := by
  unfold generateW generate
  simp only [calcTempTreatmentsW_splitTimespan]

/-! ### The fixed pass -/

/-- The step of the fixed pass. -/
def stepF24 (splitters : List JsNum) (tz : Int) : List TempEvent × Bool → TempEvent → List TempEvent × Bool :=
  fun x o => match x with
    | (acc, splitFound) =>
      match splitPass.tryAll tz o splitters with
      | some r => (acc ++ r, true)
      | none => (acc ++ [o], splitFound)

theorem splitPassF24_eq_foldl (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    splitPassF24 splitters tz rs = rs.foldl (stepF24 splitters tz) ([], false) := rfl

theorem foldl_stepF24 (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    ∀ acc b, rs.foldl (stepF24 splitters tz) (acc, b) =
      (acc ++ rs.flatMap (fun o => (Q6.trySplit splitters tz o).getD [o]),
       b || rs.any (fun o => (Q6.trySplit splitters tz o).isSome)) := by
  induction rs with
  | nil => intro acc b; simp
  | cons o os ih =>
    intro acc b
    simp only [List.foldl_cons, List.flatMap_cons, List.any_cons]
    cases h : splitPass.tryAll tz o splitters with
    | none =>
      have h' : Q6.trySplit splitters tz o = none := h
      simp [stepF24, h, ih, List.append_assoc]
    | some r =>
      have h' : Q6.trySplit splitters tz o = some r := h
      simp [stepF24, h, ih, List.append_assoc]

/-- The fixed pass is `Q6.splitPassFixed` (`LeanAID/Proofs/SplitTimespan.lean`). -/
theorem splitPassF24_eq_splitPassFixed (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    splitPassF24 splitters tz rs = Q6.splitPassFixed splitters tz rs := by
  rw [splitPassF24_eq_foldl, foldl_stepF24]
  simp [Q6.splitPassFixed]

/-- `splitTimespanF24` is `Q6.splitTimespanFixed`, so `Q6.q6_fixed_keeps` is about this fix. -/
theorem splitTimespanF24_eq (e : TempEvent) (splitters : List JsNum) (tz : Int) :
    splitTimespanF24 e splitters tz = Q6.splitTimespanFixed e splitters tz := by
  unfold splitTimespanF24 Q6.splitTimespanFixed
  generalize [e] = rs
  generalize 10000 = n
  induction n generalizing rs with
  | zero => rfl
  | succ n ih =>
    simp only [splitTimespanF24.go, Q6.splitTimespanFixed.go, splitPassF24_eq_splitPassFixed]
    split <;> simp_all

/-! ### Nothing else changed -/

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- If oref0's pass drops no piece, the fixed pass is oref0's pass (both components). -/
theorem foldl_eq_of_not_drops (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    ∀ acc seen, passDrops splitters tz seen rs = false →
      rs.foldl (Q6.step splitters tz) (acc, seen) = rs.foldl (stepF24 splitters tz) (acc, seen) := by
  induction rs with
  | nil => intro acc seen _; rfl
  | cons o os ih =>
    intro acc seen h
    simp only [passDrops, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.foldl_cons]
    cases ht : splitPass.tryAll tz o splitters with
    | none =>
      have ht' : Q6.trySplit splitters tz o = none := ht
      rw [ht] at h1 h2
      simp only [Option.isSome_none, Bool.not_false, Bool.or_false] at h1 h2
      have hs : seen = false := by cases seen <;> simp_all
      subst hs
      simp only [Q6.step, stepF24, ht', ht, Bool.not_false]
      exact ih _ _ h2
    | some r =>
      have ht' : Q6.trySplit splitters tz o = some r := ht
      rw [ht] at h2
      simp only [Option.isSome_some, Bool.or_true] at h2
      simp only [Q6.step, stepF24, ht', ht]
      exact ih _ _ h2

theorem splitPass_eq_of_not_drops (splitters : List JsNum) (tz : Int) (rs : List TempEvent)
    (h : passDrops splitters tz false rs = false) :
    splitPass splitters tz rs = splitPassF24 splitters tz rs := by
  rw [Q6.splitPass_eq_foldl, splitPassF24_eq_foldl]
  exact foldl_eq_of_not_drops splitters tz rs [] false h

/-- If oref0's `splitTimespan` drops no piece of `e`, the fixed one gives the same pieces. -/
theorem splitTimespanF24_eq_of_not_q6 (e : TempEvent) (splitters : List JsNum) (tz : Int)
    (h : q6Event e splitters tz = false) : splitTimespanF24 e splitters tz = splitTimespan e splitters tz := by
  unfold splitTimespanF24 splitTimespan
  unfold q6Event at h
  generalize [e] = rs at h ⊢
  generalize 10000 = n at h ⊢
  induction n generalizing rs with
  | zero => rfl
  | succ n ih =>
    simp only [q6Event.go, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := h
    simp only [splitTimespanF24.go, splitTimespan.go, ← splitPass_eq_of_not_drops splitters tz rs h1]
    cases hp : splitPass splitters tz rs with
    | mk rs' found =>
      rw [hp] at h2
      cases found
      · rfl
      · exact ih rs' h2

/-- `splitStageW` depends on the split function only through the temps it splits. -/
theorem splitStageW_congr (s1 s2 : SplitFn) (inp : HistoryInputs) (thO : Array TempEvent) (suspends : List Suspend)
    (firstResumeMs : Option Int) (suspendedPrior currentlySuspended : Bool) (lastSuspendTime : Option String)
    (h : ∀ e ∈ thO.toList ++ (if inp.profile.suspend_zeros_iob.truthy then
        suspendZeros inp suspends firstResumeMs suspendedPrior currentlySuspended lastSuspendTime else []),
      s1 e (inp.profile.basalprofile.map (·.minutes)) inp.tzOffsetMin =
        s2 e (inp.profile.basalprofile.map (·.minutes)) inp.tzOffsetMin) :
    splitStageW s1 inp thO suspends firstResumeMs suspendedPrior currentlySuspended lastSuspendTime =
      splitStageW s2 inp thO suspends firstResumeMs suspendedPrior currentlySuspended lastSuspendTime := by
  have hA : thO.toList.flatMap (fun o => s1 o (inp.profile.basalprofile.map (·.minutes)) inp.tzOffsetMin) =
      thO.toList.flatMap (fun o => s2 o (inp.profile.basalprofile.map (·.minutes)) inp.tzOffsetMin) :=
    flatMap_congr' (fun e he => h e (List.mem_append_left _ he))
  unfold splitStageW
  simp only
  rw [hA]
  split
  · rename_i hz
    have hB : (suspendZeros inp suspends firstResumeMs suspendedPrior currentlySuspended lastSuspendTime).flatMap
          (fun o => s1 o (inp.profile.basalprofile.map (·.minutes)) inp.tzOffsetMin) =
        (suspendZeros inp suspends firstResumeMs suspendedPrior currentlySuspended lastSuspendTime).flatMap
          (fun o => s2 o (inp.profile.basalprofile.map (·.minutes)) inp.tzOffsetMin) :=
      flatMap_congr' (fun e he => h e (List.mem_append_right _ (by simp [hz, he])))
    rw [hB]
  · rfl

/-- `calcTempTreatmentsW` depends on the split function only through `splitArgs`. -/
theorem calcTempTreatmentsW_congr (s1 s2 : SplitFn) (inp : HistoryInputs) (z : Option JsNum)
    (h : ∀ e ∈ splitArgs inp z, s1 e (inp.profile.basalprofile.map (·.minutes)) inp.tzOffsetMin =
        s2 e (inp.profile.basalprofile.map (·.minutes)) inp.tzOffsetMin) :
    calcTempTreatmentsW s1 inp z = calcTempTreatmentsW s2 inp z := by
  unfold calcTempTreatmentsW
  simp only
  rw [splitStageW_congr s1 s2 inp _ _ _ _ _ _ h]

/-- **F-24, nothing else changed.** If oref0's `splitTimespan` drops no piece of any temp
    it splits in the two calls of `calcTempTreatments` (`¬ TriggerF24 inp`), the IOB with
    the fix is oref0's IOB: `generateF24 inp c = generate inp c`. No other hypothesis. -/
theorem generateF24_eq (inp : HistoryInputs) (c : Bool) (h : ¬ TriggerF24 inp) :
    generateF24 inp c = generate inp c := by
  unfold TriggerF24 triggerF24 at h
  simp only [Bool.not_eq_true, List.any_eq_false, Bool.not_eq_true] at h
  have hq : ∀ (i : HistoryInputs) (z : Option JsNum), i.profile = inp.profile → i.tzOffsetMin = inp.tzOffsetMin →
      (∀ e ∈ splitArgs i z, q6Event e (inp.profile.basalprofile.map (·.minutes)) inp.tzOffsetMin = false) →
      calcTempTreatmentsW splitTimespanF24 i z = calcTempTreatments i z := by
    intro i z hp htz hz
    rw [← calcTempTreatmentsW_splitTimespan]
    apply calcTempTreatmentsW_congr
    intro e he
    rw [hp, htz]
    exact splitTimespanF24_eq_of_not_q6 e _ _ (hz e he)
  have h1 := hq inp none rfl rfl (fun e he => h e (List.mem_append_left _ he))
  -- the history passed to the second call does not depend on the split function
  have hh : (calcTempTreatmentsW splitTimespanF24 inp none).history = (calcTempTreatments inp none).history := rfl
  have h2 := hq { inp with history := (calcTempTreatments inp none).history, history24 := none } (some 240) rfl rfl
    (fun e he => h e (List.mem_append_right _ he))
  rw [← generateW_splitTimespan]
  unfold generateF24 generateW
  simp only
  rw [hh, h1, h2, calcTempTreatmentsW_splitTimespan, calcTempTreatmentsW_splitTimespan]

/-! ### The fix works: the pieces tile the temp -/

/-- `Tiles splitters tz o ps`: the pieces `ps` arise from `o` by a tree of splits. Either
    `ps = [o]`, or some splitter `s` splits `o` into `[a, b]` (`splitOne`) and `ps` is a
    tiling of `a` followed by a tiling of `b`. No piece is lost on the way. -/
inductive Tiles (splitters : List JsNum) (tz : Int) : TempEvent → List TempEvent → Prop
  | keep (o : TempEvent) : Tiles splitters tz o [o]
  | split (o a b : TempEvent) (s : JsNum) (la lb : List TempEvent) :
      s ∈ splitters → splitOne o s tz = [a, b] →
      Tiles splitters tz a la → Tiles splitters tz b lb → Tiles splitters tz o (la ++ lb)

/-- **The two parts of a split.** If `splitOne` splits `o` (at a splitter, at midnight or
    after 30 minutes), it returns exactly two parts `[a, b]`: `a` starts where `o` starts
    and lasts `d₁ = a.duration`, `b` starts `d₁` minutes later (as `moment().add()` and
    `format()` compute it) and lasts `o.duration − d₁` (a JavaScript subtraction). Both keep
    `o`'s rate. -/
theorem splitOne_parts {o : TempEvent} {s : JsNum} {tz : Int} {r : List TempEvent}
    (h : splitOne o s tz = r) (hl : r.length > 1) :
    ∃ a b, r = [a, b] ∧ a.startedAt = o.startedAt ∧ a.rate = o.rate ∧ b.rate = o.rate ∧
      addMinutesFormatted o.startedAt a.duration = some b.startedAt ∧ b.duration = o.duration - a.duration := by
  unfold splitOne at h
  simp only at h
  split at h
  · split at h
    · rename_i t2 ht2
      subst h
      exact ⟨_, _, rfl, rfl, rfl, rfl, ht2, rfl⟩
    · subst h; simp at hl
  · subst h; simp at hl

theorem tryAll_some {tz : Int} {o : TempEvent} :
    ∀ (ss : List JsNum) {r : List TempEvent}, splitPass.tryAll tz o ss = some r →
      ∃ s ∈ ss, splitOne o s tz = r ∧ r.length > 1
  | [], r, h => by simp [splitPass.tryAll] at h
  | s :: ss, r, h => by
    simp only [splitPass.tryAll] at h
    split at h
    · cases h; exact ⟨s, by simp, rfl, by assumption⟩
    · obtain ⟨s', hs', h1, h2⟩ := tryAll_some ss h
      exact ⟨s', by simp [hs'], h1, h2⟩

/-- A list of pieces tiled piece by piece. -/
inductive TilesL (splitters : List JsNum) (tz : Int) : List TempEvent → List TempEvent → Prop
  | nil : TilesL splitters tz [] []
  | cons (o : TempEvent) (lo os los : List TempEvent) :
      Tiles splitters tz o lo → TilesL splitters tz os los → TilesL splitters tz (o :: os) (lo ++ los)

theorem TilesL.refl (splitters : List JsNum) (tz : Int) : ∀ rs, TilesL splitters tz rs rs
  | [] => .nil
  | o :: os => by
    have := TilesL.cons o [o] os os (.keep o) (TilesL.refl splitters tz os)
    simpa using this

theorem TilesL.append {splitters : List JsNum} {tz : Int} {l1 q1 l2 q2 : List TempEvent}
    (h1 : TilesL splitters tz l1 q1) (h2 : TilesL splitters tz l2 q2) : TilesL splitters tz (l1 ++ l2) (q1 ++ q2) := by
  induction h1 with
  | nil => simpa using h2
  | cons o lo os los ho _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons o lo (os ++ l2) (los ++ q2) ho ih

theorem TilesL.split_append {splitters : List JsNum} {tz : Int} :
    ∀ {l1 l2 q : List TempEvent}, TilesL splitters tz (l1 ++ l2) q →
      ∃ q1 q2, q = q1 ++ q2 ∧ TilesL splitters tz l1 q1 ∧ TilesL splitters tz l2 q2
  | [], l2, q, h => ⟨[], q, rfl, .nil, by simpa using h⟩
  | o :: os, l2, q, h => by
    rw [List.cons_append] at h
    cases h with
    | cons _ lo _ los ho hrest =>
      obtain ⟨q1, q2, hq, h1, h2⟩ := TilesL.split_append hrest
      exact ⟨lo ++ q1, q2, by rw [hq, List.append_assoc], .cons o lo os q1 ho h1, h2⟩

theorem Tiles.trans {splitters : List JsNum} {tz : Int} {o : TempEvent} {lo : List TempEvent}
    (h : Tiles splitters tz o lo) : ∀ {q}, TilesL splitters tz lo q → Tiles splitters tz o q := by
  induction h with
  | keep o =>
    intro q hq
    cases hq with
    | cons _ lo' _ los ho hrest => cases hrest; simpa using ho
  | split o a b s la lb hs hsp _ _ iha ihb =>
    intro q hq
    obtain ⟨q1, q2, rfl, h1, h2⟩ := TilesL.split_append hq
    exact .split o a b s q1 q2 hs hsp (iha h1) (ihb h2)

theorem TilesL.trans {splitters : List JsNum} {tz : Int} {rs ps qs : List TempEvent}
    (h1 : TilesL splitters tz rs ps) (h2 : TilesL splitters tz ps qs) : TilesL splitters tz rs qs := by
  induction h1 generalizing qs with
  | nil => simpa using h2
  | cons o lo os los ho _ ih =>
    obtain ⟨q1, q2, rfl, hq1, hq2⟩ := TilesL.split_append h2
    exact .cons o q1 os q2 (ho.trans hq1) (ih hq2)

/-- One fixed pass tiles its input piece by piece. -/
theorem splitPassF24_tiles (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    TilesL splitters tz rs (splitPassF24 splitters tz rs).1 := by
  rw [splitPassF24_eq_foldl, foldl_stepF24]
  simp only [List.nil_append]
  induction rs with
  | nil => exact .nil
  | cons o os ih =>
    rw [List.flatMap_cons]
    apply TilesL.cons _ _ _ _ _ ih
    cases ht : Q6.trySplit splitters tz o with
    | none => exact .keep o
    | some r =>
      obtain ⟨s, hs, hsp, hl⟩ := tryAll_some splitters ht
      obtain ⟨a, b, rfl, -⟩ := splitOne_parts hsp hl
      exact .split o a b s [a] [b] hs hsp (.keep a) (.keep b)

/-- **F-24, the fix works.** The pieces of the fixed `splitTimespan` tile the temp: no piece
    is dropped. Every piece of every pass is either kept or replaced by the two parts of its
    split (`splitOne_parts`), whatever the schedule, the time zone and the temp. -/
theorem splitTimespanF24_tiles (e : TempEvent) (splitters : List JsNum) (tz : Int) :
    Tiles splitters tz e (splitTimespanF24 e splitters tz) := by
  have key : ∀ n rs, TilesL splitters tz rs (splitTimespanF24.go splitters tz n rs) := by
    intro n
    induction n with
    | zero => intro rs; exact TilesL.refl splitters tz rs
    | succ n ih =>
      intro rs
      simp only [splitTimespanF24.go]
      have hp := splitPassF24_tiles splitters tz rs
      cases hq : splitPassF24 splitters tz rs with
      | mk rs' found =>
        rw [hq] at hp
        cases found
        · exact hp
        · exact hp.trans (ih rs')
  have h := key 10000 [e]
  unfold splitTimespanF24
  generalize splitTimespanF24.go splitters tz 10000 [e] = q at h ⊢
  cases h with
  | cons _ lo _ los ho hrest => cases hrest; simpa using ho

/-- On the F-24 example (`Q6.ev60`, a 60-minute zero temp from 05:50 with a schedule entry
    at 06:00) oref0 keeps 30 of the 60 minutes (`Q6.q6_drops_zero_temp`), the trigger holds
    for this temp, and the fix keeps all three pieces. -/
theorem q6Event_ev60 :
    q6Event Q6.ev60 Q6.splitters 0 = true ∧
    Q6.pieces (splitTimespanF24 Q6.ev60 Q6.splitters 0) =
      [(Q6.t550, 10), (Q6.t550 + 600000, 20), (Q6.t550 + 1800000, 30)] := by
  constructor
  · decide +kernel
  · rw [splitTimespanF24_eq]; exact Q6.q6_fixed_keeps

end LeanAID.Fixed
