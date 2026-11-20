import LeanAID.Core.Iob

/-!
# Q6: `splitTimespan` drops parts of a temp basal (F-24)

oref0 splits every temp basal into pieces of at most 30 minutes and at the start times of
the basal schedule (`lib/iob/history.js` lines 8-80), then turns each piece into IOB. In
one pass of the `while` loop the flag `splitFound` is shared by all pieces, so once one
piece has been split, every later piece of the same pass that does not split is dropped
(QUIRK Q6). `LeanAID.Iob.splitPass` transcribes this.

This file

* characterizes one pass of oref0 exactly (`splitPass_fst`): the pieces before the first
  split are kept, and after it only the pieces that split again survive,
* defines the fix (`splitPassFixed`, `splitTimespanFixed`), which keeps every piece that
  does not split (`splitPassFixed_fst`),
* checks with the kernel, on one example, that a 60-minute zero temp from 05:50 with a
  basal change at 06:00 keeps only 30 of its 60 minutes in oref0 (`q6_drops_zero_temp`)
  and all 60 with the fix (`q6_fixed_keeps`). These check the start and duration of each
  piece, not the other fields.

`scripts/probe-split-timespan.js` shows the same loss with oref0 under Node, in units
of insulin and in IOB.
-/

namespace LeanAID.Iob.Q6

open LeanAID.Iob

/-- The splitter search of one piece: the result of the first splitter that splits it. -/
abbrev trySplit (splitters : List JsNum) (tz : Int) (o : TempEvent) : Option (List TempEvent) :=
  splitPass.tryAll tz o splitters

/-- The step function of `splitPass`. -/
def step (splitters : List JsNum) (tz : Int) :
    List TempEvent × Bool → TempEvent → List TempEvent × Bool :=
  fun x o =>
    match x with
    | (acc, splitFound) =>
      match trySplit splitters tz o with
      | some r => (acc ++ r, true)
      | none => if (!splitFound) = true then (acc ++ [o], splitFound) else (acc, splitFound)

theorem splitPass_eq_foldl (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    splitPass splitters tz rs = rs.foldl (step splitters tz) ([], false) := rfl

/-- The pieces of a pass after its first split: only pieces that split survive. -/
def survivors (splitters : List JsNum) (tz : Int) (rs : List TempEvent) : List TempEvent :=
  rs.flatMap fun o => (trySplit splitters tz o).getD []

/-- The output of one pass of oref0, written without the shared flag. -/
def orefPass (splitters : List JsNum) (tz : Int) : List TempEvent → List TempEvent
  | [] => []
  | o :: os =>
    match trySplit splitters tz o with
    | some r => r ++ survivors splitters tz os
    | none => o :: orefPass splitters tz os

theorem foldl_step_true (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    ∀ acc, (rs.foldl (step splitters tz) (acc, true)).1 = acc ++ survivors splitters tz rs := by
  induction rs with
  | nil => intro acc; simp [survivors]
  | cons o os ih =>
    intro acc
    simp only [List.foldl_cons, survivors, List.flatMap_cons]
    cases h : trySplit splitters tz o with
    | none => simp [step, h, ih, survivors]
    | some r => simp [step, h, ih, survivors, List.append_assoc]

theorem foldl_step_false (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    ∀ acc, (rs.foldl (step splitters tz) (acc, false)).1 = acc ++ orefPass splitters tz rs := by
  induction rs with
  | nil => intro acc; simp [orefPass]
  | cons o os ih =>
    intro acc
    simp only [List.foldl_cons, orefPass]
    cases h : trySplit splitters tz o with
    | none => simp [step, h, ih, List.append_assoc]
    | some r => simp [step, h, foldl_step_true, List.append_assoc]

/-- One pass of oref0's `splitTimespan` (QUIRK Q6), exactly: the pieces before the first
    split are kept, the first split piece is replaced by its two parts, and after it every
    piece that does not split is dropped. -/
theorem splitPass_fst (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    (splitPass splitters tz rs).1 = orefPass splitters tz rs := by
  rw [splitPass_eq_foldl, foldl_step_false]; simp

/-! ### The fix -/

/-- One pass with the fix: a piece that does not split is kept. -/
def splitPassFixed (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    List TempEvent × Bool :=
  (rs.flatMap fun o => (trySplit splitters tz o).getD [o],
   rs.any fun o => (trySplit splitters tz o).isSome)

/-- With the fix every piece is either kept or replaced by its parts. -/
theorem splitPassFixed_fst (splitters : List JsNum) (tz : Int) (rs : List TempEvent) :
    (splitPassFixed splitters tz rs).1 = rs.flatMap fun o => (trySplit splitters tz o).getD [o] :=
  rfl

/-- `splitTimespan` with the fixed pass and the same fuel bound of 10 000 passes as the
    transcription. oref0's `while` loop has no bound, so this is a bounded model of the fix:
    no theorem here shows that the bound is never reached. -/
def splitTimespanFixed (e : TempEvent) (splitters : List JsNum) (tz : Int) : List TempEvent :=
  go 10000 [e]
where
  go : Nat → List TempEvent → List TempEvent
    | 0, rs => rs
    | fuel + 1, rs =>
      let (rs', found) := splitPassFixed splitters tz rs
      if found then go fuel rs' else rs'

/-! ### The counterexample -/

/-- 2026-11-18 05:50 UTC in milliseconds. -/
def t550 : Int := 1794981000000

/-- A 60-minute zero temp from 05:50 UTC. -/
def ev60 : TempEvent := { rate := 0, duration := 60, startedAt := t550, date := .fin t550 }

/-- A basal schedule with entries at 00:00 and 06:00 (`minutes` 0 and 360). -/
def splitters : List JsNum := [0, 360]

/-- The (start, duration) pair of each event. -/
def pieces (es : List TempEvent) : List (Int × JsNum) := es.map fun e => (e.startedAt, e.duration)

/-- oref0 keeps the pieces 05:50-06:00 and 06:00-06:20, 30 of the 60 minutes. The piece
    06:20-06:50 is dropped. -/
theorem q6_drops_zero_temp :
    pieces (splitTimespan ev60 splitters 0) =
      [(t550, 10), (t550 + 600000, 20)] := by
  decide +kernel

/-- With the fix all 60 minutes are kept: 05:50-06:00, 06:00-06:20 and 06:20-06:50. -/
theorem q6_fixed_keeps :
    pieces (splitTimespanFixed ev60 splitters 0) =
      [(t550, 10), (t550 + 600000, 20), (t550 + 1800000, 30)] := by
  decide +kernel

/-- One example without a schedule change during the temp: oref0 and the fix give the same
    two pieces. This is not a general theorem. -/
theorem q6_no_change :
    pieces (splitTimespan ev60 [0] 0) = [(t550, 30), (t550 + 1800000, 30)] ∧
    pieces (splitTimespanFixed ev60 [0] 0) = [(t550, 30), (t550 + 1800000, 30)] := by
  decide +kernel

end LeanAID.Iob.Q6
