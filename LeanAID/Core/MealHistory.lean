/-
  LeanAID.Core.MealHistory — transcription of `lib/meal/history.js`
  (`findMealInputs`, lines 19-139): collect carb and bolus entries from pump
  history and Nightscout carb records, removing duplicates.
-/
import LeanAID.Core.Iob

namespace LeanAID.MealHistory

open JsNum Iob

/-- An element of `mealInputs`. `timestampMs` is `new Date(timestamp)`. -/
structure MealInput where
  timestamp : Option String := none
  timestampMs : Option Int := none
  carbs : Option JsNum := none
  nsCarbs : Option JsNum := none
  bwCarbs : Option JsNum := none
  journalCarbs : Option JsNum := none
  bolus : Option JsNum := none
  deriving Repr, Inhabited, BEq

/-- Which property `arrayHasElementWithSameTimestampAndProperty` checks. -/
inductive Prop_ where
  | carbs
  | bolus
  deriving DecidableEq

def MealInput.has (m : MealInput) : Prop_ → Bool
  | .carbs => m.carbs.isSome
  | .bolus => m.bolus.isSome

/-- `arrayHasElementWithSameTimestampAndProperty(array, t, propname)`, lines 3-17:
    an element with the property whose timestamp equals `t`, or lies strictly
    within 2 seconds of it. -/
def hasSame (arr : List MealInput) (t : Option String) (tMs : Option Int) (prop : Prop_) : Bool :=
  arr.any fun e =>
    (e.timestamp == t && e.has prop) ||
    (e.has prop && match e.timestampMs, tMs with
      | some ed, some td => decide (td - 2000 < ed) && decide (ed < td + 2000)
      | _, _ => false)

/-- A Nightscout carb record (`inputs.carbs`). -/
structure CarbRecord where
  carbs : Option JsNum := none
  created_at : Option String := none
  created_atMs : Option Int := none
  deriving Repr, Inhabited

/-- Pump-history fields read by findMealInputs (in addition to `PumpFields`). -/
structure MealPumpRecord where
  base : PumpFields
  carbs : Option JsNum := none
  carb_input : Option JsNum := none
  deriving Repr, Inhabited

/-- `findMealInputs(inputs)`, lines 19-139. -/
def findMealInputs (pumpHistory : List MealPumpRecord) (carbHistory : List CarbRecord) : List MealInput :=
  -- lines 27-40
  let m1 := carbHistory.foldl (fun acc c =>
    if c.carbs.truthyN && c.created_at.isSome then
      let t : MealInput := { timestamp := c.created_at, timestampMs := c.created_atMs, carbs := c.carbs, nsCarbs := c.carbs }
      if !hasSame acc c.created_at c.created_atMs .carbs then acc ++ [t] else acc
    else acc) []
  -- lines 42-105
  let (m2, bw) := pumpHistory.foldl (fun (acc, bw) r =>
    let cur := r.base
    let add := fun (t : MealInput) (ts : Option String) (tsMs : Option Int) (prop : Prop_) =>
      if !hasSame acc ts tsMs prop then (acc ++ [t], bw) else (acc, bw)
    if cur.type_ == some "Bolus" && cur.timestamp.isSome then
      add { timestamp := cur.timestamp, timestampMs := cur.timestampMs, bolus := cur.amount }
        cur.timestamp cur.timestampMs .bolus
    else if cur.type_ == some "BolusWizard" && cur.timestamp.isSome then (acc, bw ++ [r])
    else if (cur.type_ == some "Meal Bolus" || cur.type_ == some "Correction Bolus" || cur.type_ == some "Snack Bolus" ||
             cur.type_ == some "Bolus Wizard" || cur.type_ == some "Carb Correction") && cur.created_at.isSome then
      add { timestamp := cur.created_at, timestampMs := cur.created_atMs, carbs := r.carbs, nsCarbs := r.carbs }
        cur.created_at cur.created_atMs .carbs
    else if cur.enteredBy == some "xdrip" then
      -- QUIRK: the entry gets created_at as timestamp, but the duplicate check uses `current.timestamp`
      add { timestamp := cur.created_at, timestampMs := cur.created_atMs, carbs := r.carbs, nsCarbs := r.carbs,
            bolus := cur.insulin } cur.timestamp cur.timestampMs .carbs
    else if r.carbs.js >ʲ 0 then
      add { carbs := r.carbs, nsCarbs := r.carbs, timestamp := cur.created_at, timestampMs := cur.created_atMs,
            bolus := cur.insulin } cur.timestamp cur.timestampMs .carbs
    else if cur.type_ == some "JournalEntryMealMarker" && r.carb_input.js >ʲ 0 && cur.timestamp.isSome then
      add { timestamp := cur.timestamp, timestampMs := cur.timestampMs, carbs := r.carb_input, journalCarbs := r.carb_input }
        cur.timestamp cur.timestampMs .carbs
    else (acc, bw)) (m1, [])
  -- lines 107-136: bolus wizard records, kept only if a bolus has the same timestamp
  bw.foldl (fun acc r =>
    let cur := r.base
    let t : MealInput := { timestamp := cur.timestamp, timestampMs := cur.timestampMs, carbs := r.carb_input,
                           bwCarbs := r.carb_input }
    if !hasSame acc cur.timestamp cur.timestampMs .carbs then
      if hasSame acc cur.timestamp cur.timestampMs .bolus then acc ++ [t] else acc
    else acc) m2

end LeanAID.MealHistory
