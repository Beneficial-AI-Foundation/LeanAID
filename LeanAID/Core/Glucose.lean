/-
  LeanAID.Core.Glucose — transcription of `lib/glucose-get-last.js` (lines 1-89):
  from the CGM history to `glucose_status`.
-/
import LeanAID.Core.Types

namespace LeanAID.Glucose

open JsNum

/-- One CGM entry. Date strings are parsed by the shell with `Date.parse`. -/
structure Entry where
  glucose : Option JsNum := none
  sgv : Option JsNum := none
  noise : Option JsNum := none
  type_ : Option String := none
  device : Option String := none
  date : Option JsNum := none
  /-- `Date.parse(entry.display_time)`; `none` for undefined or unparsable -/
  displayTimeMs : Option JsNum := none
  /-- `Date.parse(entry.dateString)` -/
  dateStringMs : Option JsNum := none
  deriving Repr, Inhabited

/-- `getDateFromEntry(entry)`, lines 1-3:
    `entry.date || Date.parse(entry.display_time) || Date.parse(entry.dateString)`. -/
def getDateFromEntry (e : Entry) : JsNum :=
  if e.date.truthyN then e.date.js
  else if e.displayTimeMs.truthyN then e.displayTimeMs.js
  else e.dateStringMs.js

/-- `getLastGlucose(data)`, lines 5-89. `none` when `data` has no usable entry
    (the JavaScript throws reading `data[0]`). -/
def getLastGlucose (data0 : List Entry) : Option GlucoseStatus := do
  -- lines 6-14: keep entries with a truthy glucose or sgv; glucose := glucose || sgv
  let data := (data0.filter fun o => o.glucose.truthyN || o.sgv.truthyN).map fun o =>
    { o with glucose := if o.glucose.truthyN then o.glucose else o.sgv }
  let now ← data.head?
  let rest := data.tail
  -- state: now.glucose, now_date, last/short/long deltas, last_cal
  let init : JsNum × JsNum × Array JsNum × Array JsNum × Array JsNum × Nat × Bool :=
    (now.glucose.js, getDateFromEntry now, #[], #[], #[], 0, false)
  let (nowGlucose, nowDate, lastDeltas, shortDeltas, longDeltas, lastCal, _) :=
    rest.zipIdx.foldl (fun st (e, k) =>
      let (g, nd, ld, sd, lgd, lc, stop) := st
      if stop then st
      -- lines 26-29: a calibration record stops the scan
      else if e.type_ == some "cal" then (g, nd, ld, sd, lgd, k + 1, true)
      else if e.glucose.js >ʲ 38 && e.device == now.device then
        let thenDate := getDateFromEntry e
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
      else st) init
  let avg := fun (a : Array JsNum) => if a.size > 0 then a.foldl (· + ·) (0 : JsNum) / .fin a.size else 0
  let r2 := fun (x : JsNum) => mathRound (x * 100) / 100
  return { delta := some (r2 (avg lastDeltas)), glucose := some (r2 nowGlucose), noise := some (mathRound now.noise.js),
           short_avgdelta := some (r2 (avg shortDeltas)), long_avgdelta := some (r2 (avg longDeltas)),
           date := some nowDate, last_cal := some (.fin lastCal), device := now.device }

end LeanAID.Glucose
