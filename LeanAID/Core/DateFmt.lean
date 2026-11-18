/-
  LeanAID.Core.DateFmt — the parts of JavaScript's `Date` that oref0's outputs
  depend on: `new Date(x).getTime()`, `toString()`, `toISOString()` and
  `getMinutes()`. Pure integer arithmetic on epoch milliseconds.
-/
import LeanAID.Core.JsNum

namespace LeanAID.DateFmt

/-- `new Date(x).getTime()` for a number `x`: JavaScript's TimeClip truncates to an
    integer towards zero; `NaN` stays `NaN`. (Values beyond ±8.64e15 ms, which
    JavaScript also maps to `NaN`, are not modelled.) -/
def timeClip : JsNum → JsNum
  | .fin q => .fin (if q < 0 then -((-q).floor) else q.floor)
  | .nan => .nan

/-- Days since 1970-01-01 → (year, month 1-12, day 1-31). Howard Hinnant's
    `civil_from_days`. -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  ((if m ≤ 2 then y + 1 else y), m.toNat, d.toNat)

def pad (w : Nat) (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

def weekdays : Array String := #["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
def months : Array String := #["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- Broken-down time of epoch milliseconds `ms` shifted by `offMin` minutes. -/
structure Parts where
  year : Int
  month : Nat
  day : Nat
  weekday : Nat
  hour : Nat
  minute : Nat
  second : Nat
  milli : Nat

def parts (ms : Int) (offMin : Int) : Parts :=
  let t := ms + offMin * 60000
  let days := t / 86400000      -- Int division rounds towards -∞ (Int.div is `/` = `Int.ediv`)
  let msOfDay := (t - days * 86400000).toNat
  let (y, m, d) := civilFromDays days
  { year := y, month := m, day := d,
    weekday := ((days + 4) % 7).toNat,
    hour := msOfDay / 3600000, minute := (msOfDay / 60000) % 60,
    second := (msOfDay / 1000) % 60, milli := msOfDay % 1000 }

/-- `Date.prototype.toString()` in a time zone with fixed offset `offMin` and
    name `tzName`, e.g. "Wed Nov 18 2026 12:00:00 GMT+0000 (Coordinated Universal Time)".
    `NaN` prints as "Invalid Date". -/
def toString (x : JsNum) (offMin : Int) (tzName : String) : String :=
  match timeClip x with
  | .nan => "Invalid Date"
  | .fin q =>
    let p := parts q.floor offMin
    let sign := if offMin < 0 then "-" else "+"
    let a := offMin.natAbs
    weekdays[p.weekday]! ++ " " ++ months[p.month - 1]! ++ " " ++ pad 2 p.day ++ " " ++
      (if p.year < 0 then "-" ++ pad 6 p.year.natAbs else pad 4 p.year.toNat) ++ " " ++
      pad 2 p.hour ++ ":" ++ pad 2 p.minute ++ ":" ++ pad 2 p.second ++
      " GMT" ++ sign ++ pad 2 (a / 60) ++ pad 2 (a % 60) ++ " (" ++ tzName ++ ")"

/-- `Date.prototype.toISOString()` (what `JSON.stringify` prints for a `Date`). -/
def toISOString (ms : Int) : String :=
  let p := parts ms 0
  (if p.year < 0 then "-" ++ pad 6 p.year.natAbs else if p.year > 9999 then "+" ++ pad 6 p.year.toNat else pad 4 p.year.toNat) ++
    "-" ++ pad 2 p.month ++ "-" ++ pad 2 p.day ++ "T" ++ pad 2 p.hour ++ ":" ++ pad 2 p.minute ++ ":" ++
    pad 2 p.second ++ "." ++ pad 3 p.milli ++ "Z"

/-- `date.getMinutes()` in local time. -/
def getMinutes (ms : Int) (offMin : Int) : Nat := (parts ms offMin).minute

/-- `date.getHours()` in local time. -/
def getHours (ms : Int) (offMin : Int) : Nat := (parts ms offMin).hour

end LeanAID.DateFmt
