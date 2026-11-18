/-
  LeanAID.Core.JsonOut — render a `Result` exactly as `JSON.stringify(rT)` does in
  `bin/oref0-determine-basal.js`: same keys, same order, same number formatting,
  `NaN` as `null`, `undefined` fields omitted, `Date` as an ISO string.
-/
import LeanAID.Core.Types
import LeanAID.Core.DateFmt

namespace LeanAID.JsonOut

/-- JSON string literal (JSON.stringify escaping). -/
def str (s : String) : String :=
  let esc := s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | '\x08' => "\\b"
      | '\x0c' => "\\f"
      | c => if c.toNat < 0x20 then
          let h := Nat.toDigits 16 c.toNat
          "\\u" ++ String.ofList (List.replicate (4 - h.length) '0') ++ String.ofList h
        else c.toString
  "\"" ++ esc ++ "\""

/-- A JSON number; `NaN` is `null` in JSON. -/
def num : JsNum → String
  | .nan => "null"
  | x => JsFmt.numToString x

def numOrStr : NumOrStr → String
  | .num x => num x
  | .str s => str s

def list (xs : List JsNum) : String := "[" ++ ",".intercalate (xs.map num) ++ "]"

def predBGs (p : PredBGs) : String :=
  let fields : List (String × Option String) :=
    [("IOB", some (list p.IOB)), ("ZT", some (list p.ZT)), ("COB", p.COB.map list), ("UAM", p.UAM.map list)]
  obj fields
where
  obj (fs : List (String × Option String)) : String :=
    "{" ++ ",".intercalate (fs.filterMap fun (k, v) => v.map fun v => str k ++ ":" ++ v) ++ "}"

def obj (fs : List (String × Option String)) : String :=
  "{" ++ ",".intercalate (fs.filterMap fun (k, v) => v.map fun v => str k ++ ":" ++ v) ++ "}"

def reservoir : Reservoir → Option String
  | .undef => none
  | .null => some "null"
  | .str s => some (str s)

/-- `JSON.stringify(rT)`. -/
def result (r : Result) : String :=
  let rateDur : List (String × Option String) :=
    if r.rateFirst then [("rate", r.rate.map num), ("duration", r.duration.map num)]
    else [("duration", r.duration.map num), ("rate", r.rate.map num)]
  match r.shape with
  | .error => obj [("temp", r.temp.map str), ("deliverAt", r.deliverAt.map (str ∘ DateFmt.toISOString)),
                    ("error", r.error.map str)]
  | .cgm => obj ([("reason", r.reason.map str), ("deliverAt", r.deliverAt.map (str ∘ DateFmt.toISOString)),
                  ("temp", r.temp.map str)] ++ rateDur)
  | .lastTemp => obj ([("temp", r.temp.map str), ("deliverAt", r.deliverAt.map (str ∘ DateFmt.toISOString)),
                       ("reason", r.reason.map str)] ++ rateDur)
  | .main => obj ([
      ("temp", r.temp.map str), ("bg", r.bg.map num), ("tick", r.tick.map numOrStr),
      ("eventualBG", r.eventualBG.map num), ("insulinReq", r.insulinReq.map num),
      ("reservoir", reservoir r.reservoir), ("deliverAt", r.deliverAt.map (str ∘ DateFmt.toISOString)),
      ("sensitivityRatio", r.sensitivityRatio.map num), ("predBGs", r.predBGs.map predBGs),
      ("COB", r.COB.map num), ("IOB", r.IOB.map num), ("BGI", r.BGI.map numOrStr),
      ("deviation", r.deviation.map numOrStr), ("ISF", r.ISF.map numOrStr), ("CR", r.CR.map num),
      ("target_bg", r.target_bg.map numOrStr), ("reason", r.reason.map str),
      ("carbsReq", r.carbsReq.map num), ("units", r.units.map num)] ++ rateDur)

end LeanAID.JsonOut
