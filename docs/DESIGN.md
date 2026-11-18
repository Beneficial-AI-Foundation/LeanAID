# Design

## Layout

| path | contents | may use |
|---|---|---|
| `LeanAID/Core/` | the transcription of oref0, pure functions | Lean core only |
| `LeanAID/Spec/` | the definition of valid input | Lean core |
| `LeanAID/Proofs/` | theorems about the core | Lean core (no Mathlib needed so far) |
| `LeanAID/Conformance/` | oref0's test calls as Lean data, checked by `native_decide` | Lean core |
| `App/` | the `aid-lean` shell: JSON, files, clock | Lean core |

`scripts/check.sh` enforces: no `sorry` anywhere; no `partial`, `unsafe`, `@[extern]`,
`implemented_by`, `Float` or Mathlib in the core; `native_decide` only in
`LeanAID/Conformance`; no `axiom` declarations; headline theorems depend only on
`propext`, `Classical.choice`, `Quot.sound`.

## Numbers

**Decision: exact rationals, plus an explicit NaN.** The core computes with

```lean
inductive JsNum | nan | fin (q : Rat)
```

Why rationals rather than fixed-point integers:

- oref0 divides constantly (ISF, carb ratio, autosens ratio, `/60`, `/30`, `/24`). With
  fixed point every division needs a rounding rule that oref0 does not have, so
  outputs would drift from the original. With rationals every intermediate value is
  the exact real number the JavaScript double approximates.
- Rationals keep the proofs about order and rounding simple: Lean core's `Rat` has
  the ordered-field lemmas and `Rat.floor` lemmas we need, and `grind` closes linear
  goals over `Rat`.
- Kernel evaluation (`decide +kernel`) works on concrete rationals, so concrete
  counterexamples are proved without `native_decide`.

Why an explicit NaN: oref0 reads missing fields as `undefined`, which becomes `NaN` in
arithmetic, and its own tests depend on it (missing glucose `date` disables the
staleness check; missing `lastCarbTime` makes `remainingCATime` NaN; missing
`carb_ratio` gives `CR: NaN`). Comparisons with NaN are false, `Math.min`/`max`
propagate it, and `!==` distinguishes `undefined` from `NaN`; all of this is modelled
(`LeanAID/Core/JsNum.lean`, `Option.js`, `optSne`).

JavaScript rounding is implemented exactly on the rational value:
`Math.round(x) = ⌊x + 1/2⌋`, oref0's `round(x, d)`, `round_basal`, `toFixed` (ties away
from zero on the exact value), `Math.floor`. `Number → String` is exact for every
terminating decimal (all values oref0 prints after rounding).

### Known differences from JavaScript (outside or at the edge of the valid domain)

| id | difference | consequence |
|---|---|---|
| D1 | `x / 0` is `NaN` here, `±Infinity` in JavaScript | none for valid input (no division by zero there) |
| D2 | doubles round every operation; we do not | at an exact rounding tie oref0 may round down where we round up. Seen in 2 of 51 IOB test calls (activity 0.00125 → 0.0013 here, 0.0012 in oref0), never in determine-basal tests. A tie in an intermediate value can change a later decision, so output differences are *not* limited to one rounding unit (FINDINGS F-13: one extra 0.05 U temp bolus; different issued rates in difftest). Measured by differential testing (M10). |
| D3 | `-0` is not modelled | unobservable in outputs (`-0` prints as `0`) |
| D4 | JSON `null` is read as `undefined` | in JavaScript `null` is 0 in arithmetic; only matters for invalid input |
| D5 | `Math.exp` is a rational approximation (`Core/Exp.lean`) | differences beyond the 15th digit; rounded away by oref0's `round(…,3/4)` except at ties |
| D6 | non-terminating values print with 16 significant digits | JavaScript prints the shortest round-trip form; only seen in reason strings, never in the numeric fields we compare |
| D7 | local time uses a fixed UTC offset | daylight-saving transitions inside one IOB window are not modelled |

## Time

`determine_basal` reads the clock (`new Date()`) when `currentTime` is not given. Here the
current time is always an input (`Clock.now`, milliseconds), together with the local
time-zone offset and name that JavaScript would use for `getMinutes()` and
`Date.prototype.toString()`. The shell supplies them.

## Transcription structure

`determine_basal` (1062 lines of JavaScript in one function) is split into
`dbPrelude` (lines 128–423, a chain of stage functions, one per early return),
`dbPredict` (428–903, predictions) and `dbDose` (905–1188, the decision). Smaller
pieces were named to keep proofs tractable (`setTempBasal`'s `keepRunning`,
`smbLowTemp`, `highTempSet`, `capInsulinReq`, …). Every such refactor was re-checked
against oref0's outputs by the conformance suite; the SMB pieces, which no oref0 test
reaches, are checked by differential testing.

## Valid input

Defined in Lean as `LeanAID.ValidInput` (`LeanAID/Spec/Valid.lean`). The safety
theorems assume exactly this and nothing else:

| id | condition | justification |
|---|---|---|
| V0 | a profile is given | without one oref0 returns an error (and H5b proves that) |
| V1 | `current_basal` is a number > 0 | a pump's scheduled basal; 0 is rejected by oref0's own profile code ("current basal of 0") |
| V2 | `max_basal` is a number ≥ `current_basal` | a maximum below the scheduled rate is a configuration error; oref0-get-profile derives it from pump settings |
| V3 | `max_daily_basal` is a number ≥ `current_basal` | by definition it is the largest scheduled rate |
| V4 | safety multipliers, when set to numbers, are ≥ 1 | a multiplier below 1 would make the scheduled basal itself "unsafe"; oref0 documents defaults 3 and 4 |
| V5 | `autosens_max` is a number > 0 with at most two decimals, and `current_basal × autosens_max ≤ maxSafeBasal` | the sensitivity-adjusted basal must itself be allowed; FINDINGS F-05 shows what happens otherwise |
| V6 | `max_iob` is a number ≥ 0 | the user's IOB ceiling |
| V7 | `bolus_increment`, when set to a number, is > 0 | a pump increment |
| V8 | `sens` (ISF) is a number > 0 | a correction factor |
| V9 | the autosens ratio, when autosens data is given, is a number in (0, `autosens_max`] | autosens clamps its ratio to `[autosens_min, autosens_max]` |

Glucose, deltas, IOB, meal data, current temp and clock are *not* constrained: the
theorems hold for any values, including missing and NaN ones (that is how H5 can
talk about bad data). Where a theorem needs more (e.g. H4 needs IOB to be a number at
least `max_iob`), the extra condition is a hypothesis of that theorem.

## Exponential insulin curve

`Core/Exp.lean`: `exp(x)` for `x ≤ 0` by halving to `|y| ≤ 1/2`, a degree-30 Taylor
polynomial, and squaring, truncating to a 2⁻¹²⁸ grid after each step. The error bound
(< 10⁻³⁵ for `|x| ≤ 128`) is argued in the file header; its proof against Mathlib's
`Real.exp` is planned for M8 and has not been done. No safety theorem depends on it.
