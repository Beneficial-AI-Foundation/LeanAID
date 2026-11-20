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

**Decision: IEEE-754 binary64 arithmetic, computed exactly on rationals, plus an
explicit NaN.** The core computes with

```lean
inductive JsNum | nan | fin (q : Rat)
```

where every finite value is held as an exact rational, and every arithmetic operation is
JavaScript's: the exact result of `+ − × ÷`, rounded to the nearest double, ties to even
(`Binary64.rd`, `LeanAID/Core/Binary64.lean`). Decimal literals denote the nearest double,
as in JavaScript, and the JSON reader rounds every input number to a double. No `Float`
is used: `rd` is defined with integer arithmetic (`Nat.log2`, `Rat.floor`), so the kernel
can evaluate it and the proofs can reason about it.

Compiled code runs a faster but equal version: `rdImpl` (`Core/Binary64Impl.lean`)
computes the same value from numerator and denominator with natural numbers only (bit
lengths, one product, one division), and the theorem `rd_eq_rdImpl : rd = rdImpl` is a
`@[csimp]` lemma, so the compiler substitutes it wherever `rd` is used (the binary and
`native_decide`), while the kernel and the proofs see `rd`. Likewise `Exp.jsExp` is
replaced by a table lookup (`jsExp_eq_jsExpFast`, below). Both were added for the
closed-loop simulation (M11), which was about 10x too slow with the rational `rd`; no
trusted step is added, since each replacement is a proved equality.

History: until the second review the core used exact rational arithmetic (no
rounding). That agreed with oref0 byte for byte on 83.1% of 100,000 random inputs and
differed in the issued rate in 82 (FINDINGS F-13–F-15), because a rounding tie in an
intermediate value can flip a later decision. With binary64 rounding, **100,000 of
100,000** outputs are byte-identical (`docs/difftest.json`, seed 7), and all 148 calls of
oref0's own tests agree exactly, including the 2 IOB values that differed before.

What is modelled exactly on the double values:

- `+ − × ÷` (`JsNum.add/sub/mul/div`): `rd` of the exact result. Subnormals are included.
- `Math.round(x) = ⌊x + 1/2⌋` (exact on a double, as ECMAScript defines it), `Math.floor`,
  `Math.min/max`, comparisons.
- oref0's `round(x, d) = Math.round(x · 10^d) / 10^d`, with the multiplication and
  division rounded; `round_basal` likewise.
- `toFixed` on the double value, and `Number → String` as ECMAScript's shortest
  round-trip form (`JsFmt.numToString`, exponent form outside `1e-6 ≤ |x| < 1e21`).
- `Math.exp`: see D5.

What the proofs use about `rd` (`LeanAID/Proofs/Binary64.lean`, no `sorry`): it is
monotone, odd, idempotent, exact on integers `|n| ≤ 2^53` and on `N · 2^E` grids, and
`|rd x − x| ≤ |x|·2^-53 + 2^-1075`. Monotonicity carries most safety theorems through
unchanged; where a property holds only up to rounding, the theorem now says so
(FINDINGS F-16 lists every changed statement).

Why an explicit NaN: oref0 reads missing fields as `undefined`, which becomes `NaN` in
arithmetic, and its own tests depend on it (missing glucose `date` disables the
staleness check; missing `lastCarbTime` makes `remainingCATime` NaN; missing
`carb_ratio` gives `CR: NaN`). Comparisons with NaN are false, `Math.min`/`max`
propagate it, and `!==` distinguishes `undefined` from `NaN`; all of this is modelled
(`LeanAID/Core/JsNum.lean`, `Option.js`, `optSne`).

### Known differences from JavaScript (outside or at the edge of the valid domain)

| id | difference | consequence |
|---|---|---|
| D1 | `x / 0` is `NaN` here, `±Infinity` in JavaScript | **not** only outside the valid domain: a valid profile with meal data whose `lastCarbTime` is 2 h after the decision time divides by zero in the COB prediction, and aid-lean's `predBGs` and reason then differ from oref0's (FINDINGS F-17; the rate agreed in the one case found) |
| D2 | overflow to `±Infinity` is not modelled (values above ≈1.8·10³⁰⁸ keep growing) | none: oref0's values on valid input are far below |
| D3 | `-0` is not modelled | unobservable in outputs (`-0` prints as `0`) |
| D4 | JSON `null` is read as `undefined` | in JavaScript `null` is 0 in arithmetic; only matters for invalid input |
| D5 | `Math.exp` | ECMAScript leaves `Math.exp` implementation-approximated, and V8's is not correctly rounded. Ours computes `exp` to within 10⁻³⁵ (relative) of the true value (`Core/Exp.lean`, argued, not proved) and rounds that to the nearest double, so it is the correctly rounded result except within 10⁻³⁵ of a rounding midpoint. **Tolerance:** if V8's result is within 1 ulp of the true value (the documented accuracy of the fdlibm algorithm it uses; we did not verify V8's source), the two differ by at most 1 ulp of `exp(x)`. oref0 only uses `exp` in the exponential insulin curves and rounds IOB and activity to 3–4 decimals, so a 1-ulp difference shows only if it moves a value across a rounding tie. Observed: no difference in 148 test calls and 100,000 differential cases |
| D6 | (removed) printing: was 16 significant digits; now ECMAScript's shortest round-trip form | — |
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

`calcTempTreatments` (history.js lines 161-571) is split the same way, into
`collectSuspends`, `matchSuspends`, `scanRecords`, `trimTemps`, `splitStage` and
`tempBolusesOf`. The first transcription was one `Id.run do` block
with two `while` loops. Lean compiles a `while` loop to a definition that the kernel
does not unfold, and both loops carried all the mutable state of the block. So no fact
about the output of `Iob.generate` could be proved, and `decide` could not evaluate a
run. The run theorems need such facts: an accepted microbolus must reach the treatments
and `lastBolusTime` (`Legal.bolusSeen`, used by `p5_gap` and `p6_bolus`). Each loop now recurses on a fuel
bound that the JavaScript loop never reaches, so the results are the same. For the same
reason `sortByKey` is a structural insertion sort. `sortByKey_eq_merge` proves it equal to
`List.mergeSort`, and as a `@[csimp]` lemma it keeps the merge sort in compiled code.
After the change, `TZ=UTC node scripts/difftest/run.js 100000 7` gives 100,000 of
100,000 outputs identical to oref0.

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
| V5 | `autosens_max`, when it is a number, is > 0, is the double nearest `n/100` for an integer `0 ≤ n ≤ 2^40` (at most two decimals), and `current_basal × autosens_max ≤ maxSafeBasal` | the sensitivity-adjusted basal must itself be allowed (F-05); if `autosens_max` is missing, temp targets give a NaN ratio and no adjustment |
| V6 | `max_iob` is a number ≥ 0 | the user's IOB ceiling |
| V7 | `bolus_increment`, when set to a number, is > 0 | a pump increment |
| V8 | `sens` (ISF) is a number > 0 | a correction factor |
| V9 | the autosens ratio, when autosens data is given, is a number r > 0 with `current_basal × r ≤ maxSafeBasal` | the adjusted basal must be allowed; autosens itself keeps r within [autosens_min, autosens_max] |
| V10 | `current_basal` and `max_basal` are doubles, and `max_basal ≤ 2^30` U/h | needed by the double model (FINDINGS F-16): `rd(m · cb) ≥ cb` for `m ≥ 1` only if `cb` is a double, and `round_basal` is idempotent below 2^30. Every number read from JSON is a double, so V10 only excludes absurd `max_basal` values |

These are exactly the fields of `LeanAID.ValidInput` / `ValidProfile` (decided by
`validInputB`, proved sound by `validInputB_sound`).

Glucose, deltas, IOB, meal data, current temp and clock are *not* constrained: the
theorems hold for any values, including missing and NaN ones (that is how H5 can
talk about bad data). Rate theorems speak about *finite* issued rates: with valid
profile but inconsistent meal data oref0 can issue a NaN rate (F-06), which they do not
bound. Where a theorem needs more (e.g. H4 needs IOB to be a number at
least `max_iob`), the extra condition is a hypothesis of that theorem.

## Exponential insulin curve

`Core/Exp.lean`: `exp(x)` for `x ≤ 0` by halving to `|y| ≤ 1/2`, a degree-30 Taylor
polynomial, and squaring, truncating to a 2⁻¹²⁸ grid after each step, then rounding to
the nearest double (`jsExp`). The error bound (< 10⁻³⁵ for `|x| ≤ 128`) is argued in the
file header; its proof against Mathlib's `Real.exp` is planned for M8 and has not been
done. No safety theorem depends on it. The tolerance against JavaScript is D5.

Speed (M11). The Taylor polynomial is evaluated with integers, as one fraction
`Σ a^i b^(n-i) n!/i! / (b^n n!)` for `y = a/b` (`Exp.taylor`), instead of Horner's rule
on rationals (`Exp.taylorHorner`, kept as the reference). Both are exact, so they are
the same rational; the equality is not proved, and `taylor_eq_horner_samples`
(Conformance/Checks.lean) checks it on the 1,202 arguments the curves use with DIA 5 h.
`jsExpFast` looks `jsExp` up in a table of its own values at the arguments the curves
use for DIA 5–8 h and peaks 55/75 min; `jsExp_eq_jsExpFast` proves the two equal, and
as a `@[csimp]` lemma it makes compiled code use the table.

## What `aid-lean --safe` rejects

`aid-lean determine-basal … --safe` (not an oref0 option) refuses to produce a
suggestion, printing the reasons on stderr and exiting with code 2, exactly when one of
these holds (`App/Main.lean`, `determineBasalCmd`):

| check | rejects | why |
|---|---|---|
| `validInputB inp = false` | a profile violating V0–V8 or V10 (e.g. missing or non-numeric `current_basal`, `max_basal`, `max_daily_basal`, `max_iob`, `sens`; `max_basal` or `max_daily_basal` below `current_basal`; `max_basal` above 2^30; a safety multiplier below 1; `autosens_max` with more than two decimals or with `current_basal × autosens_max > maxSafeBasal`; a non-positive `bolus_increment`), or autosens data violating V9 (non-numeric or non-positive ratio, or `current_basal × ratio > maxSafeBasal`) | outside the domain of the safety theorems; F-12 (missing `max_basal` disables the clamp) |
| meal data with truthy `carbs` and no numeric `lastCarbTime` | carbs without a carb time | F-06 (NaN rate) |
| the glucose status has no finite `date` | CGM entries without `date`, `display_time` or `dateString` (or unparsable ones) | F-11 (staleness check skipped; maximum rate on an old reading) |

It does **not** reject: stale, noisy, flat or error-coded readings (oref0 handles these,
and H5a proves the result does not increase insulin); IOB data, current temp or meal data
that are otherwise odd (the theorems hold for any values, but a NaN rate is still
possible in ways not listed above); a wrong clock. `--safe` is part of the unverified
shell; `validInputB` is proved sound for `ValidInput` (`validInputB_sound`), the other two
checks are not proved.
