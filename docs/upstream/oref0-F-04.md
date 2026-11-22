# Draft issue for openaps/oref0 (F-04), not sent

**Title:** setTempBasal can issue a rate slightly above maxSafeBasal after rounding

**Where:** `lib/basal-set-temp.js` (`setTempBasal`), with `lib/round-basal.js`. Checked on
`master` @ 88cf032 (0.7.1) and `dev` @ d219baf; the same code is on every branch with commits
after 0.7.1.

### What happens

`setTempBasal` first caps the requested rate at `maxSafeBasal`
(`min(max_basal, 3 × max_daily_basal, 4 × current_basal)`) and then rounds it to the pump's step
with `round_basal`, which rounds to the *nearest* step. When `maxSafeBasal` is not on the pump's
grid, the rounded rate can be above it.

### Reproduction (from the repository root)

```
node -e 'var t=require("./lib/basal-set-temp");console.log(t.setTempBasal(2,30,{current_basal:0.5,max_basal:0.83,max_daily_basal:1},{},{}))'
→ { duration: 30, rate: 0.85 }          (maxSafeBasal is 0.83)
```

A case closer to real use: with autotune, basal rates have three decimals. With `current_basal`
0.307, `max_basal` 3 and `max_daily_basal` 1.2, `maxSafeBasal` = 4 × 0.307 = 1.228, and a high
request is issued as **1.25 U/h**. The same happens end to end through `determine-basal` (the SMB
branch also pre-rounds `round_basal(maxSafeBasal)` before calling `setTempBasal`).

### Why it matters (our estimate: low)

The overshoot is at most half a pump step (≤ 0.025 U/h here), and on a Medtronic rig the pump's
own Max Basal setting still applies. But `maxSafeBasal` is documented as a hard ceiling, and it is
reachable in normal use: `max_basal` read from the pump is on the grid, but autotune basals
(0.001 U/h precision, `lib/autotune/index.js`) make `4 × current_basal` and `3 × max_daily_basal`
off-grid in about 40 % of cases, and on x23/x54 pumps `3 × max_daily_basal` can round up above
1 U/h (e.g. 3 × 0.375 = 1.125 → 1.15). Downstream projects that copy `lib/` inherit this. Two of
them already handle it: AndroidAPS floors to the pump step after its constraints, and Trio's
Swift port rounds down to the pump's supported rates.

### Suggested fix

After rounding, if the result exceeds `maxSafeBasal`, round `maxSafeBasal` *down* to the pump step:

```diff
--- a/lib/basal-set-temp.js
+++ b/lib/basal-set-temp.js
@@ -28,6 +28,11 @@
     var suggestedRate = round_basal(rate, profile);
+    // rounding to the nearest pump increment can go above maxSafeBasal when maxSafeBasal
+    // is not on the pump's grid (e.g. 0.83 -> 0.85): round down instead
+    if (suggestedRate > maxSafeBasal) {
+        suggestedRate = round_basal(maxSafeBasal, profile, 'down');
+    }
--- a/lib/round-basal.js
+++ b/lib/round-basal.js
-var round_basal = function round_basal(basal, profile) {
+var round_basal = function round_basal(basal, profile, direction) {
+
+    // direction 'down': round down to the pump increment (never above basal)
+    var r = (direction === 'down') ? function (x) { return Math.floor(x + 1e-9); } : Math.round;
 ...
-        rounded_basal = Math.round(basal * lowest_rate_scale) / lowest_rate_scale;
+        rounded_basal = r(basal * lowest_rate_scale) / lowest_rate_scale;
 (and the same for the * 20 and * 10 branches)
```

(Full patch: `F-04.patch`.) With it, the example above gives 0.80 U/h. We compared patched and
unpatched `setTempBasal` on 3,944,160 inputs (current basal 0.05–3.00, max_basal 0.05–10.00,
requests 0–12 U/h, both pump grids): the unpatched code exceeds `maxSafeBasal` in 526,342 of them,
the patched code in none, and the two differ in exactly those cases. We have not yet run the
repository's mocha suite on the patched copy.

---
Found while transcribing oref0 into Lean 4 (LeanAID, Beneficial AI Foundation). The Lean model
proves the bound that does hold (every issued rate ≤ `round_basal(maxSafeBasal)`, at most half a
step above `maxSafeBasal`) and the counterexample above.
