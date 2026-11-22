# Draft issue for openaps/oref0 (F-12), not sent

**Title:** No basal cap is applied when max_basal or max_daily_basal is missing (maxSafeBasal is NaN)

**Where:** `lib/basal-set-temp.js`, `getMaxSafeBasal` and `setTempBasal` (`master` = `dev`
lines 10-30). The same code is on every branch with commits after 0.7.1.

### What happens

`getMaxSafeBasal` returns `Math.min(profile.max_basal, 3 * profile.max_daily_basal,
4 * profile.current_basal)`. If any of these is missing or not a number, the result is `NaN`.
`setTempBasal` then tests `rate > maxSafeBasal`, which is always false for `NaN`, so the
requested rate is issued without any cap.

### Reproduction (from the repository root)

```
node -e 'var db=require("./lib/determine-basal/determine-basal"),t=require("./lib/basal-set-temp");console.error=function(){};process.stderr.write=function(){return true};var now=Date.now();function prof(){return {max_iob:2.5,dia:3,type:"current",current_basal:0.9,max_daily_basal:1.3,max_basal:3.5,max_bg:120,min_bg:110,sens:40,carb_ratio:10}}var meal={carbs:0,mealCOB:0,allDeviations:[0,0,0,0,0]};function run(p){var r=db({glucose:300,delta:10,short_avgdelta:10,long_avgdelta:10,date:now},{duration:0,rate:0,temp:"absolute"},{iob:0,activity:0,bolussnooze:0},p,{ratio:1},meal,t,false,null,new Date(now));return r.rate+" U/h for "+r.duration+" min (maxSafeBasal "+t.getMaxSafeBasal(p)+")"}var a=prof();console.log("complete profile:   "+run(a));var b=prof();delete b.max_basal;console.log("without max_basal:  "+run(b))'
→ complete profile:   3.5 U/h for 30 min (maxSafeBasal 3.5)
→ without max_basal:  5.9 U/h for 30 min (maxSafeBasal NaN)
```

Without `max_daily_basal`, or without both, the result is the same: 5.9 U/h, 6.6 × the
scheduled basal of 0.9 U/h.

### Why it matters (our estimate: low on an oref0 rig; the effect is large when it happens)

On a rig, `max_basal` is the pump's `maxBasal` from `settings/settings.json` (a pump read), so
it is normally present, and the Medtronic pump enforces its own maximum. But nothing in oref0
rejects a profile without it:

- `valid_settings` in `bin/oref0-pump-loop.sh` checks only `maxBolus`;
- the `max_basal < 0.1` check in `lib/profile/index.js` is false for `undefined`;
- a non-numeric basal rate makes `max_daily_basal` NaN, which passes the `=== 0` check.

Code that builds the profile itself and calls `lib/` (as several apps derived from oref0 do)
gets no cap at all from oref0 if a value is lost. In a closed-loop simulation of this case (our
virtual-patient harness), rates reached up to 9.8 × the configured `max_basal`.

### Suggested fix

If `maxSafeBasal` is not a finite positive number, do not raise the rate. Cap at the scheduled
basal (which also replaces a running high temp with a neutral one) and report the error; if
`current_basal` is also invalid, cancel the temp:

```diff
     var maxSafeBasal = tempBasalFunctions.getMaxSafeBasal(profile);
+    if (!(typeof maxSafeBasal === 'number' && isFinite(maxSafeBasal) && maxSafeBasal > 0)) {
+        // max_basal, max_daily_basal or current_basal is missing or invalid, so there is no
+        // safety limit: never go above the scheduled basal (low temps are still allowed)
+        var cb = profile.current_basal;
+        reason(rT, 'Error: maxSafeBasal ' + maxSafeBasal + ' is not a positive number; check max_basal, max_daily_basal and current_basal');
+        if (!(typeof cb === 'number' && isFinite(cb) && cb > 0)) {
+            reason(rT, 'canceling temp');
+            rT.duration = 0;
+            rT.rate = 0;
+            return rT;
+        }
+        maxSafeBasal = cb;
+    }
```

(Full patch: `F-12.patch`.) With it, the reproduction gives 0.9 U/h (the scheduled basal), and
the complete profile is unchanged (3.5 U/h). A check on `max_basal` in `lib/profile/index.js`
(`!(profile.max_basal >= 0.1)` instead of `profile.max_basal < 0.1`) would also catch the
missing value earlier (not tested). We have not yet run the repository's mocha suite on the patched copy.

---
Found while transcribing oref0 into Lean 4 (LeanAID, Beneficial AI Foundation).
