# Draft issue for openaps/oref0 (F-11), not sent

**Title:** determine-basal skips the BG staleness check when glucose_status has no valid date

**Where:** `lib/determine-basal/determine-basal.js`, the BG age check (`master` lines 150, 187 and
198; `dev` lines 150, 195, 206 and 209). The same code is on every branch with commits
after 0.7.1.

### What happens

`minAgo = round((systemTime - new Date(glucose_status.date)) / 60 / 1000, 1)`. If
`glucose_status.date` is missing or not a valid date, `minAgo` is `NaN`, and the checks
`minAgo > 12 || minAgo < -5` are both false. The reading is then treated as fresh and
determine-basal goes on to dose from it.

### Reproduction (from the repository root)

```
node -e 'var db=require("./lib/determine-basal/determine-basal"),t=require("./lib/basal-set-temp");console.error=function(){};process.stderr.write=function(){return true};var now=Date.now();var p={max_iob:2.5,dia:3,type:"current",current_basal:0.9,max_daily_basal:1.3,max_basal:3.5,max_bg:120,min_bg:110,sens:40,carb_ratio:10};var meal={carbs:0,mealCOB:0,allDeviations:[0,0,0,0,0]};function run(gs){var r=db(gs,{duration:0,rate:0,temp:"absolute"},{iob:0,activity:0,bolussnooze:0},p,{ratio:1},meal,t,false,null,new Date(now));return r.rate===undefined?"no temp":r.rate+" U/h for "+r.duration+" min"}var g={glucose:250,delta:5,short_avgdelta:5,long_avgdelta:5};console.log("no date:          "+run(Object.assign({},g)));console.log("dated 60 min ago: "+run(Object.assign({date:now-3600000},g)))'
→ no date:          3.5 U/h for 30 min
→ dated 60 min ago: no temp
```

### Why it matters (our estimate: low on an oref0 rig; higher for code that reuses lib/)

On a rig this is masked. `lib/glucose-get-last.js` computes every delta from the newest reading's
date, so an undated newest reading gives deltas of 0. The flat-CGM check (`tooflat`) then
refuses to dose ("CGM data is unchanged", no temp). We confirmed this through the real
`glucose-get-last.js`. It depends on that second check, though, and some derived code has
removed the flat-CGM early exit. Through their own `glucose-get-last`, nightscout/trio-oref and
the bundles of iAPS (which also checks only `minAgo > 12`) dose 3.5 U/h on the same undated
reading. Both apps currently guarantee dates on the Swift side, so we know of no app where this
can happen today. The check itself should still fail closed.

### Suggested fix

Write the check so that a non-numeric age counts as stale:

```diff
-    if (minAgo > 12 || minAgo < -5) { // Dexcom data is too old, or way in the future
+    if (!(minAgo <= 12 && minAgo >= -5)) { // Dexcom data is too old, or way in the future
 ...
-    if ((minAgo > 12 || minAgo < -5) && lastTempAge < 10) {
+    if (!(minAgo <= 12 && minAgo >= -5) && lastTempAge < 10) {
 ...
-    } else if (bg <= 10 || bg === 38 || noise >= 3 || minAgo > 12 || minAgo < -5 || tooflat ) {
+    } else if (bg <= 10 || bg === 38 || noise >= 3 || !(minAgo <= 12 && minAgo >= -5) || tooflat ) {
```

The second hunk (`lastTempAge`) exists on `dev` only; `master` has the other two checks, at lines
187 and 198, with `if (` instead of `} else if (` in the third. (Full patch against `dev`:
`F-11.patch`.) For any numeric `minAgo` this is the same condition; only `NaN` changes. With it, the undated reading above gives "BG data is too old", no temp. We have not
yet run the repository's mocha suite on the patched copy.

---
Found while transcribing oref0 into Lean 4 (LeanAID, Beneficial AI Foundation).
