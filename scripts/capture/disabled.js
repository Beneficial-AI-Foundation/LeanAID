// Replays the inputs of the determine-basal tests that are disabled (commented
// out) in oref0's test file, so that Lean and oref0 can be compared on them.
// Their assertions are NOT used: the oref0 authors disabled them.
// Inputs are copied verbatim from vendor/oref0/tests/determine-basal.test.js
// (line numbers in the ids file docs/tests-inventory.json). Shared defaults are
// those at the top of that file (no earlier test mutates them before line 655).
// Run: TZ=UTC node -r ./fixclock.js disabled.js  (from scripts/capture)
'use strict';
var path = require('path');
var fs = require('fs');
var ROOT = path.resolve(__dirname, '../../vendor/oref0');
var determine_basal = require(path.join(ROOT, 'lib/determine-basal/determine-basal'));
var tempBasalFunctions = require(path.join(ROOT, 'lib/basal-set-temp'));

var glucose_status = {"delta":0,"glucose":115,"long_avgdelta":1.1,"short_avgdelta":0};
var currenttemp = {"duration":0,"rate":0,"temp":"absolute"};
var iob_data = {"iob":0,"activity":0,"bolussnooze":0};
var autosens = {"ratio":1.0};
var profile = {"max_iob":2.5,"dia":3,"type":"current","current_basal":0.9,"max_daily_basal":1.3,"max_basal":3.5,"max_bg":120,"min_bg":110,"sens":40,"carb_ratio":10};
var meal_data = {"carbs":50,"nsCarbs":50,"bwCarbs":0,"journalCarbs":0,"mealCOB":0,"currentDeviation":0,"maxDeviation":0,"minDeviation":0,"slopeFromMaxDeviation":0,"slopeFromMinDeviation":0,"allDeviations":[0,0,0,0,0],"bwFound":false};

function c(o) { return structuredClone(o); }  // keeps NaN (DB-49 passes sens: NaN)
var cases = [
  ['DB-07', [glucose_status, {"duration":30,"rate":0,"temp":"absolute"}, iob_data, profile, autosens, meal_data]],
  ['DB-11', [{"delta":5,"glucose":75,"long_avgdelta":5,"short_avgdelta":5}, currenttemp, {"iob":-1,"activity":-0.01,"bolussnooze":0}, profile, autosens, meal_data]],
  ['DB-12', [{"delta":4,"glucose":75,"long_avgdelta":-2,"short_avgdelta":-2}, currenttemp, iob_data, profile, autosens, meal_data]],
  ['DB-15', [{"delta":5,"glucose":75,"long_avgdelta":5,"short_avgdelta":5}, {"duration":20,"rate":2,"temp":"absolute"}, {"iob":-1,"activity":-0.01,"bolussnooze":0}, profile, autosens, meal_data]],
  ['DB-16', [{"delta":5,"glucose":75,"long_avgdelta":5,"short_avgdelta":5}, {"duration":20,"rate":0,"temp":"absolute"}, {"iob":-1,"activity":-0.01,"bolussnooze":0}, profile, autosens, meal_data]],
  ['DB-30', [{"delta":-1,"glucose":110,"long_avgdelta":-1,"short_avgdelta":-1}, {"duration":20,"rate":0.25,"temp":"absolute"}, iob_data, profile, autosens, meal_data]],
  ['DB-41', [{"delta":-6,"glucose":300,"long_avgdelta":-5,"short_avgdelta":-5}, currenttemp, {"iob":0.5,"activity":0.005,"bolussnooze":0}, profile, autosens, meal_data]],
  ['DB-42', [{"delta":-6,"glucose":300,"long_avgdelta":-5,"short_avgdelta":-5}, {"duration":30,"rate":3.5,"temp":"absolute"}, {"iob":0.5,"activity":0.005,"bolussnooze":0}, profile, autosens, meal_data]],
  ['DB-48', [{glucose:100}, undefined, {"activity":0}, {"current_basal":0.0, "max_bg":100,"min_bg":110}, autosens, meal_data]],
  ['DB-49', [{glucose:100}, undefined, {"activity":0, "iob":0,"bolussnooze":0}, {"current_basal":0.0, "sens":NaN}, autosens, meal_data]],
  ['DB-50', [{"delta":1,"glucose":80,"long_avgdelta":1,"short_avgdelta":1}, currenttemp, {"iob":0.5,"activity":-0.01,"bolussnooze":1,"basaliob":-0.5}, profile, autosens, {"carbs":20,"boluses":1, "mealCOB":20}]],
  ['DB-52', [{"delta":-1,"glucose":80,"long_avgdelta":1,"short_avgdelta":1}, {"duration":20,"rate":2,"temp":"absolute"}, {"iob":0.5,"activity":-0.01,"bolussnooze":1,"basaliob":-0.5}, profile, autosens, meal_data]],
  ['DB-53', [{"delta":1,"glucose":80,"long_avgdelta":1,"short_avgdelta":1}, {"duration":20,"rate":0,"temp":"absolute"}, {"iob":0.5,"activity":-0.01,"bolussnooze":1,"basaliob":-0.5}, profile, autosens, meal_data]],
  ['DB-54', [{"delta":10,"glucose":120,"avgdelta":10}, currenttemp, {"iob":0.4,"activity":0,"bolussnooze":0.7,"basaliob":-0.3}, profile, autosens, {"carbs":20,"boluses":1, "mealCOB":20}]],
  ['DB-55', [{"delta":3,"glucose":150,"avgdelta":5}, {"duration":10,"rate":2,"temp":"absolute"}, {"iob":0.5,"activity":0.01,"bolussnooze":0.6,"basaliob":-0.1}, profile, autosens, {"carbs":20,"boluses":1, "mealCOB":20}]],
  ['DB-56', [{"delta":-3,"glucose":160,"avgdelta":0}, {"duration":30,"rate":2.5,"temp":"absolute"}, {"iob":0.9,"activity":0.02,"bolussnooze":0.5,"basaliob":0.4}, profile, autosens, {"carbs":20,"boluses":1, "mealCOB":20}]],
  ['DB-57', [{"delta":4,"glucose":120,"avgdelta":4}, currenttemp, {"iob":6,"activity":0,"bolussnooze":6,"basaliob":0,"hightempinsulin":0}, profile, autosens, {"carbs":120,"boluses":6, "mealCOB":120}]],
  ['DB-58', [{"delta":4,"glucose":140,"avgdelta":4}, currenttemp, {"iob":6.5,"activity":0.01,"bolussnooze":5.5,"basaliob":1,"hightempinsulin":1}, profile, autosens, {"carbs":120,"boluses":6, "mealCOB":100}]],
  ['DB-59', [{"delta":4,"glucose":160,"avgdelta":4}, currenttemp, {"iob":7.0,"activity":0.02,"bolussnooze":5.0,"basaliob":2,"hightempinsulin":2}, profile, autosens, {"carbs":120,"boluses":6, "mealCOB":80}]],
  ['DB-60', [{"delta":1,"glucose":160,"avgdelta":1}, currenttemp, {"iob":7.0,"activity":0.02,"bolussnooze":5.0,"basaliob":2}, profile, autosens, {"carbs":120,"boluses":6, "mealCOB":80}]],
  ['DB-61', [{"delta":-1,"glucose":160,"avgdelta":-1}, {"duration":15,"rate":2.5,"temp":"absolute"}, {"iob":7.0,"activity":0.03,"bolussnooze":5.0,"basaliob":2}, profile, autosens, {"carbs":120,"boluses":6, "mealCOB":80}]],
  ['DB-62', [{"delta":1,"glucose":160,"avgdelta":1}, currenttemp, {"iob":7.0,"activity":0.02,"bolussnooze":4.0,"basaliob":3}, profile, autosens, {"carbs":120,"boluses":11, "mealCOB":80}]],
  ['DB-63', [{"delta":3,"glucose":200,"avgdelta":8.667}, {"duration":3,"rate":3.5,"temp":"absolute"}, {"iob":2.701,"activity":0.0107,"bolussnooze":0.866,"basaliob":1.013,"netbasalinsulin":1.1,"hightempinsulin":1.8}, profile, autosens, {"carbs":15,"boluses":2, "mealCOB":15}]],
];

function clone(x) {
  if (x === undefined) return { __undefined: true };
  return JSON.parse(JSON.stringify(x, function (k, v) {
    if (v === undefined) return { __undefined: true };
    if (typeof v === 'number' && !isFinite(v)) return { __number: String(v) };
    return v;
  }));
}
var records = cases.map(function (cs, k) {
  var args = cs[1].map(function (a) { return a === undefined ? undefined : c(a); });
  var cargs = args.map(clone);
  var result = null, threw = null;
  try { result = determine_basal.apply(null, args.concat([tempBasalFunctions])); }
  catch (e) { threw = String(e); }
  return { seq: k, fn: 'determine_basal', test: cs[0] + ' (disabled upstream)', id: cs[0], args: cargs,
           result: threw ? null : clone(result), threw: threw };
});
fs.writeFileSync(path.join(__dirname, 'out/determine-basal-disabled.json'), JSON.stringify(records, null, 1));
console.log(records.length + ' disabled determine-basal cases; ' + records.filter(function (r) { return r.threw; }).length + ' threw');
