// F-23 probe: oref0 0.7.1 reaches a NaN minGuardBG with bg < threshold.
//   TZ=UTC node scripts/probe-lgs-nan.js [path to oref0, default vendor/oref0]
// Cases A and B give {"rate":0,"duration":null}: a zero temp with a NaN duration.
'use strict';
var path = require('path');
var O = process.argv[2] || path.resolve(__dirname, '../vendor/oref0');
var getLastGlucose = require(path.join(O, 'lib/glucose-get-last'));
var determine_basal = require(path.join(O, 'lib/determine-basal/determine-basal'));
var tbf = require(path.join(O, 'lib/basal-set-temp'));
var now = Date.UTC(2026, 10, 18, 3, 0, 0);
function run(label, meal, bgs, enableUAM) {
  var glucose = bgs.map(function (g, i) { return { date: now - i * 300000, glucose: g }; });
  var iob = [];
  for (var k = 0; k < 48; k++) iob.push({ iob: 0, activity: 0, iobWithZeroTemp: { iob: 0, activity: 0 } });
  iob[0].lastBolusTime = now - 3 * 3600000;
  iob[0].lastTemp = { date: now - 20 * 60000, rate: 1, duration: 30 };
  var profile = { current_basal: 1, max_daily_basal: 1, max_basal: 3, max_iob: 1, min_bg: 100, max_bg: 100,
    sens: 50, carb_ratio: 10, dia: 3, type: 'current', maxCOB: 120, enableUAM: enableUAM };
  var saved = console.error; var logs = []; console.error = function () { logs.push([].join.call(arguments, ' ')); };
  var rT = determine_basal(getLastGlucose(glucose), { duration: 0, rate: 0, temp: 'absolute' }, iob, profile,
    null, meal, tbf, false, null, new Date(now));
  console.error = saved;
  console.log(label, JSON.stringify({ bg: rT.bg, rate: rT.rate, duration: rT.duration, units: rT.units,
    reason: rT.reason }));
  console.log('  JSON as sent:', JSON.stringify({ rate: rT.rate, duration: rT.duration }));
}
var rising = [60, 57, 54, 51, 48, 45, 42, 40, 40, 40];
var falling = [60, 63, 66, 69, 72, 75, 78, 81, 84, 87];
var mealBase = { nsCarbs: 0, bwCarbs: 0, journalCarbs: 0, currentDeviation: 0, maxDeviation: 0,
  minDeviation: 0, slopeFromMaxDeviation: 0, slopeFromMinDeviation: 0, allDeviations: [0, 0, 0] };
function m(extra) { return Object.assign({}, mealBase, extra); }
run('A rising, COB 20, carbs missing, UAM on ', m({ mealCOB: 20 }), rising, true);
run('B rising, COB 20, carbs 0, UAM on      ', m({ mealCOB: 20, carbs: 0 }), rising, true);
run('C rising, COB 20, carbs 30, UAM on     ', m({ mealCOB: 20, carbs: 30, lastCarbTime: now - 3600000 }), rising, true);
run('D falling, COB 20, carbs missing, UAM on', m({ mealCOB: 20 }), falling, true);
run('E rising, COB 20, carbs missing, UAM off', m({ mealCOB: 20 }), rising, false);
