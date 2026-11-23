// F-22 probe: a basal schedule whose last entry (sorted by `i`) has rate 0.
//   TZ=UTC node scripts/probe-basal-zero.js [path to oref0, default vendor/oref0]
// basalLookup returns undefined at every time of day, profile generation keeps
// current_basal undefined (its check is `=== 0`), and determine_basal returns
// "Error: could not get current basal rate" with no rate.
'use strict';
var path = require('path');
var O = process.argv[2] || path.resolve(__dirname, '../vendor/oref0');
var basal = require(path.join(O, 'lib/profile/basal'));
var generate = require(path.join(O, 'lib/profile'));
var getLastGlucose = require(path.join(O, 'lib/glucose-get-last'));
var determine_basal = require(path.join(O, 'lib/determine-basal/determine-basal'));
var tbf = require(path.join(O, 'lib/basal-set-temp'));

var good = [{ i: 0, minutes: 0, start: '00:00:00', rate: 1 }, { i: 1, minutes: 360, start: '06:00:00', rate: 0.85 }];
var zeroLast = [{ i: 0, minutes: 0, start: '00:00:00', rate: 1 }, { i: 1, minutes: 360, start: '06:00:00', rate: 0 }];
var zeroFirst = [{ i: 0, minutes: 0, start: '00:00:00', rate: 0 }, { i: 1, minutes: 360, start: '06:00:00', rate: 1 }];

var quiet = function (f) {
  var saved = console.error; console.error = function () {};
  try { return f(); } finally { console.error = saved; }
};
var hours = [0, 3, 6, 12, 23];
[['good', good], ['zeroLast', zeroLast], ['zeroFirst', zeroFirst]].forEach(function (c) {
  var out = hours.map(function (h) {
    var v = quiet(function () { return basal.basalLookup(c[1], new Date(Date.UTC(2026, 10, 18, h, 30))); });
    return h + 'h:' + (v === undefined ? 'undefined' : v);
  });
  console.log('basalLookup', c[0], out.join(' '));
});

var now = Date.UTC(2026, 10, 18, 3, 0, 0);
function profileFor(basals) {
  var inputs = {
    settings: { insulin_action_curve: 3 },
    basals: JSON.parse(JSON.stringify(basals)),
    targets: { user_preferred_units: 'mg/dL', units: 'mg/dL',
      targets: [{ i: 0, start: '00:00:00', offset: 0, low: 100, high: 100, min_bg: 100, max_bg: 100 }] },
    isf: { units: 'mg/dL', sensitivities: [{ i: 0, start: '00:00:00', offset: 0, sensitivity: 50 }] },
    carbratio: { units: 'grams', schedule: [{ i: 0, start: '00:00:00', offset: 0, ratio: 10 }] },
    temptargets: [],
    max_iob: 1
  };
  var fr = { err: '', stdout: '', return_val: 0 };
  return quiet(function () { return generate(fr, inputs); });
}
[['good', good], ['zeroLast', zeroLast]].forEach(function (c) {
  var p = profileFor(c[1]);
  if (typeof p !== 'object') { console.log('profile', c[0], 'generation returned', p); return; }
  var glucose = [120, 120, 120, 120].map(function (g, i) { return { date: now - i * 300000, glucose: g }; });
  var iob = [{ iob: 0, activity: 0, lastBolusTime: now - 3 * 3600000, iobWithZeroTemp: { iob: 0, activity: 0 },
    lastTemp: { date: now - 60 * 60000, rate: 1, duration: 30 } }];
  var rT = quiet(function () {
    return determine_basal(getLastGlucose(glucose), { duration: 0, rate: 0, temp: 'absolute' }, iob, p,
      null, { mealCOB: 0, carbs: 0 }, tbf, false, null, new Date(now));
  });
  console.log('profile', c[0], 'current_basal', p.current_basal, '->',
    JSON.stringify({ error: rT.error, rate: rT.rate, duration: rT.duration, reason: (rT.reason || '').slice(0, 50) }));
});
