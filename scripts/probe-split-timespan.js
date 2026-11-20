// F-24 probe (QUIRK Q6): oref0 0.7.1 can lose temp-basal insulin when a temp longer than
// 30 minutes crosses a basal schedule entry or midnight (case H, with a flat schedule).
//   TZ=UTC node scripts/probe-split-timespan.js [path to oref0, default vendor/oref0]
// For each case it prints the net temp insulin of the treatments that oref0 builds, the
// same with a fixed copy of lib/iob/history.js (sim/q6fix.js, loaded in memory; the oref0
// checkout is not changed), the exact integral without rounding, and the IOB at 07:00 and
// 08:00 (case H: 01:00 and 02:00; lib/iob, currentIOBOnly) with oref0 and with the fix.
// "Q6 loss" is fixed minus oref0, so rounding is the same on both sides.
'use strict';
var path = require('path');
var O = path.resolve(process.argv[2] || path.join(__dirname, '../vendor/oref0'));
var histFile = path.join(O, 'lib/iob/history.js');
var calcOref = require(histFile);
var generate = require(path.join(O, 'lib/iob'));

var calcFixed = require('../sim/q6fix').load(O);   // the fix, in memory

function iso(h, m, d) { return new Date(Date.UTC(2026, 10, d || 18, h, m, 0)).toISOString(); }
function netInsulin(treatments) {
  return treatments.filter(function (e) { return typeof e.insulin === 'number'; })
                   .reduce(function (s, e) { return s + e.insulin; }, 0);
}
function quiet(f) {
  var saved = console.error; console.error = function () {};
  try { return f(); } finally { console.error = saved; }
}
function run(label, startH, startM, rate, dur, changeMin, iobHours) {
  var history = [
    { _type: 'TempBasalDuration', 'duration (min)': dur, timestamp: iso(startH, startM, startH >= 12 ? 17 : 18) },
    { _type: 'TempBasal', temp: 'absolute', rate: rate, timestamp: iso(startH, startM, startH >= 12 ? 17 : 18) } ];
  var basalprofile = [{ i: 0, start: '00:00:00', minutes: 0, rate: 1 }];
  if (changeMin !== null) basalprofile.push({ i: 1, start: '06:00:00', minutes: changeMin, rate: 1.2 });
  var profile = { current_basal: 1, dia: 5, basalprofile: basalprofile, curve: 'rapid-acting' };
  var inputs = { history: history, history24: [], profile: profile, clock: iso(8, 0) };
  var tO = quiet(function () { return calcOref(inputs); });
  var tF = quiet(function () { return calcFixed(inputs); });
  function iobAt(h, t) {
    var at = Object.assign({}, inputs, { clock: iso(h, 0) });
    return quiet(function () { return generate(at, true, t)[0].iob; });
  }
  var exact = 0, t0 = startH * 60 + startM;
  for (var m = t0; m < t0 + dur; m++) {
    exact += (rate - ((changeMin !== null && m >= changeMin) ? 1.2 : 1)) / 60;
  }
  var nO = netInsulin(tO), nF = netInsulin(tF);
  console.log(label);
  console.log('   net temp insulin: oref0 ' + nO.toFixed(2) + ' U, fixed ' + nF.toFixed(2) +
    ' U, exact ' + exact.toFixed(2) + ' U; Q6 loss ' + (nF - nO).toFixed(2) + ' U');
  (iobHours || [7, 8]).forEach(function (h) {
    console.log('   IOB at 0' + h + ':00:     oref0 ' + iobAt(h, tO).toFixed(3) + ' U, fixed ' +
      iobAt(h, tF).toFixed(3) + ' U');
  });
}
run('A zero temp 60m from 05:50, change at 06:00', 5, 50, 0, 60, 360);
run('B zero temp 60m from 05:50, no change', 5, 50, 0, 60, null);
run('C zero temp 120m from 05:00, change at 06:00', 5, 0, 0, 120, 360);
run('D 2 U/h temp 120m from 05:40, change at 06:00', 5, 40, 2, 120, 360);
run('E 2 U/h temp 30m from 05:50, change at 06:00', 5, 50, 2, 30, 360);
run('F 2 U/h temp 60m from 05:50, change at 06:00', 5, 50, 2, 60, 360);
run('G zero temp 90m from 05:20, change at 06:00', 5, 20, 0, 90, 360);
run('H zero temp 60m from 23:50, flat schedule (midnight)', 23, 50, 0, 60, null, [1, 2]);
