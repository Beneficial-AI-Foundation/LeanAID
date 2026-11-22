'use strict';
// F-11 through oref0's own input path: glucose.json entries -> lib/glucose-get-last.js ->
// determine-basal. Information only (not part of run.js): does an undated newest reading
// still reach the dosing logic when glucose_status is built by oref0 itself?
// Entries: BG rising 5 mg/dL per 5 min; the newest one (250) has no date/display_time/dateString.
// Usage: node scripts/findings/f11-pipeline.js [lib]
var c = require('./common');
var lib = c.libDir();
var getLast = c.load(lib, 'glucose-get-last');
function entries(newestDated, device) {
  var e = [];
  for (var i = 0; i < 9; i++) {
    var t = c.NOW.getTime() - i * 5 * 60000;
    var x = {glucose: 250 - 5 * i, device: device, type: 'sgv', date: t, dateString: new Date(t).toISOString()};
    if (i === 0 && !newestDated) { delete x.date; delete x.dateString; }
    e.push(x);
  }
  return e;
}
function show(label, newestDated, device) {
  var gs = c.quiet(function () { return getLast(entries(newestDated, device)); });
  var r = c.determine(lib, gs, c.testProfile());
  console.log(label + ': glucose_status ' + JSON.stringify({glucose: gs.glucose, delta: gs.delta,
    short_avgdelta: gs.short_avgdelta, long_avgdelta: gs.long_avgdelta, date: gs.date}) +
    ' -> ' + c.fmt(r) + (r && r.reason ? ' | ' + r.reason.split(';')[0].slice(0, 110) : ''));
}
show('newest dated     ', true, 'xdrip');
show('newest undated   ', false, 'xdrip');
show('undated, fakecgm ', false, 'fakecgm');
