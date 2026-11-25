'use strict';
// F-04: setTempBasal caps to maxSafeBasal and then rounds to the pump step, which can
// round up. Trigger: request 2 U/h with max_basal 0.83 (off the 0.05 grid).
// Control: max_basal 0.85 (on the grid).
// PRESENT: trigger issues a rate above maxSafeBasal, control issues at most maxSafeBasal.
// --fixed (docs/FIXED.md): the fix acts at the exit of determine_basal, not in setTempBasal, so
// the verdict is taken end to end: PRESENT if determine_basal with max_basal 0.83 issues a rate
// above maxSafeBasal; the control (max_basal 0.85) must give the same result as vendor/oref0.
var c = require('./common');
var lib = c.libDir();
if (c.FIXED) {
  var e2e = function (mb) {
    return function (l) {
      var q = c.testProfile(); q.max_basal = mb;
      return c.determine(l, {glucose: 300, delta: 10, short_avgdelta: 10, long_avgdelta: 10, date: c.NOW.getTime()}, q);
    };
  };
  var ft, fc, same;
  try { ft = e2e(0.83)(lib); fc = e2e(0.85)(lib); same = c.sameAsVendor(e2e(0.85), lib); }
  catch (e) { c.verdict('F-04', 'INCONCLUSIVE', 'threw: ' + e.message); }
  var fd = 'determine_basal with max_basal 0.83: ' + c.fmt(ft) + '; control max_basal 0.85: ' + c.fmt(fc) +
    (same ? ' (as vendor/oref0)' : ' (DIFFERS from vendor/oref0)');
  if (!same || typeof ft.rate !== 'number') c.verdict('F-04', 'INCONCLUSIVE', fd);
  c.verdict('F-04', ft.rate > 0.83 ? 'PRESENT' : 'ABSENT', fd);
}
function run(maxBasal) {
  var t = c.load(lib, 'basal-set-temp');
  var prof = {current_basal: 0.5, max_basal: maxBasal, max_daily_basal: 1};
  return c.quiet(function () {
    return {max: t.getMaxSafeBasal(prof), r: t.setTempBasal(2, 30, prof, {}, {})};
  });
}
var trig, ctrl, e2e = '';
try {
  trig = run(0.83); ctrl = run(0.85);
  // End to end through determine_basal (information only): test profile, max_basal 0.83.
  var q = c.testProfile(); q.max_basal = 0.83;
  var r = c.determine(lib, {glucose: 300, delta: 10, short_avgdelta: 10, long_avgdelta: 10,
                             date: c.NOW.getTime()}, q);
  e2e = '; determine_basal with max_basal 0.83: ' + c.fmt(r);
} catch (e) {
  if (!trig || !ctrl) c.verdict('F-04', 'INCONCLUSIVE', 'threw: ' + e.message);
  e2e = '; determine_basal threw: ' + e.message;
}
var detail = 'maxSafeBasal ' + trig.max + ' -> ' + c.fmt(trig.r) + '; control maxSafeBasal ' +
  ctrl.max + ' -> ' + c.fmt(ctrl.r) + e2e;
var ctrlOk = typeof ctrl.r.rate === 'number' && ctrl.r.rate <= ctrl.max;
if (!ctrlOk || typeof trig.r.rate !== 'number') c.verdict('F-04', 'INCONCLUSIVE', detail);
if (trig.r.rate > trig.max) c.verdict('F-04', 'PRESENT', detail);
c.verdict('F-04', 'ABSENT', detail);
