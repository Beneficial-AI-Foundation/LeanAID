'use strict';
// F-12: with max_basal or max_daily_basal missing, maxSafeBasal is NaN and no cap applies.
// Trigger: the test profile without max_basal and/or max_daily_basal, BG 300 rising, IOB 0.
// Control: the intact test profile (max_basal 3.5) with the same reading.
// PRESENT: some trigger issues a rate above 4 x current_basal (the cap that remains
// when the missing settings are ignored) and the control stays within maxSafeBasal.
var c = require('./common');
var lib = c.libDir();
var bg = {glucose: 300, delta: 10, short_avgdelta: 10, long_avgdelta: 10, date: c.NOW.getTime()};
var p = c.testProfile();
var bound = 4 * p.current_basal;
var variants = {
  'no max_basal, no max_daily_basal': function (q) { delete q.max_basal; delete q.max_daily_basal; },
  'no max_basal': function (q) { delete q.max_basal; },
  'no max_daily_basal': function (q) { delete q.max_daily_basal; }
};
var parts = [], present = false, odd = false, ctrl;
try {
  ctrl = c.determine(lib, Object.assign({}, bg), c.testProfile());
  Object.keys(variants).forEach(function (k) {
    var q = c.testProfile(); variants[k](q);
    var r = c.determine(lib, Object.assign({}, bg), q);
    parts.push(k + ': ' + c.fmt(r));
    if (!r || r.error) odd = true;
    else if (typeof r.rate === 'number' && r.rate > bound) present = true;
  });
} catch (e) {
  c.verdict('F-12', 'INCONCLUSIVE', 'threw: ' + e.message);
}
var ctrlOk = ctrl && !ctrl.error && typeof ctrl.rate === 'number' && ctrl.rate <= p.max_basal;
var detail = parts.join('; ') + '; control (max_basal 3.5): ' + c.fmt(ctrl);
if (c.FIXED) {   // the control must give the same result as vendor/oref0
  var same = c.sameAsVendor(function (l) { return c.determine(l, Object.assign({}, bg), c.testProfile()); }, lib);
  detail += same ? ' (control as vendor/oref0)' : ' (control DIFFERS from vendor/oref0)';
  if (!same) c.verdict('F-12', 'INCONCLUSIVE', detail);
}
if (!ctrlOk) c.verdict('F-12', 'INCONCLUSIVE', detail);
if (present) c.verdict('F-12', 'PRESENT', detail);
if (!odd) c.verdict('F-12', 'ABSENT', detail);
c.verdict('F-12', 'INCONCLUSIVE', detail);
