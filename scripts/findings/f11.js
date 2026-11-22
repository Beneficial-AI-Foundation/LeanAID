'use strict';
// F-11: a glucose reading with no date has age NaN and skips the staleness check.
// Trigger: BG 250, deltas +5, no date. Control: the same reading dated 60 min ago.
// PRESENT: trigger raises the rate above the scheduled basal, control does not.
var c = require('./common');
var lib = c.libDir();
var bg = {glucose: 250, delta: 5, short_avgdelta: 5, long_avgdelta: 5};
var trig, ctrl;
try {
  trig = c.determine(lib, Object.assign({}, bg), c.testProfile());
  ctrl = c.determine(lib, Object.assign({date: c.NOW.getTime() - 60 * 60 * 1000}, bg), c.testProfile());
} catch (e) {
  c.verdict('F-11', 'INCONCLUSIVE', 'threw: ' + e.message);
}
var basal = c.testProfile().current_basal;
function raises(r) { return r && !r.error && typeof r.rate === 'number' && r.rate > basal; }
var detail = 'undated: ' + c.fmt(trig) + '; dated 60 min ago: ' + c.fmt(ctrl);
if (!trig || trig.error || !ctrl || ctrl.error) c.verdict('F-11', 'INCONCLUSIVE', detail);
if (raises(trig) && !raises(ctrl)) c.verdict('F-11', 'PRESENT', detail);
if (!raises(trig) && !raises(ctrl)) c.verdict('F-11', 'ABSENT', detail);
c.verdict('F-11', 'INCONCLUSIVE', detail);
