'use strict';
// F-04, step 2: how common are realistic triggers? Changes nothing; only calls
// oref0's getMaxSafeBasal, round_basal and setTempBasal.
// A request above the limit is issued as round_basal(maxSafeBasal), so the issued
// rate exceeds the limit exactly when round_basal rounds maxSafeBasal up. Overshoots
// below 1e-9 U/h (floating-point noise on on-grid values) are not counted.
// Usage: node scripts/findings/f04-search.js [lib]
var c = require('./common');
var lib = c.libDir();
var t = c.load(lib, 'basal-set-temp');
var round_basal = c.load(lib, 'round-basal');
var EPS = 1e-9;
function vals(lo, hi, step) { var a = []; for (var i = Math.round(lo / step); i <= Math.round(hi / step) + 1e-9; i++) a.push(Math.round(i * step * 1000) / 1000); return a; }
function up(m, model) { return round_basal(m, {model: model}) - m > EPS; }
var out = {};
c.quiet(function () {
  [['default (0.05 step below 1 U/h)', undefined], ['x23/x54 (0.025 step below 1 U/h)', '554']].forEach(function (pm) {
    var model = pm[1], r = {};
    var cb2 = vals(0.05, 3.00, 0.01), cbGrid = vals(0.05, 3.00, model ? 0.025 : 0.05);
    function share(list, f) { var n = list.filter(f).length; return n + '/' + list.length + ' (' + (100 * n / list.length).toFixed(1) + '%)'; }
    r['current_basal, two decimals 0.05-3.00: 4 x current_basal rounds up'] = share(cb2, function (x) { return up(4 * x, model); });
    r['current_basal on the pump grid 0.05-3.00: 4 x current_basal rounds up'] = share(cbGrid, function (x) { return up(4 * x, model); });
    r['max_basal, two decimals 0.05-10.00: rounds up'] = share(vals(0.05, 10, 0.01), function (x) { return up(x, model); });
    r['max_daily_basal, two decimals 0.05-3.00: 3 x max_daily_basal rounds up'] = share(cb2, function (x) { return up(3 * x, model); });
    // All combinations, two decimals: current_basal 0.05-3.00, max_daily_basal >= current_basal (0.05-3.00), max_basal 0.05-10.00.
    var mb = vals(0.05, 10, 0.01), n = 0, k = 0, worst = 0, ex = null, cache = {};
    cb2.forEach(function (cb) { cb2.forEach(function (md) {
      if (md < cb) return;
      mb.forEach(function (a) {
        var m = Math.min(a, 3 * md, 4 * cb); n++;
        var key = m, o = cache[key]; if (o === undefined) o = cache[key] = round_basal(m, {model: model}) - m;
        if (o > EPS) { k++; if (o > worst) { worst = o; ex = [cb, a, md, m]; } }
      });
    }); });
    r['all (current_basal, max_basal, max_daily_basal) two-decimal combinations with max_daily_basal >= current_basal: limit rounds up'] =
      k + '/' + n + ' (' + (100 * k / n).toFixed(1) + '%), largest overshoot ' + worst.toFixed(4) + ' U/h';
    // Confirm the largest case through setTempBasal itself.
    var prof = {current_basal: ex[0], max_basal: ex[1], max_daily_basal: ex[2]}; if (model) prof.model = model;
    var res = t.setTempBasal(10, 30, prof, {}, {});
    r['example (setTempBasal, request 10 U/h)'] = 'current_basal ' + ex[0] + ', max_basal ' + ex[1] + ', max_daily_basal ' + ex[2] +
      ': maxSafeBasal ' + t.getMaxSafeBasal(prof) + ', issued ' + res.rate + ' U/h';
    // Typical user values: the scheduled basals (current_basal, max_daily_basal) are pump
    // settings and so on the pump grid; max_basal is typed freely with two decimals.
    var n2 = 0, k2 = 0, bind = 0, kb = 0;
    cbGrid.forEach(function (cb) { cbGrid.forEach(function (md) {
      if (md < cb) return;
      mb.forEach(function (a) {
        var m = Math.min(a, 3 * md, 4 * cb); n2++;
        var o = round_basal(m, {model: model}) - m;
        if (o > EPS) k2++;
        if (a <= Math.min(3 * md, 4 * cb)) { bind++; if (o > EPS) kb++; }
      });
    }); });
    r['typical: current_basal and max_daily_basal on the pump grid 0.05-3.00, max_basal two decimals 0.05-10.00: limit rounds up'] =
      k2 + '/' + n2 + ' (' + (100 * k2 / n2).toFixed(1) + '%); among those where max_basal is the binding limit: ' +
      kb + '/' + bind + ' (' + (100 * kb / bind).toFixed(1) + '%)';
    r['typical: max_basal values 0.05-10.00 on the 0.1 U/h grid (e.g. 2.0, 3.5) that round up'] =
      share(vals(0.1, 10, 0.1), function (x) { return up(x, model); });
    out[pm[0]] = r;
  });
});
Object.keys(out).forEach(function (k) { console.log('Pump model: ' + k); Object.keys(out[k]).forEach(function (q) { console.log('  ' + q + ': ' + out[k][q]); }); });
