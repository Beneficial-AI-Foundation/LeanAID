// Differential check of the F-04 fix: patched vs unpatched setTempBasal.
// Usage: NODE_PATH=vendor/oref0/node_modules node scripts/findings/f04-fix-differential.js <unpatched lib> <patched lib> (absolute paths)
var A = require(process.argv[2] + '/basal-set-temp'), B = require(process.argv[3] + '/basal-set-temp');
console.error = function () {};
var n = 0, diff = 0, bad = 0, over = 0, wrongDiff = 0;
[undefined, '554'].forEach(function (model) {
  for (var cb = 0.05; cb <= 3.0001; cb += 0.05) for (var mb = 0.05; mb <= 10.0001; mb += 0.01)
  for (var req = 0; req <= 12; req += 0.37) {
    var p = {current_basal: +cb.toFixed(2), max_basal: +mb.toFixed(2), max_daily_basal: +cb.toFixed(2)};
    if (model) p.model = model;
    var m = A.getMaxSafeBasal(p);
    var a = A.setTempBasal(req, 30, p, {}, {}), b = B.setTempBasal(req, 30, p, {}, {});
    n++;
    if (a.rate > m + 1e-9) over++;
    if (b.rate > m + 1e-9) bad++;
    if (a.rate !== b.rate || a.duration !== b.duration) { diff++; if (!(a.rate > m + 1e-9)) wrongDiff++; }
  }
});
console.log('cases ' + n + '; unpatched above maxSafeBasal: ' + over + '; patched above maxSafeBasal: ' + bad +
  '; patched differs from unpatched: ' + diff + ' (of which where unpatched was within the limit: ' + wrongDiff + ')');
