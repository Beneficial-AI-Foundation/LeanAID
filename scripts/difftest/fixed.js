// The differential test of the corrected version (docs/FIXED.md), shared by
//   TZ=UTC node scripts/difftest/run.js 100000 7 --fixed      (random cases; docs/difftest-fixed.json)
//   TZ=UTC node scripts/difftest/targeted.js --fixed           (scripts/difftest/targeted.jsonl)
// Each case runs through
//   - oref0 (vendor/oref0),
//   - the patched copy of oref0 (scripts/fixes/out/oref0-fixed, made by scripts/fixes/apply.sh),
//   - `aid-lean batch --fixed-triggers`: the corrected Lean version and the findings whose trigger
//     holds (LeanAID.Fixed.triggers).
// Checks:
//   (1) aid-lean --fixed is byte-identical to oref0, except on cases where a trigger holds;
//   (2) aid-lean --fixed is byte-identical to the patched oref0 (the same fixes in JavaScript);
//   (3) on the cases of each trigger, the corrected result is safe (see `safety`).
// Exit code 1 if (1), (2) or (3) fails for any case.
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var fs = require('fs');
var path = require('path');
var common = require('./common');
var ROOT = common.ROOT;

var FINDINGS = ['F-04', 'F-11', 'F-12', 'F-23'];

function newFixedStats(prefix) {
  var s = {};
  Object.keys(prefix).forEach(function (k) { s[k] = prefix[k]; });
  s.fixedVsOref0 = { identical: 0, differ: 0, differWithTrigger: 0, differWithoutTrigger: 0, triggerButIdentical: 0 };
  s.fixedVsPatchedJs = { identical: 0, differ: 0 };
  s.triggers = {};
  FINDINGS.forEach(function (f) { s.triggers[f] = { cases: 0, differ: 0, unsafe: 0 }; });
  s.triggerCombinations = {};
  s.f04 = { oref0MaxOvershoot: 0, oref0MaxOvershootCase: null, oref0RatesAboveMaxSafeBasal: 0,
    fixedRatesAboveMaxSafeBasal: 0, fixedMaxBelowMaxSafeBasal: 0, examples: [] };
  s.f11 = { oref0RateAboveBasal: 0, fixedRateAboveBasal: 0, fixedUnits: 0, examples: [] };
  s.f12 = { oref0RateAboveBasal: 0, fixedRateAboveBasal: 0, fixedUnits: 0, fixedZeroTemps: 0, examples: [] };
  s.f23 = { oref0DurationNull: 0, fixedDurations: {}, examples: [] };
  s.allFixedRatesWithinMaxSafeBasal = { checked: 0, above: 0 };
  return s;
}

function r6(x) { return Math.round(x * 1e6) / 1e6; }

// The safety property of each fix on a triggered case; returns false if it fails.
function safety(s, f, c, eo, fo) {
  var msb = common.getMaxSafeBasal(c.profile);
  var cb = c.profile.current_basal;
  var ex = function (o) { return { rate: o.rate, duration: o.duration, units: o.units }; };
  if (f === 'F-04') {
    var over = eo.rate - msb;
    s.f04.oref0RatesAboveMaxSafeBasal++;
    if (over > s.f04.oref0MaxOvershoot) { s.f04.oref0MaxOvershoot = r6(over); s.f04.oref0MaxOvershootCase = { maxSafeBasal: msb, oref0Rate: eo.rate, fixedRate: fo.rate }; }
    if (!(fo.rate <= msb)) { s.f04.fixedRatesAboveMaxSafeBasal++; return false; }
    s.f04.fixedMaxBelowMaxSafeBasal = Math.max(s.f04.fixedMaxBelowMaxSafeBasal, r6(msb - fo.rate));
    if (s.f04.examples.length < 3) s.f04.examples.push({ maxSafeBasal: msb, oref0: ex(eo), fixed: ex(fo) });
    return true;
  }
  if (f === 'F-11' || f === 'F-12') {
    var t = f === 'F-11' ? s.f11 : s.f12;
    if (eo.rate > cb) t.oref0RateAboveBasal++;
    if (fo.units !== undefined) t.fixedUnits++;
    if (fo.rate > cb && !(f === 'F-11' && fo.rate === roundBasal(cb, c.profile))) t.fixedRateAboveBasal++;
    if (f === 'F-12' && fo.rate === 0 && fo.duration > 0) t.fixedZeroTemps++;
    if (t.examples.length < 3) t.examples.push({ oref0: ex(eo), fixed: ex(fo) });
    // F-12: no microbolus, no rate above current_basal, and no rate only while the running
    // temp is not above current_basal (docs/FIXED.md, F-12)
    if (f === 'F-12') return fo.units === undefined && !(fo.rate > cb) &&
      (fo.rate !== undefined || !(c.currenttemp && c.currenttemp.rate > cb));
    return fo.units === undefined && !(fo.rate > Math.max(cb, roundBasal(cb, c.profile)));
  }
  if (f === 'F-23') {
    if (eo.duration === null) s.f23.oref0DurationNull++;
    s.f23.fixedDurations[fo.duration] = (s.f23.fixedDurations[fo.duration] || 0) + 1;
    if (s.f23.examples.length < 3) s.f23.examples.push({ oref0: ex(eo), fixed: ex(fo) });
    return fo.units === undefined && (fo.rate === undefined || fo.rate === 0) &&
      (fo.duration === undefined || (fo.duration >= 30 && fo.duration <= 120));
  }
  return true;
}

var roundBasal = require(path.join(ROOT, 'vendor/oref0/lib/round-basal'));

// Count one case. Returns a mismatch record or null.
function countCase(s, c, e, j, l, n) {
  var trig = l.triggers;
  var key = trig.length ? trig.join('+') : 'none';
  s.triggerCombinations[key] = (s.triggerCombinations[key] || 0) + 1;
  var eo = JSON.parse(e.out), fo = JSON.parse(l.out);
  var bad = [];
  if (l.out === j.out) s.fixedVsPatchedJs.identical++; else { s.fixedVsPatchedJs.differ++; bad.push('patched JS differs'); }
  if (l.out === e.out) {
    s.fixedVsOref0.identical++;
    if (trig.length) s.fixedVsOref0.triggerButIdentical++;
  } else {
    s.fixedVsOref0.differ++;
    if (trig.length) s.fixedVsOref0.differWithTrigger++;
    else { s.fixedVsOref0.differWithoutTrigger++; bad.push('differs from oref0 without a trigger'); }
  }
  trig.forEach(function (f) {
    s.triggers[f].cases++;
    if (l.out !== e.out) s.triggers[f].differ++;
    if (!safety(s, f, c, eo, fo)) { s.triggers[f].unsafe++; bad.push(f + ' result not safe'); }
  });
  var msb = common.getMaxSafeBasal(c.profile);
  if (typeof fo.rate === 'number' && msb > 0) {
    s.allFixedRatesWithinMaxSafeBasal.checked++;
    if (fo.rate > msb) { s.allFixedRatesWithinMaxSafeBasal.above++; bad.push('fixed rate above maxSafeBasal'); }
  }
  if (!bad.length) return null;
  return { n: n, problems: bad, triggers: trig, oref0: eo, fixed: fo, patchedJs: JSON.parse(j.out), input: c };
}

function ok(s) {
  return s.fixedVsOref0.differWithoutTrigger === 0 && s.fixedVsPatchedJs.differ === 0 &&
    FINDINGS.every(function (f) { return s.triggers[f].unsafe === 0; }) && s.allFixedRatesWithinMaxSafeBasal.above === 0;
}

function patchedRunner() {
  if (!fs.existsSync(path.join(common.FIXED_OREF0, 'lib'))) {
    console.error('missing ' + common.FIXED_OREF0 + ': run bash scripts/fixes/apply.sh first'); process.exit(2);
  }
  return common.runnerFor(common.FIXED_OREF0);
}

// Random cases (scripts/difftest/run.js --fixed).
function runFixed(o) {
  var runPatched = patchedRunner();
  var casesFile = path.join(o.OUT, 'chunk-fixed.jsonl');
  var s = newFixedStats({ cases: o.N, seed: o.seed });
  s.nodeSeconds = 0; s.aidLeanSeconds = 0;
  var mm = fs.openSync(path.join(o.OUT, 'fixed-mismatches.jsonl'), 'w');
  var t00 = Date.now();
  var CHUNK = 10000;
  for (var base = 0; base < o.N; base += CHUNK) {
    var m = Math.min(CHUNK, o.N - base), cases = [], lines = [], exp = [], pat = [];
    var t0 = Date.now();
    for (var n = 0; n < m; n++) {
      var c = o.genCase(); cases.push(c); lines.push(JSON.stringify(c));
      exp.push(common.runNodeQuiet(c)); pat.push(runPatched(c));
    }
    s.nodeSeconds += (Date.now() - t0) / 1000;
    fs.writeFileSync(casesFile, lines.join('\n') + '\n');
    t0 = Date.now();
    var lean = common.runLeanFixed(casesFile);
    s.aidLeanSeconds += (Date.now() - t0) / 1000;
    for (n = 0; n < m; n++) {
      var d = countCase(s, cases[n], exp[n], pat[n], lean[n], base + n);
      if (d) fs.writeSync(mm, JSON.stringify(d) + '\n');
    }
    console.error('fixed: ' + (base + m) + '/' + o.N + ' cases, ' + Math.round((Date.now() - t00) / 1000) + ' s');
  }
  fs.closeSync(mm);
  s.nodeSeconds = Math.round(s.nodeSeconds * 10) / 10;
  s.aidLeanSeconds = Math.round(s.aidLeanSeconds * 10) / 10;
  s.wallSeconds = Math.round((Date.now() - t00) / 100) / 10;
  s.ok = ok(s);
  fs.writeFileSync(path.join(ROOT, 'docs/difftest-fixed.json'), JSON.stringify(s, null, 1) + '\n');
  console.log(JSON.stringify(s, null, 1));
  summary(s);
  process.exit(s.ok ? 0 : 1);
}

// The cases of a file (scripts/difftest/targeted.js --fixed).
function runFixedFile(file) {
  var runPatched = patchedRunner();
  var cases = fs.readFileSync(file, 'utf8').split('\n').filter(function (l) { return l.trim() !== ''; }).map(JSON.parse);
  var s = newFixedStats({ file: path.relative(ROOT, path.resolve(file)), cases: cases.length });
  var lean = common.runLeanFixed(file);
  var bad = [];
  cases.forEach(function (c, n) {
    var d = countCase(s, c, common.runNodeQuiet(c), runPatched(c), lean[n], n);
    if (d) { d.name = c.name; bad.push(d); }
  });
  bad.forEach(function (d) { console.log('PROBLEM ' + (d.name || d.n) + ': ' + d.problems.join('; ')); });
  s.ok = ok(s);
  console.log(JSON.stringify(s));
  summary(s, 'targeted --fixed');
  process.exit(s.ok ? 0 : 1);
}

function summary(s, tag) {
  console.log((tag || 'fixed') + ': ' + s.fixedVsOref0.identical + '/' + s.cases + ' identical to oref0, ' +
    s.fixedVsOref0.differWithTrigger + ' differ with a trigger, ' + s.fixedVsOref0.differWithoutTrigger +
    ' differ without one; ' + s.fixedVsPatchedJs.identical + '/' + s.cases + ' identical to the patched oref0; ' +
    'triggers ' + FINDINGS.map(function (f) { return f + ' ' + s.triggers[f].cases; }).join(', ') +
    (s.ok ? '; OK' : '; FAILED'));
}

module.exports = { runFixed: runFixed, runFixedFile: runFixedFile };
