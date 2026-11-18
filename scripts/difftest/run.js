#!/usr/bin/env node
// Differential testing of aid-lean against oref0's determine_basal (M10).
//   TZ=UTC node scripts/difftest/run.js [N=100000] [seed=1]
// Generates N random inputs, runs oref0 in-process (exactly as
// bin/oref0-determine-basal.js does: getLastGlucose, then determine_basal) and
// `aid-lean batch` on the same inputs, and compares the JSON outputs.
// Writes docs/difftest.json (summary) and scripts/difftest/out/mismatches.jsonl.
'use strict';
var fs = require('fs');
var path = require('path');
var cp = require('child_process');
var ROOT = path.resolve(__dirname, '../..');
var O = path.join(ROOT, 'vendor/oref0');
var getLastGlucose = require(path.join(O, 'lib/glucose-get-last'));
var determine_basal = require(path.join(O, 'lib/determine-basal/determine-basal'));
var tempBasalFunctions = require(path.join(O, 'lib/basal-set-temp'));

if (process.env.TZ !== 'UTC') { console.error('run with TZ=UTC'); process.exit(1); }
var N = parseInt(process.argv[2] || '100000', 10);
var seed = parseInt(process.argv[3] || '1', 10);

// mulberry32
function rng() { seed |= 0; seed = seed + 0x6D2B79F5 | 0; var t = Math.imul(seed ^ seed >>> 15, 1 | seed);
  t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }
function uni(a, b, d) { var x = a + rng() * (b - a); var f = Math.pow(10, d || 0); return Math.round(x * f) / f; }
function pick(xs) { return xs[Math.floor(rng() * xs.length)]; }
function chance(p) { return rng() < p; }

function genCase() {
  var now = Date.UTC(2026, 10, 18, 0, 0, 0) + Math.floor(rng() * 86400) * 1000;
  var model = pick(['522', '523', '554', undefined]);
  var cb = chance(0.5) ? uni(0.1, 3, 1) : uni(0.025, 1.5, 3);
  cb = Math.max(0.025, Math.round(cb * 40) / 40);
  var mdb = Math.round((cb + uni(0, 1.5, 2)) * 1000) / 1000;
  var mb = chance(0.2) ? uni(cb, cb * 2, 2) : Math.round((cb * uni(2, 5, 1)) * 100) / 100;
  var min_bg = uni(80, 130, 0), max_bg = min_bg + uni(0, 40, 0);
  var amax = pick([1.2, 1.5, 2]);
  var profile = {
    current_basal: cb, max_daily_basal: mdb, max_basal: mb, max_iob: uni(0, 6, 1),
    min_bg: min_bg, max_bg: max_bg, sens: uni(20, 150, 0), carb_ratio: uni(5, 20, 1), autosens_max: amax,
    dia: pick([3, 4, 5]), type: 'current', maxCOB: 120, noisyCGMTargetMultiplier: 1.3, maxRaw: 200,
    enableUAM: chance(0.5), enableSMB_with_COB: chance(0.5), enableSMB_always: chance(0.3),
    enableSMB_after_carbs: chance(0.3), enableSMB_with_temptarget: chance(0.3), enableSMB_high_bg: chance(0.2),
    enableSMB_high_bg_target: 160, allowSMB_with_high_temptarget: chance(0.3), A52_risk_enable: chance(0.2) ? true : false,
    maxSMBBasalMinutes: chance(0.8) ? pick([30, 45, 60, 75, 90]) : undefined,
    maxUAMSMBBasalMinutes: chance(0.8) ? pick([30, 45, 60]) : undefined,
    bolus_increment: chance(0.5) ? pick([0.05, 0.1, 0.025]) : undefined,
    SMBInterval: chance(0.5) ? pick([1, 3, 5, 10, 15]) : undefined,
    skip_neutral_temps: chance(0.1), carbsReqThreshold: pick([1, 5, 10]),
    remainingCarbsCap: chance(0.5) ? pick([60, 90, 120]) : undefined,
    remainingCarbsFraction: chance(0.3) ? pick([0.5, 1]) : undefined,
    exercise_mode: chance(0.2), high_temptarget_raises_sensitivity: chance(0.2),
    low_temptarget_lowers_sensitivity: chance(0.2), sensitivity_raises_target: chance(0.5),
    resistance_lowers_target: chance(0.3), half_basal_exercise_target: chance(0.3) ? pick([140, 160, 200]) : undefined,
    temptargetSet: chance(0.2), out_units: chance(0.1) ? 'mmol/L' : 'mg/dL',
    current_basal_safety_multiplier: chance(0.2) ? pick([1, 2, 5]) : undefined,
    max_daily_safety_multiplier: chance(0.2) ? pick([1, 2, 4]) : undefined,
    maxDelta_bg_threshold: chance(0.2) ? pick([0.1, 0.3, 0.5]) : undefined
  };
  if (model) profile.model = model;
  Object.keys(profile).forEach(function (k) { if (profile[k] === undefined) delete profile[k]; });
  // keep the validity condition V5: cb * amax <= maxSafeBasal
  var msb = Math.min(mb, (profile.max_daily_safety_multiplier || 3) * mdb, (profile.current_basal_safety_multiplier || 4) * cb);
  if (cb * amax > msb) profile.max_basal = mb = Math.round(cb * amax * 100 + 1) / 100;
  // glucose history: 10 readings every 5 minutes
  var bg = uni(40, 350, 0), slope = uni(-12, 12, 1), age = chance(0.05) ? uni(13, 30, 0) : uni(0, 6, 0);
  var dev = chance(0.5) ? 'dex' : undefined, noise = chance(0.1) ? pick([1, 2, 3]) : undefined;
  var glucose = [];
  for (var i = 0; i < 10; i++) {
    var e = { date: now - age * 60000 - i * 300000, glucose: Math.max(39, Math.round(bg - slope * i + uni(-2, 2, 0))) };
    if (dev) e.device = dev;
    if (i === 0 && noise) e.noise = noise;
    glucose.push(e);
  }
  if (chance(0.02)) glucose[0].glucose = pick([5, 38]);
  // IOB array
  var iob0 = uni(-1.5, 6, 3), act0 = uni(-0.01, 0.06, 4), iob = [];
  for (var k = 0; k < 48; k++) {
    var f = Math.max(0, 1 - k / 48);
    iob.push({ iob: Math.round(iob0 * f * 1000) / 1000, activity: Math.round(act0 * f * 10000) / 10000,
      iobWithZeroTemp: { iob: Math.round((iob0 - 0.2 * k / 12) * f * 1000) / 1000,
                         activity: Math.round((act0 - 0.003) * f * 10000) / 10000 } });
  }
  if (chance(0.05)) iob = iob[0];   // a single object, as in oref0's unit tests
  var head = Array.isArray(iob) ? iob[0] : iob;
  head.lastBolusTime = now - uni(0, 300, 0) * 60000;
  var ctDur = chance(0.4) ? 0 : uni(1, 120, 0);
  var ctRate = ctDur ? uni(0, mb * 1.2, 2) : 0;
  head.lastTemp = { date: now - uni(0, 40, 0) * 60000, rate: chance(0.9) ? ctRate : uni(0, 3, 2), duration: chance(0.9) ? 30 : uni(1, 60, 0) };
  var currenttemp = { duration: ctDur, rate: ctRate, temp: 'absolute' };
  // meal data
  var meal = {};
  if (chance(0.8)) {
    var carbs = chance(0.4) ? 0 : uni(5, 120, 0);
    meal = { carbs: carbs, nsCarbs: carbs, bwCarbs: 0, journalCarbs: 0, mealCOB: carbs ? uni(0, carbs, 0) : 0,
      currentDeviation: uni(-5, 5, 2), maxDeviation: uni(0, 8, 2), minDeviation: uni(-5, 0, 2),
      slopeFromMaxDeviation: uni(-2, 0, 3), slopeFromMinDeviation: uni(0, 2, 3), allDeviations: [0, 0, 0],
      lastCarbTime: carbs ? now - uni(0, 360, 0) * 60000 : 0, bwFound: chance(0.1) };
  }
  var autosens = chance(0.8) ? { ratio: uni(0.7, Math.min(1.3, amax), 2) } : undefined;
  return { iob: iob, currenttemp: currenttemp, glucose: glucose, profile: profile, autosens: autosens,
           meal: meal, microBolusAllowed: chance(0.5), currentTime: now };
}

function runNode(c) {
  var gs = getLastGlucose(JSON.parse(JSON.stringify(c.glucose)));
  var autosens = c.autosens ? JSON.parse(JSON.stringify(c.autosens)) : null;
  var rT = determine_basal(gs, JSON.parse(JSON.stringify(c.currenttemp)), JSON.parse(JSON.stringify(c.iob)),
    JSON.parse(JSON.stringify(c.profile)), autosens, JSON.parse(JSON.stringify(c.meal)), tempBasalFunctions,
    c.microBolusAllowed, null, new Date(c.currentTime));
  return typeof rT.error === 'undefined' ? JSON.stringify(rT) : JSON.stringify({ error: rT.error });
}

var OUT = path.join(__dirname, 'out');
fs.mkdirSync(OUT, { recursive: true });
var casesFile = path.join(OUT, 'cases.jsonl');
var fd = fs.openSync(casesFile, 'w');
var expected = [];
var origErr = console.error; console.error = function () {};
var origWrite = process.stderr.write.bind(process.stderr); process.stderr.write = function () { return true; };
for (var n = 0; n < N; n++) {
  var c = genCase();
  fs.writeSync(fd, JSON.stringify(c) + '\n');
  expected.push(runNode(c));
}
fs.closeSync(fd);
console.error = origErr; process.stderr.write = origWrite;

var t0 = Date.now();
var lean = cp.execFileSync(path.join(ROOT, '.lake/build/bin/aid-lean'), ['batch', casesFile],
  { encoding: 'utf8', maxBuffer: 1 << 30 }).split('\n');
var leanSecs = (Date.now() - t0) / 1000;

var stats = { cases: N, seed: parseInt(process.argv[3] || '1', 10), identical: 0, reasonOnly: 0, valueDiff: 0,
  fieldsDiffering: {}, paths: { smbUnits: 0, errors: 0, rateNull: 0 }, aidLeanSeconds: leanSecs };
var mm = fs.openSync(path.join(OUT, 'mismatches.jsonl'), 'w');
var cases = fs.readFileSync(casesFile, 'utf8').split('\n');
for (n = 0; n < N; n++) {
  var e = expected[n], l = lean[n];
  var eo = JSON.parse(e);
  if (eo.units !== undefined) stats.paths.smbUnits++;
  if (eo.error !== undefined) stats.paths.errors++;
  if (eo.rate === null) stats.paths.rateNull++;
  if (e === l) { stats.identical++; continue; }
  var lo; try { lo = JSON.parse(l); } catch (err) { lo = {}; }
  var keys = {}; Object.keys(eo).concat(Object.keys(lo)).forEach(function (k) { keys[k] = 1; });
  var diff = Object.keys(keys).filter(function (k) { return JSON.stringify(eo[k]) !== JSON.stringify(lo[k]); });
  if (diff.length === 1 && diff[0] === 'reason') stats.reasonOnly++; else stats.valueDiff++;
  diff.forEach(function (k) { stats.fieldsDiffering[k] = (stats.fieldsDiffering[k] || 0) + 1; });
  fs.writeSync(mm, JSON.stringify({ n: n, fields: diff, oref0: eo, aidLean: lo, input: JSON.parse(cases[n]) }) + '\n');
}
fs.closeSync(mm);
fs.writeFileSync(path.join(ROOT, 'docs/difftest.json'), JSON.stringify(stats, null, 1) + '\n');
console.log(JSON.stringify(stats, null, 1));
