#!/usr/bin/env node
// Generates LeanAID/Conformance/Data/*.lean from the calls captured by
// scripts/capture/run.sh. Each case holds the exact inputs oref0's test passed
// (as Lean terms) and oref0's output, serialised with JSON.stringify.
//
// Numbers are emitted as decimal literals, which denote exact rationals in Lean
// (`(0.9 : JsNum)` is 9/10). `undefined` becomes `none`; JSON `null` becomes `none`
// too (see docs/DESIGN.md).
'use strict';
var fs = require('fs');
var path = require('path');
var ROOT = path.resolve(__dirname, '..');
var CAP = path.join(__dirname, 'capture/out');
var OUT = path.join(ROOT, 'LeanAID/Conformance/Data');
var FIXED_NOW = Date.UTC(2026, 10, 18, 12, 0, 0);

function isUndef(v) { return v === undefined || (v && typeof v === 'object' && v.__undefined); }

// ---- Lean term builders ----------------------------------------------------
function num(v) {
  if (typeof v !== 'number') throw new Error('not a number: ' + JSON.stringify(v));
  if (!isFinite(v)) throw new Error('non-finite');
  var s = String(v);                // shortest round-trip decimal, as JS prints it
  // Lean scientific literals accept 1e-7 / 1.5e+21 forms without '+'
  s = s.replace('e+', 'e');
  return v < 0 ? '(-' + s.slice(1) + ' : JsNum)' : '(' + s + ' : JsNum)';
}
function optNum(v) {
  if (isUndef(v) || v === null) return 'none';
  if (typeof v === 'number') return isNaN(v) ? 'some .nan' : 'some ' + num(v);
  if (v && v.__number === 'NaN') return 'some .nan';
  if (typeof v === 'string' && v.trim() !== '' && !isNaN(Number(v))) return 'some ' + num(Number(v)); // numeric string
  throw new Error('unsupported numeric field value ' + JSON.stringify(v));
}
function optBool(v) {
  if (isUndef(v) || v === null) return 'none';
  if (typeof v === 'boolean') return 'some ' + v;
  throw new Error('unsupported boolean field value ' + JSON.stringify(v));
}
function leanStr(s) { return JSON.stringify(s); }
function optStr(v) {
  if (typeof v === 'string') return 'some ' + leanStr(v);
  return 'none';
}

var PROFILE_NUM = ['current_basal', 'min_bg', 'max_bg', 'enableSMB_high_bg_target', 'max_iob',
  'half_basal_exercise_target', 'autosens_max', 'noisyCGMTargetMultiplier', 'maxRaw', 'sens', 'carb_ratio',
  'remainingCarbsCap', 'remainingCarbsFraction', 'maxDelta_bg_threshold', 'carbsReqThreshold',
  'maxSMBBasalMinutes', 'maxUAMSMBBasalMinutes', 'bolus_increment', 'SMBInterval', 'max_basal',
  'max_daily_basal', 'max_daily_safety_multiplier', 'current_basal_safety_multiplier', 'dia', 'insulinPeakTime'];
var PROFILE_BOOL = ['exercise_mode', 'high_temptarget_raises_sensitivity', 'low_temptarget_lowers_sensitivity',
  'temptargetSet', 'sensitivity_raises_target', 'resistance_lowers_target', 'allowSMB_with_high_temptarget',
  'A52_risk_enable', 'enableSMB_always', 'enableSMB_with_COB', 'enableSMB_after_carbs',
  'enableSMB_with_temptarget', 'enableSMB_high_bg', 'enableUAM', 'skip_neutral_temps', 'useCustomPeakTime',
  'suspend_zeros_iob'];
var PROFILE_STR = ['model', 'out_units', 'curve'];

function fields(pairs) {
  var fs_ = pairs.filter(function (p) { return p[1] !== 'none'; });
  if (fs_.length === 0) return '{}';
  return '{ ' + fs_.map(function (p) { return p[0] + ' := ' + p[1]; }).join(', ') + ' }';
}

function profile(p) {
  if (isUndef(p)) return 'none';
  var pairs = [];
  PROFILE_NUM.forEach(function (k) { pairs.push([k, optNum(p[k])]); });
  PROFILE_BOOL.forEach(function (k) { pairs.push([k, optBool(p[k])]); });
  PROFILE_STR.forEach(function (k) { pairs.push([k, optStr(p[k])]); });
  if (Array.isArray(p.basalprofile)) {
    pairs.push(['basalprofile', '[' + p.basalprofile.map(function (b) {
      return fields([['i', optNum(b.i)], ['minutes', num(b.minutes)], ['rate', num(b.rate)]]);
    }).join(', ') + ']']);
  }
  return 'some ' + fields(pairs);
}
function profileBare(p) { var s = profile(p); return s === 'none' ? '{}' : s.slice(5); }

function glucoseStatus(g) {
  if (isUndef(g)) return 'none';
  return 'some ' + fields([['glucose', optNum(g.glucose)], ['delta', optNum(g.delta)],
    ['short_avgdelta', optNum(g.short_avgdelta)], ['long_avgdelta', optNum(g.long_avgdelta)],
    ['date', optNum(g.date)], ['noise', optNum(g.noise)], ['last_cal', optNum(g.last_cal)],
    ['device', optStr(g.device)]]);
}
function currentTemp(c) {
  if (isUndef(c)) return 'none';
  return 'some ' + fields([['duration', optNum(c.duration)], ['rate', optNum(c.rate)], ['temp', optStr(c.temp)]]);
}
function iobTick(t) {
  var zt = 'none';
  if (t.iobWithZeroTemp && typeof t.iobWithZeroTemp === 'object' && !t.iobWithZeroTemp.__undefined) {
    zt = 'some (' + optNum(t.iobWithZeroTemp.activity) + ')';
  }
  var lt = 'none';
  if (t.lastTemp && typeof t.lastTemp === 'object' && !t.lastTemp.__undefined) {
    lt = 'some ' + fields([['date', optNum(t.lastTemp.date)], ['rate', optNum(t.lastTemp.rate)],
                           ['duration', optNum(t.lastTemp.duration)]]);
  }
  return fields([['iob', optNum(t.iob)], ['activity', optNum(t.activity)], ['iobWithZeroTemp', zt],
                 ['lastTemp', lt], ['lastBolusTime', optNum(t.lastBolusTime)]]);
}
function iobInput(x) {
  if (isUndef(x)) return 'none';
  if (Array.isArray(x)) return 'some (.array [' + x.map(iobTick).join(', ') + '])';
  return 'some (.single ' + iobTick(x) + ')';
}
function autosens(a) {
  if (isUndef(a) || a === null || a === false) return 'none';
  return 'some ' + fields([['ratio', optNum(a.ratio)]]);
}
function meal(m) {
  if (isUndef(m)) return 'none';
  return 'some ' + fields([['carbs', optNum(m.carbs)], ['mealCOB', optNum(m.mealCOB)], ['bwCarbs', optNum(m.bwCarbs)],
    ['bwFound', optBool(m.bwFound)], ['slopeFromMaxDeviation', optNum(m.slopeFromMaxDeviation)],
    ['slopeFromMinDeviation', optNum(m.slopeFromMinDeviation)], ['lastCarbTime', optNum(m.lastCarbTime)],
    ['reason', optStr(m.reason)]]);
}
function reservoir(r) {
  if (isUndef(r)) return '.undef';
  if (r === null) return '.null';
  return '(.str ' + leanStr(String(r)) + ')';
}
function clockOf(ct) {
  var now = FIXED_NOW;
  if (ct && ct.__date !== undefined) now = ct.__date;
  return '{ now := ' + now + ' }';
}

// Re-serialise oref0's captured result exactly as JSON.stringify would.
function revive(v) {
  if (Array.isArray(v)) return v.map(revive);
  if (v && typeof v === 'object') {
    if (v.__undefined) return undefined;
    if (v.__number) return Number(v.__number);
    if (v.__date !== undefined) return new Date(v.__date);
    var o = {};
    Object.keys(v).forEach(function (k) { o[k] = revive(v[k]); });
    return o;
  }
  return v;
}

function dbInputs(a) {
  var I = '\n      ';
  return '{' + I + 'glucose_status := ' + glucoseStatus(a[0]) +
    ',' + I + 'currenttemp := ' + currentTemp(a[1]) +
    ',' + I + 'iob_data := ' + iobInput(a[2]) +
    ',' + I + 'profile := ' + profile(a[3]) +
    ',' + I + 'autosens_data := ' + autosens(a[4]) +
    ',' + I + 'meal_data := ' + meal(a[5]) +
    ',' + I + 'microBolusAllowed := ' + (a[7] === true ? 'true' : 'false') +
    ',' + I + 'reservoir_data := ' + reservoir(a[8]) +
    ',' + I + 'clock := ' + clockOf(a[9]) + ' }';
}

// ---- test id lookup (from docs/tests-inventory.json) ------------------------
var inv = JSON.parse(fs.readFileSync(path.join(ROOT, 'docs/tests-inventory.json'), 'utf8'));
function testId(file, title) {
  var name = title.replace(/^[^ ]+ /, '');  // drop the describe() prefix
  var hits = inv.filter(function (t) { return t.file === file && !t.commented &&
    (title.endsWith(t.name) || name === t.name || (t.id === 'DB-05' && /round basal rates properly/.test(title))); });
  // duplicate names (DB-27/DB-28) are disambiguated by order of appearance
  return hits.map(function (h) { return h.id; });
}

function header(mod, doc) {
  return '/-\n  ' + doc + '\n  GENERATED by scripts/gen_conformance.js from scripts/capture/out. Do not edit.\n-/\n' +
    'import LeanAID.Conformance.Case\n\nnamespace LeanAID.Conformance.' + mod + '\n\nopen LeanAID\n\n';
}

function genDetermineBasal() {
  var recs = JSON.parse(fs.readFileSync(path.join(CAP, 'determine-basal.json'), 'utf8'));
  var calls = recs.filter(function (r) { return r.fn === 'determine_basal'; });
  var seen = {};
  var out = header('DetermineBasalData', 'oref0 determine-basal.test.js: every determine_basal call, with inputs and oref0 output.');
  var names = [];
  calls.forEach(function (r, k) {
    var ids = testId('determine-basal.test.js', r.test);
    var n = (seen[r.test] = (seen[r.test] || 0) + 1);
    var id = ids.length > 1 ? ids[Math.min(n, ids.length) - 1] : ids[0];
    if (ids.length > 1) { seen[r.test] = n; }
    var a = r.args;
    var expected = r.threw ? null : JSON.stringify(revive(r.result));
    var nm = 'c' + String(k + 1).padStart(2, '0');
    names.push(nm);
    out += '/-- ' + id + ': ' + r.test.replace(/-\//g, '- /') + ' -/\n';
    out += 'def ' + nm + ' : DBCase where\n  id := ' + leanStr(id) + '\n  name := ' + leanStr(r.test) +
      '\n  input := ' + dbInputs(a) + '\n  expected := ' + leanStr(expected) + '\n\n';
  });
  out += 'def all : List DBCase := [' + names.join(', ') + ']\n\nend LeanAID.Conformance.DetermineBasalData\n';
  fs.writeFileSync(path.join(OUT, 'DetermineBasalData.lean'), out);
  console.log('DetermineBasalData.lean: ' + calls.length + ' cases');
}

fs.mkdirSync(OUT, { recursive: true });
genDetermineBasal();
module.exports = { num: num, optNum: optNum, profile: profile, profileBare: profileBare, fields: fields,
  leanStr: leanStr, revive: revive, testId: testId, header: header, isUndef: isUndef, currentTemp: currentTemp };
