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
  out += 'def all : List DBCase := [' + names.join(', ') + ']\n\n';
  // tests disabled upstream: inputs replayed through Node by scripts/capture/disabled.js
  var dis = JSON.parse(fs.readFileSync(path.join(CAP, 'determine-basal-disabled.json'), 'utf8'));
  var dnames = [];
  dis.forEach(function (r, k) {
    var nm = 'd' + String(k + 1).padStart(2, '0');
    dnames.push(nm);
    var expected = r.threw ? null : JSON.stringify(revive(r.result));
    out += '/-- ' + r.id + ' (disabled upstream; compared with oref0 output, not with its disabled assertions) -/\n';
    out += 'def ' + nm + ' : DBCase where\n  id := ' + leanStr(r.id) + '\n  name := ' + leanStr(r.test) +
      '\n  input := ' + dbInputs(r.args) + '\n  expected := ' + leanStr(expected) + '\n\n';
  });
  out += 'def disabled : List DBCase := [' + dnames.join(', ') + ']\n\nend LeanAID.Conformance.DetermineBasalData\n';
  fs.writeFileSync(path.join(OUT, 'DetermineBasalData.lean'), out);
  console.log('DetermineBasalData.lean: ' + calls.length + ' cases + ' + dis.length + ' disabled');
}

fs.mkdirSync(OUT, { recursive: true });
genDetermineBasal();
module.exports = { num: num, optNum: optNum, profile: profile, profileBare: profileBare, fields: fields,
  leanStr: leanStr, revive: revive, testId: testId, header: header, isUndef: isUndef, currentTemp: currentTemp };

// ---- IOB ---------------------------------------------------------------------
var tz = require(path.join(ROOT, 'vendor/oref0/node_modules/moment-timezone'));
function msOf(s) {
  if (isUndef(s) || s === null) return 'none';
  var t = new Date(tz(s)).getTime();
  return isNaN(t) ? 'none' : 'some (' + t + ' : Int)';
}
function pumpFields(r) {
  return [['type_', optStr(r._type)], ['eventType', optStr(r.eventType)], ['enteredBy', optStr(r.enteredBy)],
    ['timestamp', optStr(r.timestamp)], ['timestampMs', typeof r.timestamp === 'string' ? msOf(r.timestamp) : 'none'],
    ['created_at', optStr(r.created_at)], ['created_atMs', typeof r.created_at === 'string' ? msOf(r.created_at) : 'none'],
    ['amount', optNum(r.amount)], ['insulin', optNum(r.insulin)], ['rate', optNum(r.rate)], ['absolute', optNum(r.absolute)],
    ['duration', optNum(r.duration)], ['durationNull', r.duration === null ? 'true' : 'none'],
    ['durationMin', optNum(r['duration (min)'])], ['temp', optStr(r.temp)]];
}
function pumpRecord(r) {
  var pairs = pumpFields(r);
  if (r.bolus && typeof r.bolus === 'object') pairs.push(['bolus', 'some ' + fields(pumpFields(r.bolus))]);
  return fields(pairs);
}
function jnum(v) { return (typeof v === 'number' && isFinite(v)) ? num(v) : '.nan'; }
function sumTuple(s) {
  return '(' + [s.iob, s.activity, s.basaliob, s.bolusiob, s.netbasalinsulin, s.bolusinsulin].map(jnum).join(', ') + ')';
}
function genIob() {
  var recs = JSON.parse(fs.readFileSync(path.join(CAP, 'iob.json'), 'utf8'));
  var calls = recs.filter(function (r) { return r.fn === 'iob'; });
  var out = header('IobData', 'oref0 iob.test.js: every call of lib/iob (generate), with inputs and oref0 output.');
  var names = [];
  calls.forEach(function (r, k) {
    var inp = r.args[0];
    var ids = testId('iob.test.js', r.test);
    var nm = 'c' + String(k + 1).padStart(2, '0');
    names.push(nm);
    var clockMs = new Date(tz(inp.clock)).getTime();
    var hist = (inp.history || []).map(pumpRecord);
    var h24 = Array.isArray(inp.history24) ? 'some [' + inp.history24.map(pumpRecord).join(',\n      ') + ']' : 'none';
    var res = r.result;
    var ticks = res.map(function (t) { return '(' + sumTuple(t) + ', ' + sumTuple(t.iobWithZeroTemp) + ')'; });
    var lt = res[0].lastTemp || {};
    out += '/-- ' + (ids[0] || '?') + ': ' + r.test + ' -/\ndef ' + nm + ' : IobCase where\n  id := ' + leanStr(ids[0] || '?') +
      '\n  name := ' + leanStr(r.test) +
      '\n  input := {\n    history := [' + hist.join(',\n      ') + '],\n    history24 := ' + h24 +
      ',\n    profile := ' + profileBare(inp.profile) +
      ',\n    autosens := ' + autosens(inp.autosens) + ',\n    clockMs := ' + clockMs + ' }' +
      '\n  currentIOBOnly := ' + (r.args[1] === true ? 'true' : 'false') +
      '\n  ticks := [' + ticks.join(',\n    ') + ']' +
      '\n  lastBolusTime := ' + jnum(res[0].lastBolusTime) +
      '\n  lastTempDate := ' + jnum(typeof lt.date === 'number' ? lt.date : (lt.date ? new Date(lt.date).getTime() : NaN)) +
      '\n  lastTempRate := ' + optNum(lt.rate) + '\n  lastTempDuration := ' + optNum(lt.duration) + '\n\n';
  });
  out += 'def all : List IobCase := [' + names.join(', ') + ']\n\nend LeanAID.Conformance.IobData\n';
  fs.writeFileSync(path.join(OUT, 'IobData.lean'), out);
  console.log('IobData.lean: ' + calls.length + ' cases');
}
genIob();

// ---- small suites --------------------------------------------------------------
function optOptNum(v) { return optNum(v); }
function resultIn(r) {
  if (isUndef(r) || r === null) return '{}';
  return fields([['reason', typeof r.reason === 'string' ? 'some ' + leanStr(r.reason) : 'none'],
                 ['rate', optNum(r.rate)], ['duration', optNum(r.duration)]]);
}
function genSmall() {
  var out = header('SmallData', 'oref0 round_basal, setTempBasal, basal, get-last-glucose and cobhistory tests: inputs and oref0 outputs.');
  // round_basal
  var rb = JSON.parse(fs.readFileSync(path.join(CAP, 'determine-basal.json'), 'utf8')).filter(function (r) { return r.fn === 'round_basal'; });
  out += 'def roundBasal : List RBCase := [\n' + rb.map(function (r) {
    var ids = testId('determine-basal.test.js', r.test);
    var model = (r.args[1] && typeof r.args[1].model === 'string') ? 'some ' + leanStr(r.args[1].model) : 'none';
    return '  { id := ' + leanStr(ids[0]) + ', name := ' + leanStr(r.test) + ', basal := ' + num(r.args[0]) +
      ', model := ' + model + ', expected := ' + num(r.result) + ' }';
  }).join(',\n') + ']\n\n';
  // setTempBasal
  var st = JSON.parse(fs.readFileSync(path.join(CAP, 'set-temp-basal.json'), 'utf8')).filter(function (r) { return r.fn === 'setTempBasal'; });
  out += 'def setTempBasal : List STBCase := [\n' + st.map(function (r) {
    var ids = testId('set-temp-basal.test.js', r.test);
    var a = r.args, res = r.result || {};
    return '  { id := ' + leanStr(ids[0]) + ', name := ' + leanStr(r.test) + ',\n    rate := ' + num(a[0]) + ', duration := ' + num(a[1]) +
      ',\n    profile := ' + profileBare(a[2]) + ',\n    rT := ' + resultIn(a[3]) + ',\n    currenttemp := ' + currentTemp(a[4]) +
      ',\n    expRate := ' + optNum(res.rate) + ', expDuration := ' + optNum(res.duration) +
      ', expReason := ' + (typeof res.reason === 'string' ? 'some ' + leanStr(res.reason) : 'none') + ' }';
  }).join(',\n') + ']\n\n';
  // basal
  var bs = JSON.parse(fs.readFileSync(path.join(CAP, 'basal.json'), 'utf8'));
  var sched = function (xs) { return '[' + xs.map(function (b) { return fields([['i', optNum(b.i)], ['minutes', num(b.minutes)], ['rate', num(b.rate)]]); }).join(', ') + ']'; };
  out += 'def basalLookup : List BasalLookupCase := [\n' + bs.filter(function (r) { return r.fn === 'basalLookup'; }).map(function (r) {
    return '  { id := "BAS-02", schedule := ' + sched(r.args[0]) + ', nowMs := ' + r.args[1].__date + ', expected := ' + optNum(r.result) + ' }';
  }).join(',\n') + ']\n\n';
  out += 'def maxDailyBasal : List MaxDailyCase := [\n' + bs.filter(function (r) { return r.fn === 'maxDailyBasal'; }).map(function (r) {
    return '  { id := "BAS-01", basals := ' + sched(r.args[0].basals) + ', expected := ' + num(r.result) + ' }';
  }).join(',\n') + ']\n\n';
  // get-last-glucose
  var gl = JSON.parse(fs.readFileSync(path.join(CAP, 'get-last-glucose.json'), 'utf8')).filter(function (r) { return r.fn === 'getLastGlucose'; });
  var parse = function (s) { if (typeof s !== 'string') return 'none'; var t = Date.parse(s); return isNaN(t) ? 'none' : 'some ' + num(t); };
  out += 'def getLastGlucose : List GLGCase := [\n' + gl.map(function (r) {
    var ids = testId('get-last-glucose.test.js', r.test);
    var entries = r.args[0].map(function (e) {
      return fields([['glucose', optNum(e.glucose)], ['sgv', optNum(e.sgv)], ['noise', optNum(e.noise)], ['type_', optStr(e.type)],
        ['device', optStr(e.device)], ['date', optNum(e.date)], ['displayTimeMs', parse(e.display_time)], ['dateStringMs', parse(e.dateString)]]);
    });
    var g = revive(r.result);
    return '  { id := ' + leanStr(ids[0]) + ', name := ' + leanStr(r.test) + ',\n    entries := [' + entries.join(',\n      ') + '],\n    expected := ' +
      leanStr(JSON.stringify(g)) + ' }';
  }).join(',\n') + ']\n\n';
  // cobhistory
  var ch = JSON.parse(fs.readFileSync(path.join(CAP, 'cobhistory.json'), 'utf8')).filter(function (r) { return r.fn === 'findMealInputs'; });
  var dms = function (s) { if (typeof s !== 'string') return 'none'; var t = new Date(s).getTime(); return isNaN(t) ? 'none' : 'some (' + t + ' : Int)'; };
  out += 'def cobHistory : List COBHCase := [\n' + ch.map(function (r) {
    var ids = testId('cobhistory.test.js', r.test);
    var ph = (r.args[0].history || []).map(function (e) {
      var base = fields([['type_', optStr(e._type)], ['enteredBy', optStr(e.enteredBy)], ['timestamp', optStr(e.timestamp)],
        ['timestampMs', dms(e.timestamp)], ['created_at', optStr(e.created_at)], ['created_atMs', dms(e.created_at)],
        ['amount', optNum(e.amount)], ['insulin', optNum(e.insulin)]]);
      return fields([['base', base], ['carbs', optNum(e.carbs)], ['carb_input', optNum(e.carb_input)]]);
    });
    var cr = (r.args[0].carbs || []).map(function (e) {
      return fields([['carbs', optNum(e.carbs)], ['created_at', optStr(e.created_at)], ['created_atMs', dms(e.created_at)]]);
    });
    var exp = r.result.map(function (m) {
      return fields([['timestamp', optStr(m.timestamp)], ['timestampMs', dms(m.timestamp)], ['carbs', optNum(m.carbs)],
        ['nsCarbs', optNum(m.nsCarbs)], ['bwCarbs', optNum(m.bwCarbs)], ['journalCarbs', optNum(m.journalCarbs)], ['bolus', optNum(m.bolus)]]);
    });
    return '  { id := ' + leanStr(ids[0]) + ', name := ' + leanStr(r.test) + ',\n    pump := [' + ph.join(',\n      ') +
      '],\n    carbs := [' + cr.join(', ') + '],\n    expected := [' + exp.join(',\n      ') + '] }';
  }).join(',\n') + ']\n\nend LeanAID.Conformance.SmallData\n';
  fs.writeFileSync(path.join(OUT, 'SmallData.lean'), out);
  console.log('SmallData.lean: ' + rb.length + ' round_basal, ' + st.length + ' setTempBasal, ' + bs.length + ' basal, ' + gl.length + ' glucose, ' + ch.length + ' cobhistory');
}
genSmall();
