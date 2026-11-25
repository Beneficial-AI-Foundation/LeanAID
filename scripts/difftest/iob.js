#!/usr/bin/env node
// Differential test of insulin on board, meal history and the basal schedule: oref0's
// lib/iob (`generate`), lib/meal/history.js (`findMealInputs`) and lib/profile/basal.js
// (`basalLookup`) against the Lean core through `aid-lean iob-batch` (App/IobBatch.lean).
//
//   TZ=UTC node scripts/difftest/iob.js [N=100000] [seed=1]
//   TZ=UTC node scripts/difftest/iob.js --file cases.jsonl     (the cases of a file instead)
//   ... --fixed   the corrected IOB (docs/FIXED.md) against oref0 and the patched oref0
// aid-lean runs in IOB_JOBS parallel processes (default: number of CPUs minus 2).
//
// Generates N random, well-formed pump histories, carb histories and profiles (seeded,
// reproducible; see genCase), runs oref0 in-process and aid-lean on each, and compares
//   - the whole IOB array (every field of every element, iobWithZeroTemp, lastBolusTime,
//     lastTemp), as JSON.stringify prints it;
//   - the meal inputs found in the histories;
//   - basalLookup at several times, on the profile's schedule and on random ones.
// The comparison ignores the order of keys in objects; values must be identical. A case that
// differs is counted as "at a rounding tie" if one of oref0's Math.round calls had an argument
// within 1e-9 (relative) of a .5 tie, exactly as scripts/difftest/run.js counts them.
// Writes docs/iobtest.json (summary; not with --file) and scripts/difftest/out/iob-mismatches.jsonl
// (iob-file-mismatches.jsonl with --file).
// Exit code 1 if any case differs without a rounding tie.
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var fs = require('fs');
var path = require('path');
var cp = require('child_process');
var common = require('./common');
var ROOT = common.ROOT;
var O = path.join(ROOT, 'vendor/oref0');
var generateIob = require(path.join(O, 'lib/iob'));
var findMeals = require(path.join(O, 'lib/meal/history'));
var basalLookup = require(path.join(O, 'lib/profile/basal')).basalLookup;

if (process.env.TZ !== 'UTC') { console.error('run with TZ=UTC'); process.exit(1); }
// --fixed: compare `aid-lean iob-batch --fixed` (the corrected IOB, docs/FIXED.md) with oref0 and
// with the patched copy of scripts/fixes/apply.sh; write docs/iobtest-fixed.json instead.
var FIXED = process.argv.indexOf('--fixed') >= 0;
process.argv = process.argv.filter(function (a) { return a !== '--fixed'; });
var fileMode = process.argv[2] === '--file';
var N = fileMode ? 0 : parseInt(process.argv[2] || '100000', 10);
var seed = fileMode ? 0 : parseInt(process.argv[3] || '1', 10);
var P = FIXED ? {
  generateIob: require(path.join(common.FIXED_OREF0, 'lib/iob')),
  findMeals: require(path.join(common.FIXED_OREF0, 'lib/meal/history')),
  basalLookup: require(path.join(common.FIXED_OREF0, 'lib/profile/basal')).basalLookup } : null;
var seed0 = seed;

// mulberry32, as in scripts/difftest/run.js
function rng() { seed |= 0; seed = seed + 0x6D2B79F5 | 0; var t = Math.imul(seed ^ seed >>> 15, 1 | seed);
  t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }
function uni(a, b, d) { var x = a + rng() * (b - a); var f = Math.pow(10, d || 0); return Math.round(x * f) / f; }
function int(a, b) { return a + Math.floor(rng() * (b - a + 1)); }
function pick(xs) { return xs[Math.floor(rng() * xs.length)]; }
function chance(p) { return rng() < p; }
function copy(x) { return x === undefined ? undefined : JSON.parse(JSON.stringify(x)); }

var MIN = 60000, HOUR = 3600000;
var DAY0 = Date.UTC(2026, 10, 18);

function pad(n, w) { var s = String(Math.abs(n)); while (s.length < w) s = '0' + s; return s; }
// An ISO-8601 time with a zone offset of `off` minutes, as Medtronic pump records have it
// ("2017-10-05T22:06:31-07:00"); the instant is t.
function isoOff(t, off) {
  var d = new Date(t + off * MIN);
  var s = d.getUTCFullYear() + '-' + pad(d.getUTCMonth() + 1, 2) + '-' + pad(d.getUTCDate(), 2) + 'T' +
    pad(d.getUTCHours(), 2) + ':' + pad(d.getUTCMinutes(), 2) + ':' + pad(d.getUTCSeconds(), 2);
  return s + (off === 0 && chance(0.5) ? 'Z' : (off < 0 ? '-' : '+') + pad(Math.floor(Math.abs(off) / 60), 2) + ':' + pad(Math.abs(off) % 60, 2));
}
// A Nightscout `created_at` ("2017-10-06T05:06:31.000Z")
function nsTime(t) { return new Date(t).toISOString(); }

// A basal schedule as lib/profile reads it from the pump: entries {i, start, minutes, rate}.
function genSchedule() {
  var n = pick([1, 1, 2, 3, 3, 4, 5, 6, 8]);
  var mins = [0];
  while (mins.length < n) {
    var m = chance(0.8) ? 30 * int(1, 47) : int(1, 1439);
    if (mins.indexOf(m) < 0) mins.push(m);
  }
  mins.sort(function (a, b) { return a - b; });
  var s = mins.map(function (m, i) {
    var rate = chance(0.5) ? uni(0.05, 3, 2) : Math.round(uni(0.025, 2.5, 3) * 40) / 40;
    return { i: i, start: pad(Math.floor(m / 60), 2) + ':' + pad(m % 60, 2) + ':00', minutes: m, rate: Math.max(0.025, rate) };
  });
  if (chance(0.03)) s[s.length - 1].rate = 0;          // FINDINGS F-22: last entry with rate 0
  if (chance(0.05)) s[int(0, s.length - 1)].rate = 0;  // a zero entry elsewhere
  if (chance(0.1)) {                                    // entries not in `i` order in the array
    for (var k = s.length - 1; k > 0; k--) { var j = int(0, k); var x = s[k]; s[k] = s[j]; s[j] = x; }
  }
  return s;
}

// Lines of the history: each generator returns an array of records (newest last here; the
// whole history is reversed at the end, since pump histories are newest first).
function genCase() {
  var sched = genSchedule();
  // now: anywhere in the day, just after midnight, or just after a schedule entry
  var now, r = rng();
  if (r < 0.55) now = DAY0 + int(0, 86399) * 1000;
  else if (r < 0.7) now = DAY0 + 86400000 + int(0, 900) * 1000;            // 00:00-00:15 the next day
  else if (r < 0.9) now = DAY0 + pick(sched).minutes * MIN + int(0, 600) * 1000;
  else now = DAY0 + int(0, 1439) * MIN + pick([0, 30000]);                // on a minute or half minute
  var off = pick([0, 0, 0, -300, -420, 60, 120, 330]);                     // the pump's zone in its timestamps
  var clock = r < 0.98 ? (chance(0.5) ? nsTime(now) : isoOff(now, off)) : isoOff(now, 0).replace(/(Z|[+-]\d\d:\d\d)$/, '');

  var curve = pick([undefined, 'bilinear', 'bilinear', 'rapid-acting', 'rapid-acting', 'ultra-rapid', 'ultra-rapid',
    'Rapid-Acting', 'ULTRA-RAPID', 'humalog']);
  var profile = {
    dia: pick([2, 3, 3, 3.5, 4, 4, 5, 5, 6, 7]),
    basalprofile: sched,
    current_basal: chance(0.9) ? Math.max(0.025, pick(sched).rate) : uni(0.1, 2, 2),
    max_daily_basal: Math.max.apply(null, sched.map(function (e) { return e.rate; })),
    max_basal: 4,
    suspend_zeros_iob: chance(0.5) ? true : (chance(0.5) ? false : undefined)
  };
  if (curve !== undefined) profile.curve = curve;
  if (chance(0.03)) delete profile.basalprofile;        // no schedule: current_basal is used
  if (chance(0.5)) { profile.useCustomPeakTime = chance(0.8); profile.insulinPeakTime = pick([20, 30, 35, 40, 45, 50, 55, 60, 75, 90, 100, 110, 120, 130, 150]); }
  if (chance(0.9)) { profile.min_bg = uni(80, 140, 0); profile.max_bg = profile.min_bg + uni(0, 40, 0); }
  if (chance(0.3)) profile.half_basal_exercise_target = pick([120, 140, 160, 200]);
  if (chance(0.3)) profile.exercise_mode = chance(0.7);
  if (chance(0.3)) profile.temptargetSet = chance(0.7);
  if (profile.temptargetSet && chance(0.5)) { profile.min_bg = uni(100, 160, 0); profile.max_bg = profile.min_bg; }
  Object.keys(profile).forEach(function (k) { if (profile[k] === undefined) delete profile[k]; });
  var autosens = chance(0.5) ? { ratio: uni(0.7, 1.3, 2) } : undefined;

  var recs = [];        // [time, record]
  var carbs = [];       // carbhistory (Nightscout carb entries)
  var span = pick([3, 6, 9, 10]) * HOUR;
  function ts(t) { return isoOff(t, off); }
  function randT() { return now - Math.floor(rng() * span / 1000) * 1000; }
  // temp basals as Medtronic records, in sequence from the past to now
  var t = now - span + int(0, 60) * MIN;
  var nTemps = pick([0, 2, 5, 10, 20, 40]);
  for (var k = 0; k < nTemps && t < now; k++) {
    var dur = pick([0, 30, 30, 30, 60, 90, 120, 240, int(1, 29), int(31, 180), 5 * int(1, 48)]);
    var rate = pick([0, 0, uni(0, 4, 2), Math.round(uni(0, 3, 2) * 40) / 40, uni(0, 1, 1)]);
    var tstamp = ts(t);
    var tb = { _type: 'TempBasal', temp: chance(0.03) ? 'percent' : 'absolute', rate: rate, timestamp: tstamp };
    var td = { _type: 'TempBasalDuration', 'duration (min)': dur, timestamp: tstamp };
    var order = rng();
    if (order < 0.02) recs.push([t, tb]);                       // no duration record
    else if (order < 0.6) { recs.push([t, tb]); recs.push([t, td]); }   // reversed later: duration first
    else { recs.push([t, td]); recs.push([t, tb]); }
    t += (chance(0.7) ? Math.min(dur, 30) : int(1, Math.max(1, dur + 20))) * MIN + int(0, 59) * 1000;
  }
  // boluses: Medtronic, SMB-sized or meal-sized
  var nBol = pick([0, 1, 2, 4, 8, 15]);
  for (k = 0; k < nBol; k++) {
    var bt = randT(), amt = chance(0.5) ? uni(0.1, 1, 1) : uni(0.5, 8, 1);
    var b = { _type: 'Bolus', amount: amt, programmed: amt, unabsorbed: 0, duration: 0, timestamp: ts(bt) };
    if (chance(0.15)) {   // a bolus wizard record for it, with the same timestamp
      var bw = { _type: 'BolusWizard', timestamp: ts(bt), carb_input: chance(0.2) ? 0 : uni(5, 80, 0) };
      if (chance(0.3)) bw.bolus = { _type: 'Bolus', amount: amt, timestamp: ts(bt) };
      recs.push([bt, bw]);
    }
    recs.push([bt, b]);
  }
  // a bolus exactly DIA hours ago, give or take 40 s (the end of the insulin curves)
  if (chance(0.1)) {
    var diaEff = Math.max(profile.dia, 3);
    bt = now - Math.round(diaEff * 3600) * 1000 + int(-40, 40) * 1000;
    recs.push([bt, { _type: 'Bolus', amount: uni(0.5, 3, 1), programmed: 1, unabsorbed: 0, duration: 0, timestamp: ts(bt) }]);
    if (diaEff < 5) {
      bt = now - 5 * 3600 * 1000 + int(-40, 40) * 1000;
      recs.push([bt, { _type: 'Bolus', amount: uni(0.5, 3, 1), programmed: 1, unabsorbed: 0, duration: 0, timestamp: ts(bt) }]);
    }
  }
  // bolus wizard without a bolus
  if (chance(0.1)) { bt = randT(); recs.push([bt, { _type: 'BolusWizard', timestamp: ts(bt), carb_input: pick([0, 30]) }]); }
  // a bolus in the future
  if (chance(0.05)) { bt = now + int(1, 30) * MIN; recs.push([bt, { _type: 'Bolus', amount: 1, programmed: 1, unabsorbed: 0, duration: 0, timestamp: ts(bt) }]); }
  // suspends and resumes
  if (chance(0.35)) {
    var pat = pick(['pairs', 'pairs', 'resumeFirst', 'suspendLast', 'both', 'extraSuspend', 'extraResume', 'random']);
    var st = now - span + int(0, 120) * MIN;
    if (pat === 'random') {               // any sequence of suspends and resumes
      var ne = int(1, 5);
      for (k = 0; k < ne && st < now; k++) {
        recs.push([st, { _type: chance(0.5) ? 'PumpSuspend' : 'PumpResume', timestamp: ts(st) }]);
        st += int(1, 90) * MIN + int(0, 59) * 1000;
      }
      pat = 'none';
    }
    if (pat === 'none') { /* done */ } else if (pat === 'resumeFirst' || pat === 'both' || pat === 'extraResume') {
      recs.push([st, { _type: 'PumpResume', timestamp: ts(st) }]); st += int(5, 90) * MIN;
    }
    var np = pat === 'none' ? 0 : int(1, 3);
    for (k = 0; k < np && st < now; k++) {
      recs.push([st, { _type: 'PumpSuspend', timestamp: ts(st) }]);
      if (pat === 'extraSuspend' && k === 0) { st += int(1, 10) * MIN; recs.push([st, { _type: 'PumpSuspend', timestamp: ts(st) }]); }
      st += int(1, 120) * MIN + int(0, 59) * 1000;
      if (st >= now) break;
      if (!((pat === 'suspendLast' || pat === 'both') && k === np - 1)) {
        recs.push([st, { _type: 'PumpResume', timestamp: ts(st) }]);
        if (pat === 'extraResume' && k === 0) { st += int(1, 10) * MIN; recs.push([st, { _type: 'PumpResume', timestamp: ts(st) }]); }
      }
      st += int(5, 180) * MIN;
    }
  }
  // Nightscout treatments merged into the pump history (Care Portal, xDrip, HAPP, AndroidAPS, Loop)
  var nNs = pick([0, 0, 0, 1, 3, 6]);
  for (k = 0; k < nNs; k++) {
    var nt = randT(), ca = nsTime(nt), kind = int(0, 10), rec;
    if (kind === 0) rec = { eventType: pick(['Meal Bolus', 'Correction Bolus', 'Snack Bolus', 'Bolus Wizard']), insulin: uni(0.5, 6, 1), carbs: chance(0.5) ? uni(5, 60, 0) : undefined, created_at: ca, enteredBy: 'careportal' };
    else if (kind === 1) rec = { enteredBy: 'xdrip', insulin: uni(0.5, 5, 1), carbs: chance(0.5) ? uni(5, 60, 0) : undefined, created_at: ca, eventType: '<none>' };
    else if (kind === 2) rec = { enteredBy: 'HAPP_App', insulin: chance(0.8) ? uni(0.5, 5, 1) : 0, created_at: ca, eventType: 'Bolus' };
    else if (kind === 3) rec = { eventType: 'Temp Basal', enteredBy: pick(['HAPP_App', 'openaps://AndroidAPS']), absolute: uni(0, 3, 2), rate: uni(0, 3, 2), duration: pick([30, 60, 15, 120]), created_at: ca };
    else if (kind === 4) rec = { eventType: 'Temp Basal', enteredBy: 'openaps://AndroidAPS', created_at: ca, duration: null };   // a cancel record
    else if (kind === 5) rec = { eventType: 'Temp Basal', enteredBy: 'loop://iPhone', rate: uni(0, 3, 2), duration: pick([30, 30, 12.5, 45]), amount: chance(0.6) ? uni(0, 1.5, 3) : undefined, created_at: ca, timestamp: ca };
    else if (kind === 6) rec = { eventType: 'Carb Correction', _type: chance(0.5) ? 'Carb Correction' : undefined, carbs: uni(5, 40, 0), created_at: ca };
    else if (kind === 7) rec = { _type: pick(['Meal Bolus', 'Correction Bolus', 'Snack Bolus', 'Bolus Wizard']), carbs: chance(0.7) ? uni(5, 60, 0) : undefined, insulin: uni(0.5, 5, 1), created_at: ca };
    else if (kind === 8) rec = { eventType: 'Note', carbs: uni(1, 50, 0), insulin: chance(0.3) ? 1 : undefined, created_at: ca };
    else if (kind === 9) rec = { _type: 'JournalEntryMealMarker', carb_input: pick([0, uni(5, 80, 0)]), timestamp: ts(nt) };
    else rec = { _type: pick(['Prime', 'BasalProfileStart', 'Rewind', 'CalBGForPH']), timestamp: ts(nt), amount: 0.5 };
    if (rec.created_at && !rec.timestamp && chance(0.3)) rec.timestamp = chance(0.5) ? rec.created_at : ts(nt);  // uploaders that send both
    Object.keys(rec).forEach(function (key) { if (rec[key] === undefined) delete rec[key]; });
    recs.push([nt, rec]);
  }
  // carb entries in Nightscout, with exact and near (< 2 s) duplicates
  var nC = pick([0, 0, 1, 2, 4]);
  for (k = 0; k < nC; k++) {
    var ct = randT();
    carbs.push({ carbs: chance(0.1) ? 0 : uni(5, 80, 0), created_at: nsTime(ct), enteredBy: 'careportal' });
    if (chance(0.2)) carbs.push({ carbs: uni(5, 80, 0), created_at: nsTime(ct + pick([0, 1000, -1500, 2000, 2500])), enteredBy: 'xdrip' });
    if (chance(0.1)) recs.push([ct, { eventType: 'Meal Bolus', carbs: uni(5, 80, 0), insulin: 1, created_at: isoOff(ct + pick([0, 1000]), off) }]);
    // the same meal again in the pump history, as the other record kinds lib/meal reads
    if (chance(0.15)) {
      var dt = ct + pick([0, 0, 1000, -1000, 3000]), dk = int(0, 3), dup;
      if (dk === 0) dup = { _type: pick(['Meal Bolus', 'Carb Correction']), carbs: uni(5, 80, 0), created_at: nsTime(dt) };
      else if (dk === 1) dup = { enteredBy: 'xdrip', carbs: uni(5, 80, 0), insulin: 1, created_at: nsTime(dt), timestamp: nsTime(dt) };
      else if (dk === 2) dup = { eventType: 'Note', carbs: uni(5, 80, 0), created_at: nsTime(dt), timestamp: ts(dt) };
      else dup = { _type: 'JournalEntryMealMarker', carb_input: uni(5, 80, 0), timestamp: ts(dt) };
      recs.push([dt, dup]);
    }
  }

  // pump history: newest first; a few records out of order
  recs.sort(function (a, b) { return b[0] - a[0]; });
  var history = recs.map(function (x) { return x[1]; });
  if (chance(0.05) && history.length > 3) { var i = int(1, history.length - 2); var y = history[i]; history[i] = history[i + 1]; history[i + 1] = y; }
  var history24;
  if (chance(0.1) && history.length > 2) {       // the last 24 h in a second file, overlapping the first
    var cut = int(1, history.length - 1);
    history24 = history.slice(Math.max(0, cut - 2));
    history = history.slice(0, cut);
  }

  // basal lookups: the profile's schedule and a random one, at several times
  var lookups = [];
  for (k = 0; k < 6; k++) {
    var s = k < 4 ? sched : genSchedule();
    var lt = chance(0.5) ? DAY0 + int(0, 1439) * MIN + pick([0, 0, 59999, int(0, 59) * 1000]) : DAY0 + pick(s).minutes * MIN + pick([-1, 0, 1, 60000]);
    lookups.push({ schedule: s, t: chance(0.01) ? null : lt });   // null: basalLookup(schedule) with no time
  }

  var c = { pumphistory: history, carbhistory: carbs, profile: profile, clock: clock, lookups: lookups };
  if (history24) c.history24 = history24;
  if (autosens) c.autosens = autosens;
  if (chance(0.05)) c.currentIOBOnly = true;
  return c;
}

// oref0 on one case. Returns the outputs and the case as aid-lean gets it (a lookup with no
// time gets the time at which basalLookup ran, read with Date.now() on both sides of the call).
function runNode(c) {
  common.resetNearTie();
  var inputs = { history: copy(c.pumphistory), profile: copy(c.profile), clock: c.clock };
  if (c.history24) inputs.history24 = copy(c.history24);
  if (c.autosens) inputs.autosens = copy(c.autosens);
  var iob = copy(generateIob(inputs, c.currentIOBOnly));
  var meal = copy(findMeals({ history: copy(c.pumphistory), carbs: copy(c.carbhistory), profile: copy(c.profile) }));
  var leanCase = copy(c);
  var basal = c.lookups.map(function (l, k) {
    var v;
    if (l.t === null) {
      var t0, t1;
      do { t0 = Date.now(); v = basalLookup(copy(l.schedule)); t1 = Date.now(); }
      while (Math.floor(t0 / MIN) !== Math.floor(t1 / MIN));
      leanCase.lookups[k].t = t0;
    } else v = basalLookup(copy(l.schedule), new Date(l.t));
    return v === undefined ? null : v;
  });
  var patched = null;
  if (FIXED) {
    var pin = { history: copy(c.pumphistory), profile: copy(c.profile), clock: c.clock };
    if (c.history24) pin.history24 = copy(c.history24);
    if (c.autosens) pin.autosens = copy(c.autosens);
    patched = { iob: copy(P.generateIob(pin, c.currentIOBOnly)),
      meal: copy(P.findMeals({ history: copy(c.pumphistory), carbs: copy(c.carbhistory), profile: copy(c.profile) })),
      basal: leanCase.lookups.map(function (l) { var v = P.basalLookup(copy(l.schedule), new Date(l.t)); return v === undefined ? null : v; }) };
  }
  return { out: { iob: iob, meal: meal, basal: basal }, nearTie: common.sawNearTie(), leanCase: leanCase, patched: patched };
}

// JSON with the keys of every object sorted.
function canon(x) {
  if (Array.isArray(x)) return '[' + x.map(canon).join(',') + ']';
  if (x !== null && typeof x === 'object') {
    return '{' + Object.keys(x).sort().map(function (k) { return JSON.stringify(k) + ':' + canon(x[k]); }).join(',') + '}';
  }
  return JSON.stringify(x);
}

var OUT = path.join(__dirname, 'out');
fs.mkdirSync(OUT, { recursive: true });
// separate scratch files for --file, so that check.sh can run while a random run is going
var TAG = fileMode ? 'iob-file' : 'iob';
var casesFile = path.join(OUT, TAG + '-chunk.jsonl');
var JOBS = parseInt(process.env.IOB_JOBS || String(Math.max(1, require('os').cpus().length - 2)), 10);
var stats = { cases: 0, seed: fileMode ? null : seed0, file: fileMode ? process.argv[3] : null,
  identical: 0, mismatchWithNearTie: 0, mismatchWithoutNearTie: 0, casesWithNearTie: 0,
  partsDiffering: { iob: 0, meal: 0, basal: 0 },
  exercised: { suspendZerosIob: 0, withSuspends: 0, history24: 0, currentIOBOnly: 0, exponential: 0, withCarbs: 0,
    unzonedClock: 0, lookupsWithoutTime: 0, lookupsUndefined: 0 },
  jobs: JOBS, nodeSeconds: 0, aidLeanSeconds: 0, aidLeanCpuSeconds: 0 };
if (FIXED) {
  stats.fixedVsOref0 = { identical: 0, differ: 0, differWithTrigger: 0, differWithoutTrigger: 0, triggerButIdentical: 0 };
  stats.fixedVsPatchedJs = { identical: 0, differ: 0 };
  stats.f24 = { cases: 0, differ: 0, iobTicksDiffering: 0, maxIobDiff: 0, maxZeroTempIobDiff: 0,
    fixedIobHigher: 0, fixedIobLower: 0, maxIobDiffCase: null };
  TAG += '-fixed';
}
var mm = fs.openSync(path.join(OUT, TAG + '-mismatches.jsonl'), 'w');

// `aid-lean iob-batch` on the lines, split over JOBS processes; one output line per input line.
function runLean(lines) {
  var per = Math.ceil(lines.length / JOBS), parts = [];
  for (var j = 0; j * per < lines.length; j++) parts.push(lines.slice(j * per, (j + 1) * per));
  return Promise.all(parts.map(function (part, j) {
    var f = casesFile.replace(/\.jsonl$/, '-' + j + '.jsonl');
    fs.writeFileSync(f, part.join('\n') + '\n');
    return new Promise(function (resolve, reject) {
      var t0 = Date.now();
      cp.execFile((process.env.AID_LEAN || path.join(ROOT, '.lake/build/bin/aid-lean')), FIXED ? ['iob-batch', f, '--fixed'] : ['iob-batch', f], { encoding: 'utf8', maxBuffer: 1 << 30 },
        function (err, out) {
          if (err) return reject(err);
          stats.aidLeanCpuSeconds += (Date.now() - t0) / 1000;
          resolve(out.split('\n').slice(0, part.length));
        });
    });
  })).then(function (outs) { return [].concat.apply([], outs); });
}

function runChunk(cases, base) {
  var t0 = Date.now();
  var res = cases.map(function (c) { return common.quietly(function () { return runNode(c); }); });
  stats.nodeSeconds += (Date.now() - t0) / 1000;
  t0 = Date.now();
  return runLean(res.map(function (r) { return JSON.stringify(r.leanCase); })).then(function (lean) {
  stats.aidLeanSeconds += (Date.now() - t0) / 1000;
  res.forEach(function (r, n) {
    var c = cases[n];
    stats.cases++;
    if (c.profile.suspend_zeros_iob) stats.exercised.suspendZerosIob++;
    if (c.pumphistory.concat(c.history24 || []).some(function (h) { return h._type === 'PumpSuspend' || h._type === 'PumpResume'; })) stats.exercised.withSuspends++;
    if (c.history24) stats.exercised.history24++;
    if (c.currentIOBOnly) stats.exercised.currentIOBOnly++;
    if (c.profile.curve && c.profile.curve.toLowerCase() !== 'bilinear') stats.exercised.exponential++;
    if (r.out.meal.length) stats.exercised.withCarbs++;
    if (!/(Z|[+-][0-2][0-9]:?[034][05])+/.test(c.clock)) stats.exercised.unzonedClock++;
    c.lookups.forEach(function (l, k) { if (l.t === null) stats.exercised.lookupsWithoutTime++; if (r.out.basal[k] === null) stats.exercised.lookupsUndefined++; });
    if (r.nearTie) stats.casesWithNearTie++;
    var lo; try { lo = JSON.parse(lean[n]); } catch (e) { lo = { unparsable: String(lean[n]) }; }
    if (FIXED) return countFixed(r, lo, base + n);
    var parts = ['iob', 'meal', 'basal'].filter(function (p) { return canon(r.out[p]) !== canon(lo[p]); });
    if (!parts.length) { stats.identical++; return; }
    if (r.nearTie) stats.mismatchWithNearTie++; else stats.mismatchWithoutNearTie++;
    parts.forEach(function (p) { stats.partsDiffering[p]++; });
    fs.writeSync(mm, JSON.stringify({ n: base + n, nearTie: r.nearTie, parts: parts, oref0: r.out, aidLean: lo, input: r.leanCase }) + '\n');
  });
  });
}

// --fixed: count one case. The corrected IOB may differ from oref0's only when the F-24 trigger
// holds (`f24` in aid-lean's output), and must equal the patched oref0's.
function countFixed(r, lo, n) {
  var trig = lo.f24 === true;
  var parts = ['iob', 'meal', 'basal'].filter(function (p) { return canon(r.out[p]) !== canon(lo[p]); });
  var partsJs = ['iob', 'meal', 'basal'].filter(function (p) { return canon(r.patched[p]) !== canon(lo[p]); });
  var bad = [];
  if (trig) stats.f24.cases++;
  if (!parts.length) { stats.identical++; stats.fixedVsOref0.identical++; if (trig) stats.fixedVsOref0.triggerButIdentical++; }
  else {
    stats.fixedVsOref0.differ++;
    parts.forEach(function (p) { stats.partsDiffering[p]++; });
    if (trig) {
      stats.fixedVsOref0.differWithTrigger++; stats.f24.differ++;
      (r.out.iob || []).forEach(function (t, k) {
        var u = (lo.iob || [])[k]; if (!u) return;
        var d = u.iob - t.iob, dz = u.iobWithZeroTemp.iob - t.iobWithZeroTemp.iob;
        if (d !== 0 || dz !== 0) stats.f24.iobTicksDiffering++;
        if (Math.abs(d) > stats.f24.maxIobDiff) { stats.f24.maxIobDiff = Math.round(Math.abs(d) * 1e4) / 1e4; stats.f24.maxIobDiffCase = n; }
        stats.f24.maxZeroTempIobDiff = Math.max(stats.f24.maxZeroTempIobDiff, Math.round(Math.abs(dz) * 1e4) / 1e4);
        if (k === 0 && d > 0) stats.f24.fixedIobHigher++;
        if (k === 0 && d < 0) stats.f24.fixedIobLower++;
      });
    } else { stats.fixedVsOref0.differWithoutTrigger++; bad.push('differs from oref0 without the F-24 trigger'); }
  }
  if (!partsJs.length) stats.fixedVsPatchedJs.identical++;
  else { stats.fixedVsPatchedJs.differ++; bad.push('differs from the patched oref0: ' + partsJs.join(',')); }
  if (bad.length) {
    if (r.nearTie) stats.mismatchWithNearTie++; else stats.mismatchWithoutNearTie++;
    fs.writeSync(mm, JSON.stringify({ n: n, problems: bad, nearTie: r.nearTie, f24: trig, oref0: r.out, patchedJs: r.patched, aidLean: lo, input: r.leanCase }) + '\n');
  }
}

var CHUNK = 5000;
var t00 = Date.now();
var chain = Promise.resolve();
if (fileMode) {
  var all = fs.readFileSync(process.argv[3], 'utf8').split('\n').filter(function (l) { return l.trim(); }).map(JSON.parse);
  for (var b = 0; b < all.length; b += CHUNK) {
    (function (b) { chain = chain.then(function () { return runChunk(all.slice(b, b + CHUNK), b); }); })(b);
  }
} else {
  // the cases are generated in order, chunk by chunk, so the run does not depend on JOBS
  for (var base = 0; base < N; base += CHUNK) {
    (function (base) {
      chain = chain.then(function () {
        var m = Math.min(CHUNK, N - base), cases = [];
        for (var n = 0; n < m; n++) cases.push(genCase());
        return runChunk(cases, base);
      }).then(function () {
        if (!fileMode && N > CHUNK) console.error('iob: ' + stats.cases + '/' + N + ' cases, ' + stats.identical + ' identical, ' +
          Math.round((Date.now() - t00) / 1000) + ' s');
      });
    })(base);
  }
}
chain.then(finish, function (e) { console.error(e); process.exit(2); });
function finish() {
fs.closeSync(mm);
stats.wallSeconds = Math.round((Date.now() - t00) / 100) / 10;
stats.aidLeanCpuSeconds = Math.round(stats.aidLeanCpuSeconds * 10) / 10;
stats.nodeSeconds = Math.round(stats.nodeSeconds * 10) / 10;
stats.aidLeanSeconds = Math.round(stats.aidLeanSeconds * 10) / 10;
if (!fileMode) fs.writeFileSync(path.join(ROOT, FIXED ? 'docs/iobtest-fixed.json' : 'docs/iobtest.json'), JSON.stringify(stats, null, 1) + '\n');
if (FIXED) {
  console.log('iob --fixed: ' + stats.fixedVsOref0.identical + '/' + stats.cases + ' identical to oref0, ' +
    stats.fixedVsOref0.differWithTrigger + ' differ with the F-24 trigger, ' + stats.fixedVsOref0.differWithoutTrigger +
    ' differ without it; ' + stats.fixedVsPatchedJs.identical + '/' + stats.cases + ' identical to the patched oref0; ' +
    'F-24 trigger in ' + stats.f24.cases + ' cases');
  process.exit(stats.fixedVsOref0.differWithoutTrigger === 0 && stats.fixedVsPatchedJs.differ === 0 ? 0 : 1);
}
console.log(JSON.stringify(stats, null, 1));
console.log('iob: ' + stats.identical + '/' + stats.cases + ' identical, ' + stats.mismatchWithNearTie +
  ' differ at a rounding tie, ' + stats.mismatchWithoutNearTie + ' differ without one');
process.exit(stats.mismatchWithoutNearTie === 0 ? 0 : 1);
}
