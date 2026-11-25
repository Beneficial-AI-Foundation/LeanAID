#!/usr/bin/env node
// Writes scripts/difftest/iob-targeted.jsonl: hand-made cases for scripts/difftest/iob.js
// (`--file`), for branches of lib/iob/history.js and lib/iob/calculate.js that the random,
// well-formed histories of iob.js cannot reach or reach only rarely. Each case has `name`
// and `target` (file:line and outcome, as in docs/COVERAGE.md), which aid-lean ignores.
//   node scripts/difftest/make-iob-targeted.js
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var fs = require('fs');
var path = require('path');

var MIN = 60000, HOUR = 3600000;
var NOW = Date.UTC(2026, 10, 18, 12, 0, 0);
function iso(t) { return new Date(t).toISOString().replace('.000Z', '+00:00'); }
function sched() { return [{ i: 0, start: '00:00:00', minutes: 0, rate: 1 }, { i: 1, start: '12:00:00', minutes: 720, rate: 0.8 }]; }
function base() {
  return { pumphistory: [], carbhistory: [], clock: iso(NOW),
    profile: { dia: 4, basalprofile: sched(), current_basal: 0.8, max_daily_basal: 1, max_basal: 4,
               min_bg: 100, max_bg: 120, suspend_zeros_iob: true },
    lookups: [] };
}
function temp(t, rate, dur) {
  return [{ _type: 'TempBasal', temp: 'absolute', rate: rate, timestamp: iso(t) },
          { _type: 'TempBasalDuration', 'duration (min)': dur, timestamp: iso(t) }];
}
var cases = [];
function add(name, target, f) { var c = base(); f(c); cases.push(Object.assign({ name: name, target: target }, c)); }

// QUIRK Q7 (history.js:105-110) has no case here. `lastSuspendTime` is the suspend's timestamp
// *string*, compared there with numbers; for ISO-8601 timestamps that is NaN and the branch is
// never taken. A numeric string (epoch ms) would compare as a number, but then
// `new Date(lastSuspendTime).toISOString()` at line 482, which runs in the same call, throws
// RangeError, so oref0 gives no output to compare (docs/COVERAGE.md).
// history.js:95 then: with the pump suspended before the history starts, a temp that ends
// before the first resume loses all of its duration
add('suspended-prior-temp-before-resume', 'iob/history.js:95 if 0', function (c) {
  c.pumphistory = temp(NOW - 30 * MIN, 1.5, 30).concat([{ _type: 'PumpResume', timestamp: iso(NOW - 60 * MIN) }])
    .concat(temp(NOW - 150 * MIN, 2, 30));
});
// history.js:390 then: an AndroidAPS "cancel TBR" record (duration null) cuts the temp before it
// and is removed
add('aaps-cancel-cuts-temp', 'iob/history.js:390 if 0', function (c) {
  c.profile.suspend_zeros_iob = false;
  c.pumphistory = [
    { eventType: 'Temp Basal', enteredBy: 'openaps://AndroidAPS', created_at: new Date(NOW - 20 * MIN).toISOString(), duration: null },
    { eventType: 'Temp Basal', enteredBy: 'openaps://AndroidAPS', created_at: new Date(NOW - 50 * MIN).toISOString(), absolute: 2.5, rate: 2.5, duration: 60 }];
});
// history.js:287 then: a bolus in the future is ignored. A record later than the last kept
// one is skipped (line 276) before it gets there, unless that last record's time is invalid
// (`x > Invalid Date` is false), as after a record with an unparsable timestamp.
add('future-bolus-after-invalid-timestamp', 'iob/history.js:287 if 0', function (c) {
  c.pumphistory = [{ _type: 'Prime', amount: 0.3, timestamp: 'not a date' },
    { _type: 'Bolus', amount: 1, programmed: 1, unabsorbed: 0, duration: 0, timestamp: iso(NOW + 20 * MIN) },
    { _type: 'Bolus', amount: 2, programmed: 2, unabsorbed: 0, duration: 0, timestamp: iso(NOW - 60 * MIN) }];
});
// history.js:521 else: no basal schedule; the temps are compared with current_basal
add('no-basal-schedule', 'iob/history.js:521 if 1', function (c) {
  delete c.profile.basalprofile;
  c.pumphistory = temp(NOW - 50 * MIN, 2, 30).concat(temp(NOW - 120 * MIN, 0, 60));
});
// meal/history.js:119 else: a Bolus Wizard record whose carbs are already there (a Nightscout
// carb entry at the same time) is counted as a duplicate
add('bolus-wizard-duplicate-carbs', 'meal/history.js:119 if 1', function (c) {
  var t = NOW - 40 * MIN;
  c.pumphistory = [{ _type: 'Bolus', amount: 3, programmed: 3, unabsorbed: 0, duration: 0, timestamp: iso(t) },
    { _type: 'BolusWizard', timestamp: iso(t), carb_input: 30 }];
  c.carbhistory = [{ carbs: 30, created_at: new Date(t + 1000).toISOString(), enteredBy: 'careportal' }];
});
// calculate.js:123 else: a bolus at DIA hours ago minus 20 s has minsAgo = round(DIA·60 − 1/3)
// = DIA·60, so `minsAgo < end` is false (exponential curves)
add('exponential-bolus-at-end', 'iob/calculate.js:123 if 1', function (c) {
  c.profile.curve = 'rapid-acting'; c.profile.dia = 5;
  c.pumphistory = [{ _type: 'Bolus', amount: 2, programmed: 2, unabsorbed: 0, duration: 0, timestamp: iso(NOW - 5 * HOUR + 20000) }];
});
add('ultra-rapid-bolus-at-end-short-dia', 'iob/calculate.js:123 if 1', function (c) {
  c.profile.curve = 'ultra-rapid'; c.profile.dia = 3;   // raised to 5 h by total.js
  c.pumphistory = [{ _type: 'Bolus', amount: 2, programmed: 2, unabsorbed: 0, duration: 0, timestamp: iso(NOW - 5 * HOUR + 25000) }];
});

// Regression cases for the two transcription errors found by iob.js (docs/FINDINGS.md F-25).
// QUIRK Q11: `var duration` (history.js:345) is function-scoped, so the TempBasal at 15:19:05,
// which has no TempBasalDuration record, gets the 30 min of the TempBasal processed before it.
// (Minimised from case 24 of the first run of iob.js, 500 cases, seed 1.)
cases.push({ name: 'q11-temp-without-duration-record', target: 'iob/history.js:345-359 (QUIRK Q11)',
  pumphistory: [{ _type: 'TempBasalDuration', 'duration (min)': 30, timestamp: '2026-11-18T17:00:51Z' },
    { _type: 'TempBasal', temp: 'absolute', rate: 0.3, timestamp: '2026-11-18T17:00:51Z' },
    { _type: 'TempBasal', temp: 'absolute', rate: 0, timestamp: '2026-11-18T15:19:05Z' }],
  carbhistory: [],
  profile: { dia: 4, basalprofile: [{ i: 0, start: '00:00:00', minutes: 0, rate: 1.2 }, { i: 1, start: '11:00:00', minutes: 660, rate: 0.71 }],
    current_basal: 1.2, max_daily_basal: 1.2, max_basal: 4, suspend_zeros_iob: false, curve: 'ultra-rapid',
    useCustomPeakTime: false, insulinPeakTime: 35, min_bg: 135, max_bg: 136 },
  clock: '2026-11-18T17:20:25.000Z', lookups: [] });
// QUIRK Q8, timestamp: the temp at 11:20 UTC (pump timestamp "2026-11-18T06:20:00-05:00")
// starts during a suspend that ends at 11:30 UTC. splitAroundSuspends (line 151) gives the very
// tempHistory object the timestamp moment(...).format() = "2026-11-18T11:30:00+00:00", and
// index.js reports it in lastTemp.
add('q8-lasttemp-timestamp-after-suspend', 'iob/history.js:144-153 (QUIRK Q8)', function (c) {
  function est(t) { return new Date(t - 5 * HOUR).toISOString().slice(0, 19) + '-05:00'; }
  var t0 = NOW - 40 * MIN;
  c.pumphistory = [
    { _type: 'PumpResume', timestamp: est(t0 + 10 * MIN) },
    { _type: 'TempBasalDuration', 'duration (min)': 30, timestamp: est(t0) },
    { _type: 'TempBasal', temp: 'absolute', rate: 2, timestamp: est(t0) },
    { _type: 'PumpSuspend', timestamp: est(t0 - 15 * MIN) }];
});

var out = path.join(__dirname, 'iob-targeted.jsonl');
fs.writeFileSync(out, cases.map(function (c) { return JSON.stringify(c); }).join('\n') + '\n');
console.log('wrote ' + cases.length + ' cases to ' + path.relative(process.cwd(), out));
