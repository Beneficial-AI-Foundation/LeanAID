#!/usr/bin/env node
// Writes scripts/fixes/findings.jsonl: for each finding of determine_basal fixed in
// LeanAID/Fixed (F-04, F-11, F-12, F-23), a trigger input and a control input, as cases of
// `aid-lean batch` (see scripts/difftest/common.js). Run them with
//   TZ=UTC node scripts/difftest/targeted.js scripts/fixes/findings.jsonl --fixed
// which compares oref0, the patched oref0 (scripts/fixes/apply.sh) and `aid-lean --fixed`.
// The inputs are those of scripts/findings/f04.js, f11.js, f12.js and scripts/probe-lgs-nan.js.
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var fs = require('fs');
var path = require('path');
var NOW = Date.UTC(2026, 10, 18, 3, 0, 0);
function testProfile() {
  return { max_iob: 2.5, dia: 3, type: 'current', current_basal: 0.9, max_daily_basal: 1.3,
    max_basal: 3.5, max_bg: 120, min_bg: 110, sens: 40, carb_ratio: 10 };
}
function emptyMeal() {
  return { carbs: 0, nsCarbs: 0, bwCarbs: 0, journalCarbs: 0, mealCOB: 0, currentDeviation: 0, maxDeviation: 0,
    minDeviation: 0, slopeFromMaxDeviation: 0, slopeFromMinDeviation: 0, allDeviations: [0, 0, 0, 0, 0], bwFound: false };
}
// readings every 5 minutes, newest first, `step` mg/dL per 5 minutes; `dated` false drops the dates
function readings(bg, step, dated, ageMin) {
  var g = [];
  for (var i = 0; i < 10; i++) {
    var e = { glucose: bg - step * i };
    if (dated) e.date = NOW - (ageMin || 0) * 60000 - i * 300000;
    g.push(e);
  }
  return g;
}
function caseOf(name, target, o) {
  return Object.assign({ name: name, target: target, iob: { iob: 0, activity: 0, bolussnooze: 0 },
    currenttemp: { duration: 0, rate: 0, temp: 'absolute' }, autosens: { ratio: 1 }, meal: emptyMeal(),
    microBolusAllowed: false, currentTime: NOW }, o);
}
var cases = [];
var p04 = testProfile(); p04.current_basal = 0.5; p04.max_basal = 0.83;
var p04c = testProfile(); p04c.current_basal = 0.5; p04c.max_basal = 0.85;
cases.push(caseOf('F-04 trigger', 'max_basal 0.83 off the pump grid, BG 300 rising', { glucose: readings(300, 10, true), profile: p04 }));
cases.push(caseOf('F-04 control', 'max_basal 0.85 on the grid', { glucose: readings(300, 10, true), profile: p04c }));
var p04cgm = testProfile(); p04cgm.current_basal = 0.83; p04cgm.max_basal = 0.83;
cases.push(caseOf('F-04 trigger (CGM-error branch)', 'current_basal = max_basal = 0.83, stale reading, temp 2 U/h running',
  { glucose: readings(150, 0, true, 30), profile: p04cgm, currenttemp: { duration: 20, rate: 2, temp: 'absolute' } }));
cases.push(caseOf('F-11 trigger', 'readings without dates, BG 250 rising', { glucose: readings(250, 5, false), profile: testProfile(),
  currenttemp: { duration: 20, rate: 2, temp: 'absolute' } }));
cases.push(caseOf('F-11 control', 'the same readings dated now', { glucose: readings(250, 5, true), profile: testProfile(),
  currenttemp: { duration: 20, rate: 2, temp: 'absolute' } }));
var p12 = testProfile(); delete p12.max_basal; delete p12.max_daily_basal;
var p12b = testProfile(); delete p12b.max_basal;
cases.push(caseOf('F-12 trigger', 'no max_basal, no max_daily_basal, BG 300 rising', { glucose: readings(300, 10, true), profile: p12 }));
cases.push(caseOf('F-12 trigger (running high temp)', 'no max_basal, temp 2 U/h running', { glucose: readings(300, 10, true), profile: p12b,
  currenttemp: { duration: 20, rate: 2, temp: 'absolute' } }));
cases.push(caseOf('F-12 trigger (long zero temp)', 'no max_basal, zero temp with 90 min left', { glucose: readings(300, 10, true), profile: p12b,
  currenttemp: { duration: 90, rate: 0, temp: 'absolute' } }));
cases.push(caseOf('F-12 control', 'the test profile, max_basal 3.5', { glucose: readings(300, 10, true), profile: testProfile() }));
// F-23: scripts/probe-lgs-nan.js case A (mealCOB 20, no carbs, UAM, BG 60 rising) and its control with carbs
var p23 = { current_basal: 1, max_daily_basal: 1, max_basal: 3, max_iob: 1, min_bg: 100, max_bg: 100,
  sens: 50, carb_ratio: 10, dia: 3, type: 'current', maxCOB: 120, enableUAM: true };
var iob23 = [];
for (var k = 0; k < 48; k++) iob23.push({ iob: 0, activity: 0, iobWithZeroTemp: { iob: 0, activity: 0 } });
iob23[0].lastBolusTime = NOW - 3 * 3600000;
iob23[0].lastTemp = { date: NOW - 20 * 60000, rate: 1, duration: 30 };
var meal23 = { nsCarbs: 0, bwCarbs: 0, journalCarbs: 0, currentDeviation: 0, maxDeviation: 0, minDeviation: 0,
  slopeFromMaxDeviation: 0, slopeFromMinDeviation: 0, allDeviations: [0, 0, 0], mealCOB: 20, lastCarbTime: NOW - 60 * 60000 };
var rising = [60, 57, 54, 51, 48, 45, 42, 40, 40, 40].map(function (g, i) { return { date: NOW - i * 300000, glucose: g }; });
cases.push(caseOf('F-23 trigger', 'mealCOB 20 without carbs, UAM, BG 60 rising', { glucose: rising, profile: p23, iob: iob23,
  autosens: undefined, meal: meal23 }));
cases.push(caseOf('F-23 control', 'the same with carbs 30', { glucose: rising, profile: p23, iob: iob23,
  autosens: undefined, meal: Object.assign({}, meal23, { carbs: 30 }) }));
var out = path.join(__dirname, 'findings.jsonl');
fs.writeFileSync(out, cases.map(function (c) { return JSON.stringify(c); }).join('\n') + '\n');
console.log('wrote ' + cases.length + ' cases to ' + path.relative(process.cwd(), out));
