#!/usr/bin/env node
// Writes scripts/difftest/targeted.jsonl: hand-made determine_basal cases, one for each
// branch of determine-basal.js and glucose-get-last.js that neither oref0's tests nor the
// random difftest (scripts/difftest/run.js) reach (docs/COVERAGE.md, before this suite).
// Each case is an ordinary `aid-lean batch` case plus `name` and `target` (the branch,
// file:line and outcome as in docs/COVERAGE.md), which aid-lean ignores.
//   node scripts/difftest/make-targeted.js
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var fs = require('fs');
var path = require('path');

var NOW = Date.UTC(2026, 10, 18, 12, 0, 0);

function clone(x) { return JSON.parse(JSON.stringify(x)); }

// A plain, valid case: BG 150 rising slowly, no carbs, modest IOB, no temp running.
function base() {
  var glucose = [];
  for (var i = 0; i < 10; i++) glucose.push({ date: NOW - i * 300000, glucose: 150 - 2 * i, device: 'dex' });
  var iob = [];
  for (var k = 0; k < 48; k++) {
    var f = Math.max(0, 1 - k / 48);
    iob.push({ iob: Math.round(1.2 * f * 1000) / 1000, activity: Math.round(0.01 * f * 10000) / 10000,
      iobWithZeroTemp: { iob: Math.round((1.2 - 0.2 * k / 12) * f * 1000) / 1000,
                         activity: Math.round(0.007 * f * 10000) / 10000 } });
  }
  iob[0].lastBolusTime = NOW - 90 * 60000;
  iob[0].lastTemp = { date: NOW - 20 * 60000, rate: 0, duration: 0 };
  return {
    glucose: glucose,
    currenttemp: { duration: 0, rate: 0, temp: 'absolute' },
    iob: iob,
    profile: {
      current_basal: 1, max_daily_basal: 1.3, max_basal: 3, max_iob: 3, min_bg: 100, max_bg: 120,
      sens: 50, carb_ratio: 10, autosens_max: 1.2, dia: 4, type: 'current', maxCOB: 120,
      noisyCGMTargetMultiplier: 1.3, maxRaw: 200, enableUAM: false, enableSMB_with_COB: false,
      enableSMB_always: false, enableSMB_after_carbs: false, enableSMB_with_temptarget: false,
      enableSMB_high_bg: false, enableSMB_high_bg_target: 160, allowSMB_with_high_temptarget: false,
      A52_risk_enable: false, maxSMBBasalMinutes: 30, maxUAMSMBBasalMinutes: 30, bolus_increment: 0.1,
      SMBInterval: 3, skip_neutral_temps: false, carbsReqThreshold: 1, exercise_mode: false,
      high_temptarget_raises_sensitivity: false, low_temptarget_lowers_sensitivity: false,
      sensitivity_raises_target: true, resistance_lowers_target: false, temptargetSet: false,
      out_units: 'mg/dL', model: '523'
    },
    autosens: { ratio: 1 },
    meal: { carbs: 0, nsCarbs: 0, bwCarbs: 0, journalCarbs: 0, mealCOB: 0, currentDeviation: 0,
      maxDeviation: 0, minDeviation: 0, slopeFromMaxDeviation: 0, slopeFromMinDeviation: 0,
      allDeviations: [0, 0, 0], lastCarbTime: 0, bwFound: false },
    microBolusAllowed: false,
    currentTime: NOW
  };
}

// Flat CGM data: every reading `bg`, from device `dev`.
function flat(c, bg, dev) {
  c.glucose.forEach(function (e) { e.glucose = bg; if (dev === undefined) delete e.device; else e.device = dev; });
  return c;
}

var cases = [];
function add(name, target, f) { var c = base(); f(c); c = Object.assign({ name: name, target: target }, c); cases.push(c); }

// --- determine-basal.js:83 then: SMB enabled with COB, and the carbs came from the Bolus Wizard.
// With bwFound, SMB is disabled earlier (line 66) unless A52_risk_enable is true.
add('smb-with-cob-bwcarbs', 'determine-basal.js:83 if 0', function (c) {
  c.profile.enableSMB_with_COB = true;
  c.meal.carbs = 40; c.meal.nsCarbs = 0; c.meal.bwCarbs = 40; c.meal.mealCOB = 30;
  c.meal.lastCarbTime = NOW - 30 * 60000; c.meal.bwFound = true; c.profile.A52_risk_enable = true;
  c.microBolusAllowed = true;
});
// --- determine-basal.js:94 then: SMB enabled for 6 h after carbs, the carbs from the Bolus Wizard
add('smb-after-carbs-bwcarbs', 'determine-basal.js:94 if 0', function (c) {
  c.profile.enableSMB_after_carbs = true;
  c.meal.carbs = 40; c.meal.nsCarbs = 0; c.meal.bwCarbs = 40; c.meal.mealCOB = 0;
  c.meal.lastCarbTime = NOW - 200 * 60000; c.meal.bwFound = true; c.profile.A52_risk_enable = true;
  c.microBolusAllowed = true;
});
// --- determine-basal.js:179 then: flat data from the simulator device "fakecgm" is accepted
add('flat-fakecgm', 'determine-basal.js:179 if 0', function (c) { flat(c, 120, 'fakecgm'); });
add('flat-fakecgm-low', 'determine-basal.js:179 if 0', function (c) { flat(c, 70, 'fakecgm'); });
// --- determine-basal.js:191 then, and its second operand: a calibration record one or two
// readings back stops getLastGlucose (glucose-get-last.js:27), last_cal is 1 or 2, and the
// deltas are 0, so the data is flat
add('just-calibrated-1', 'determine-basal.js:191 if 0; binary-expr 1; glucose-get-last.js:27 if 0', function (c) {
  c.glucose[1].type = 'cal';
});
add('just-calibrated-2', 'determine-basal.js:191 if 0; binary-expr 1; glucose-get-last.js:27 if 0', function (c) {
  flat(c, 130, 'dex'); c.glucose[2].type = 'cal';
});
// last_cal = 3: the second operand is false
add('calibrated-3-ago-flat', 'determine-basal.js:191 if 1 via binary-expr 1 false', function (c) {
  flat(c, 130, 'dex'); c.glucose[3].type = 'cal';
});
// --- determine-basal.js:268 then: c * (c + target_bg - normalTarget) <= 0
// low temp target 80 with half_basal_exercise_target 110: c = 10, c + 80 - 100 = -10
add('low-tt-small-halfbasal', 'determine-basal.js:268 if 0', function (c) {
  c.profile.low_temptarget_lowers_sensitivity = true; c.profile.temptargetSet = true;
  c.profile.min_bg = 80; c.profile.max_bg = 80; c.profile.half_basal_exercise_target = 110;
});
// half_basal_exercise_target 100: c = 0
add('low-tt-halfbasal-100', 'determine-basal.js:268 if 0', function (c) {
  c.profile.low_temptarget_lowers_sensitivity = true; c.profile.temptargetSet = true;
  c.profile.min_bg = 90; c.profile.max_bg = 90; c.profile.half_basal_exercise_target = 100;
});
// high temp target 150 with half_basal_exercise_target 60: c = -40, c + 50 = 10
add('high-tt-halfbasal-below-100', 'determine-basal.js:268 if 0', function (c) {
  c.profile.high_temptarget_raises_sensitivity = true; c.profile.temptargetSet = true;
  c.profile.min_bg = 150; c.profile.max_bg = 150; c.profile.half_basal_exercise_target = 60;
});
// --- determine-basal.js:361 then: an IOB element without `activity`, or without `iob`
add('iob-no-activity', 'determine-basal.js:361 if 0', function (c) { delete c.iob[0].activity; });
add('iob-no-iob', 'determine-basal.js:361 if 0', function (c) { delete c.iob[0].iob; });
add('iob-single-no-activity', 'determine-basal.js:361 if 0', function (c) {
  var h = c.iob[0]; delete h.activity; c.iob = h;
});
// --- determine-basal.js:419 then: eventualBG is NaN. A profile without `sens` makes sens,
// bgi, deviation and eventualBG NaN.
add('no-sens', 'determine-basal.js:419 if 0', function (c) { delete c.profile.sens; });
add('no-sens-no-autosens', 'determine-basal.js:419 if 0', function (c) { delete c.profile.sens; delete c.autosens; });
// --- determine-basal.js:898 then: lib/meal could not parse the clock
add('meal-clock-unparsed', 'determine-basal.js:898 if 0', function (c) {
  c.meal.reason = 'Could not parse clock data';
});
// the same while carbs would be required (BG low and falling)
add('meal-clock-unparsed-low', 'determine-basal.js:898 if 0', function (c) {
  c.glucose.forEach(function (e, i) { e.glucose = 75 + 3 * i; });
  c.meal.reason = 'Could not parse clock data';
});
// --- glucose-get-last.js:32 else: an older reading of 38 (an error code) and one from
// another device are skipped
add('older-reading-38', 'glucose-get-last.js:32 if 1', function (c) { c.glucose[2].glucose = 38; });
add('older-reading-other-device', 'glucose-get-last.js:32 if 1', function (c) { c.glucose[3].device = 'other'; });
add('older-reading-no-device', 'glucose-get-last.js:32 if 1', function (c) { delete c.glucose[1].device; });

var out = path.join(__dirname, 'targeted.jsonl');
fs.writeFileSync(out, cases.map(function (c) { return JSON.stringify(c); }).join('\n') + '\n');
console.log('wrote ' + cases.length + ' cases to ' + path.relative(process.cwd(), out));
