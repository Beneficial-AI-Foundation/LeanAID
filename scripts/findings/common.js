'use strict';
// Shared helpers for the finding reproductions (F-04, F-11, F-12).
// Each script takes the path of an oref0-style lib/ directory (default
// vendor/oref0/lib) and prints one verdict line. Exit codes: 0 PRESENT,
// 1 ABSENT, 2 INCONCLUSIVE.
var path = require('path');

var REPO = path.resolve(__dirname, '..', '..');

// --fixed (docs/FIXED.md): the lib/ of the patched copy made by scripts/fixes/apply.sh is the
// default, and each script also checks that its control input gives the same result as with
// vendor/oref0/lib (`sameAsVendor`).
var FIXED = process.argv.indexOf('--fixed') >= 0;
var ARGS = process.argv.slice(2).filter(function (a) { return a !== '--fixed'; });
var VENDOR_LIB = path.join(REPO, 'vendor', 'oref0', 'lib');
var FIXED_LIB = path.join(REPO, 'scripts', 'fixes', 'out', 'oref0-fixed', 'lib');

function libDir() {
  var arg = ARGS[0];
  return path.resolve(arg || (FIXED ? FIXED_LIB : VENDOR_LIB));
}

// --fixed: the control input `f(lib)` gives the same result on `lib` as on vendor/oref0/lib.
function sameAsVendor(f, lib) {
  return JSON.stringify(f(lib)) === JSON.stringify(f(VENDOR_LIB));
}

// oref0 logs its reasoning with console.error; keep the verdict line clean
// unless VERBOSE is set.
function quiet(fn) {
  var saved = console.error, savedLog = console.log, savedW = process.stderr.write;
  if (!process.env.VERBOSE) {
    console.error = function () {}; console.log = function () {};
    process.stderr.write = function () { return true; };
  }
  try { return fn(); } finally { console.error = saved; console.log = savedLog; process.stderr.write = savedW; }
}

function load(lib, rel) { return require(path.join(lib, rel)); }

// The standard profile of oref0's determine-basal tests (tests/determine-basal.test.js:65).
function testProfile() {
  return {max_iob: 2.5, dia: 3, type: 'current', current_basal: 0.9, max_daily_basal: 1.3,
          max_basal: 3.5, max_bg: 120, min_bg: 110, sens: 40, carb_ratio: 10};
}

// Meal data with no carbs on board (as in oref0's tests, carbs zeroed).
function emptyMeal() {
  return {carbs: 0, nsCarbs: 0, bwCarbs: 0, journalCarbs: 0, mealCOB: 0, currentDeviation: 0,
          maxDeviation: 0, minDeviation: 0, slopeFromMaxDeviation: 0, slopeFromMinDeviation: 0,
          allDeviations: [0, 0, 0, 0, 0], bwFound: false};
}

// The decision time. All inputs are relative to it. It is the current time (to the minute)
// rather than a fixed date because some old descendants (e.g. N3FM/oref0, 2018) ignore determine_basal's
// currentTime argument and use the system clock.
var NOW = new Date(Math.floor(Date.now() / 60000) * 60000);

function determine(lib, glucose_status, profile) {
  var db = load(lib, 'determine-basal/determine-basal');
  var tbf = load(lib, 'basal-set-temp');
  var args = [glucose_status, {duration: 0, rate: 0, temp: 'absolute'},
              {iob: 0, activity: 0, bolussnooze: 0}, profile, {ratio: 1}, emptyMeal(),
              tbf, false, null, NOW];
  // Descendants with a longer signature (trio-oref / iAPS oref2: pumphistory, preferences,
  // basalprofile, trio_custom_variables or oref2_variables, middleWare) get neutral values:
  // no override, no dynamic ISF, SMB settings untouched, no middleware.
  if (db.length > 10) {
    var custom = {overrideTarget: 0, useOverride: false, smbIsOff: false, smbIsScheduledOff: false,
      advancedSettings: false, isfAndCr: false, isf: false, cr: false, smbMinutes: 30,
      uamMinutes: 30, currentTDD: 0, weightedAverage: 0, overridePercentage: 100,
      unlimited: false, overrideMaxIOB: false, smbIsAlwaysOff: false, duration: 0, date: NOW};
    var prefs = {useNewFormula: false, sigmoid: false, curve: 'rapid-acting', useCustomPeakTime: false,
      adjustmentFactor: 0.8, adjustmentFactorSigmoid: 0.5, enableDynamicCR: false};
    args = args.concat([[], prefs, [], custom, '']);
  }
  return quiet(function () { return db.apply(null, args); });
}

function fmt(r) {
  if (r === undefined) return 'threw';
  if (r.error) return 'error(' + r.error + ')';
  if (r.rate === undefined) return 'no temp';
  return r.rate + ' U/h for ' + r.duration + ' min';
}

function verdict(id, v, detail) {
  console.log(id + ': ' + v + ' — ' + detail);
  process.exit(v === 'PRESENT' ? 0 : v === 'ABSENT' ? 1 : 2);
}

module.exports = {FIXED: FIXED, sameAsVendor: sameAsVendor, libDir: libDir, quiet: quiet, load: load, testProfile: testProfile,
  emptyMeal: emptyMeal, NOW: NOW, determine: determine, fmt: fmt, verdict: verdict};
