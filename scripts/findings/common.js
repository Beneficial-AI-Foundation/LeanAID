'use strict';
// Shared helpers for the finding reproductions (F-04, F-11, F-12).
// Each script takes the path of an oref0-style lib/ directory (default
// vendor/oref0/lib) and prints one verdict line. Exit codes: 0 PRESENT,
// 1 ABSENT, 2 INCONCLUSIVE.
var path = require('path');

var REPO = path.resolve(__dirname, '..', '..');

function libDir() {
  var arg = process.argv[2];
  return path.resolve(arg || path.join(REPO, 'vendor', 'oref0', 'lib'));
}

// oref0 logs its reasoning with console.error; keep the verdict line clean
// unless VERBOSE is set.
function quiet(fn) {
  var saved = console.error, savedLog = console.log;
  if (!process.env.VERBOSE) { console.error = function () {}; console.log = function () {}; }
  try { return fn(); } finally { console.error = saved; console.log = savedLog; }
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

var NOW = new Date('2026-11-20T12:00:00Z');

function determine(lib, glucose_status, profile) {
  var db = load(lib, 'determine-basal/determine-basal');
  var tbf = load(lib, 'basal-set-temp');
  return quiet(function () {
    return db(glucose_status, {duration: 0, rate: 0, temp: 'absolute'},
              {iob: 0, activity: 0, bolussnooze: 0}, profile, {ratio: 1}, emptyMeal(),
              tbf, false, null, NOW);
  });
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

module.exports = {libDir: libDir, quiet: quiet, load: load, testProfile: testProfile,
  emptyMeal: emptyMeal, NOW: NOW, determine: determine, fmt: fmt, verdict: verdict};
