// Shared by the differential tests of determine_basal (scripts/difftest/run.js,
// scripts/difftest/targeted.js): how oref0 is run on a case, how `aid-lean batch` is run
// on a file of cases, and how the two outputs are compared and counted.
//
// A case is a JSON object { glucose, currenttemp, iob, profile, autosens?, meal,
// microBolusAllowed, currentTime } (see App/Main.lean, `batchCase`).
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var fs = require('fs');
var path = require('path');
var cp = require('child_process');
var ROOT = path.resolve(__dirname, '../..');
var O = path.join(ROOT, 'vendor/oref0');
var getLastGlucose = require(path.join(O, 'lib/glucose-get-last'));
var determine_basal = require(path.join(O, 'lib/determine-basal/determine-basal'));
var tempBasalFunctions = require(path.join(O, 'lib/basal-set-temp'));

// Flag Math.round calls whose argument lies within 1e-9 (relative) of a .5 tie: there,
// double rounding and exact arithmetic can go different ways (DESIGN D2, FINDINGS F-13).
var realRound = Math.round, nearTie = false;
Math.round = function (x) {
  var f = x - Math.floor(x);
  if (Math.abs(f - 0.5) <= 1e-9 * Math.max(1, Math.abs(x))) nearTie = true;
  return realRound(x);
};

// oref0 on one case, as bin/oref0-determine-basal.js does: getLastGlucose, then determine_basal.
function runNode(c) {
  nearTie = false;
  var gs = getLastGlucose(JSON.parse(JSON.stringify(c.glucose)));
  var autosens = c.autosens ? JSON.parse(JSON.stringify(c.autosens)) : null;
  var rT = determine_basal(gs, JSON.parse(JSON.stringify(c.currenttemp)), JSON.parse(JSON.stringify(c.iob)),
    JSON.parse(JSON.stringify(c.profile)), autosens, JSON.parse(JSON.stringify(c.meal)), tempBasalFunctions,
    c.microBolusAllowed, null, new Date(c.currentTime));
  var out = typeof rT.error === 'undefined' ? JSON.stringify(rT) : JSON.stringify({ error: rT.error });
  return { out: out, nearTie: nearTie };
}

// runNode with oref0's diagnostics on stderr silenced.
function runNodeQuiet(c) { return quietly(function () { return runNode(c); }); }

// `aid-lean batch` on a JSONL file: one output line per case.
function runLean(casesFile) {
  return cp.execFileSync(path.join(ROOT, '.lake/build/bin/aid-lean'), ['batch', casesFile],
    { encoding: 'utf8', maxBuffer: 1 << 30 }).split('\n');
}

// The counters, after the keys of `prefix` (kept first, for a stable JSON layout).
function newStats(prefix) {
  var s = {};
  Object.keys(prefix || {}).forEach(function (k) { s[k] = prefix[k]; });
  var c = { identical: 0, reasonOnly: 0, valueDiff: 0,
    predOnlyPlusMinus1: 0, rateDiffers: 0, mismatchWithNearTie: 0, mismatchWithoutNearTie: 0, casesWithNearTie: 0,
    fieldsDiffering: {}, paths: { smbUnits: 0, errors: 0, rateNull: 0 } };
  Object.keys(c).forEach(function (k) { s[k] = c[k]; });
  return s;
}

function predOnly1(eo, lo, diff) {
  if (diff.some(function (f) { return f !== 'predBGs' && f !== 'reason'; })) return false;
  return ['IOB', 'ZT', 'COB', 'UAM'].every(function (k) {
    var a = (eo.predBGs || {})[k] || [], b = (lo.predBGs || {})[k] || [];
    return a.length === b.length && a.every(function (x, i) { return Math.abs(x - b[i]) <= 1; });
  });
}

// Compare oref0's output `e` (string) with aid-lean's `l` (string) and count the result in
// `stats`. Identical means byte-identical JSON. Returns null if identical, else a mismatch
// record { nearTie, fields, oref0, aidLean }.
function compare(stats, e, l, tie) {
  if (tie) stats.casesWithNearTie++;
  var eo = JSON.parse(e);
  if (eo.units !== undefined) stats.paths.smbUnits++;
  if (eo.error !== undefined) stats.paths.errors++;
  if (eo.rate === null) stats.paths.rateNull++;
  if (e === l) { stats.identical++; return null; }
  if (tie) stats.mismatchWithNearTie++; else stats.mismatchWithoutNearTie++;
  var lo; try { lo = JSON.parse(l); } catch (err) { lo = {}; }
  var keys = {}; Object.keys(eo).concat(Object.keys(lo)).forEach(function (k) { keys[k] = 1; });
  var diff = Object.keys(keys).filter(function (k) { return JSON.stringify(eo[k]) !== JSON.stringify(lo[k]); });
  if (diff.length === 1 && diff[0] === 'reason') stats.reasonOnly++;
  else { stats.valueDiff++; if (predOnly1(eo, lo, diff)) stats.predOnlyPlusMinus1++; }
  if (diff.indexOf('rate') >= 0) stats.rateDiffers++;
  diff.forEach(function (k) { stats.fieldsDiffering[k] = (stats.fieldsDiffering[k] || 0) + 1; });
  return { nearTie: tie, fields: diff, oref0: eo, aidLean: lo };
}

// For other runners: clear the flag, and read whether a Math.round call since then was near a tie.
function resetNearTie() { nearTie = false; }
function sawNearTie() { return nearTie; }

// Run f() with oref0's diagnostics (console.error, process.stderr.write) silenced.
function quietly(f) {
  var origErr = console.error; console.error = function () {};
  var origWrite = process.stderr.write.bind(process.stderr); process.stderr.write = function () { return true; };
  try { return f(); } finally { console.error = origErr; process.stderr.write = origWrite; }
}

module.exports = { ROOT: ROOT, runNode: runNode, runNodeQuiet: runNodeQuiet, runLean: runLean,
  newStats: newStats, compare: compare, resetNearTie: resetNearTie, sawNearTie: sawNearTie, quietly: quietly };
