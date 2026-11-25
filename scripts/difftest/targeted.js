#!/usr/bin/env node
// Targeted differential test of aid-lean against oref0's determine_basal.
//   TZ=UTC node scripts/difftest/targeted.js [cases.jsonl = scripts/difftest/targeted.jsonl] [--fixed]
// Runs every case of the file through oref0 (getLastGlucose, then determine_basal) and
// through `aid-lean batch`, and compares the outputs exactly as scripts/difftest/run.js does
// (scripts/difftest/common.js). Prints a summary; exit code 1 if any case differs without a
// rounding tie in oref0's Math.round calls, or if aid-lean gives no line for a case.
// The cases are made by scripts/difftest/make-targeted.js.
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var fs = require('fs');
var path = require('path');
var common = require('./common');

if (process.env.TZ !== 'UTC') { console.error('run with TZ=UTC'); process.exit(1); }
// --fixed: the corrected version against oref0 and the patched oref0 (scripts/difftest/fixed.js)
var FIXED = process.argv.indexOf('--fixed') >= 0;
var argv = process.argv.filter(function (a) { return a !== '--fixed'; });
var file = argv[2] || path.join(__dirname, 'targeted.jsonl');
if (FIXED) { require('./fixed').runFixedFile(file); return; }
var lines = fs.readFileSync(file, 'utf8').split('\n').filter(function (l) { return l.trim() !== ''; });
var cases = lines.map(function (l) { return JSON.parse(l); });

var expected = cases.map(common.runNodeQuiet);
var t0 = Date.now();
var lean = common.runLean(file);
var stats = common.newStats({ file: path.relative(common.ROOT, path.resolve(file)), cases: cases.length });
stats.aidLeanSeconds = (Date.now() - t0) / 1000;
var mismatches = [];
cases.forEach(function (c, n) {
  var d = common.compare(stats, expected[n].out, lean[n] === undefined ? '' : lean[n], expected[n].nearTie);
  if (d) { d.n = n; d.name = c.name; d.target = c.target; mismatches.push(d); }
});
mismatches.forEach(function (d) {
  console.log('MISMATCH ' + d.name + ' (' + d.target + ')' + (d.nearTie ? ' [rounding tie]' : '') +
    ': fields ' + d.fields.join(', '));
  d.fields.forEach(function (k) {
    console.log('  oref0   ' + k + ': ' + JSON.stringify(d.oref0[k]));
    console.log('  aid-lean ' + k + ': ' + JSON.stringify(d.aidLean[k]));
  });
});
console.log(JSON.stringify(stats));
console.log('targeted: ' + stats.identical + '/' + stats.cases + ' identical, ' + stats.mismatchWithNearTie +
  ' differ at a rounding tie, ' + stats.mismatchWithoutNearTie + ' differ without one');
process.exit(stats.mismatchWithoutNearTie === 0 ? 0 : 1);
