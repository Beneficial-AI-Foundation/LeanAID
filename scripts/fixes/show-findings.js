#!/usr/bin/env node
// Prints, for each case of scripts/fixes/findings.jsonl, the triggers and the rate, duration
// and microbolus of oref0 and of `aid-lean --fixed` (docs/FIXED.md).
//   TZ=UTC node scripts/fixes/show-findings.js
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var fs = require('fs');
var path = require('path');
var common = require('../difftest/common');
var file = path.join(__dirname, 'findings.jsonl');
var cases = fs.readFileSync(file, 'utf8').split('\n').filter(Boolean).map(JSON.parse);
var lean = common.runLeanFixed(file);
function b(o) {
  var s = o.error ? 'error' : (o.rate === undefined ? 'no rate' : (o.rate === null ? 'NaN' : o.rate) + ' U/h ' +
    (o.duration === null ? 'NaN' : o.duration) + ' min');
  return s + (o.units !== undefined ? ', ' + o.units + ' U' : '');
}
cases.forEach(function (c, n) {
  var e = JSON.parse(common.runNodeQuiet(c).out), f = JSON.parse(lean[n].out);
  console.log('| ' + c.name + ' | ' + c.target + ' | ' + (lean[n].triggers.join(', ') || '–') + ' | ' + b(e) + ' | ' + b(f) + ' |');
});
