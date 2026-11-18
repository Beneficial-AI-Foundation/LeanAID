#!/usr/bin/env node
// Extracts every test (`it(...)`, including commented-out ones) from oref0's in-scope
// test files, with the input overrides and the assertions written in the test.
// Writes docs/tests-inventory.json, which docs/TESTS.md is generated from
// (scripts/report.js joins it with the classification and theorem tables).
'use strict';
var fs = require('fs');
var path = require('path');
var ROOT = path.resolve(__dirname, '..');
var T = path.join(ROOT, 'vendor/oref0/tests');

var files = [
  ['DB', 'determine-basal.test.js'],
  ['IOB', 'iob.test.js'],
  ['STB', 'set-temp-basal.test.js'],
  ['BAS', 'basal.test.js'],
  ['GLG', 'get-last-glucose.test.js'],
  ['COBH', 'cobhistory.test.js'],
];

function extract(prefix, file) {
  var src = fs.readFileSync(path.join(T, file), 'utf8');
  var lines = src.split('\n');
  // Region inside /* ... */ blocks
  var inBlock = [], blk = false;
  lines.forEach(function (l, i) {
    if (/^\s*\/\*/.test(l)) blk = true;
    inBlock[i] = blk;
    if (/\*\/\s*$/.test(l)) blk = false;
  });
  var tests = [];
  for (var i = 0; i < lines.length; i++) {
    var m = lines[i].match(/^(\s*)(\/\/\s*)?it\((['"])(.*?)\3\s*(\+[^,]*)?,/);
    if (!m) continue;
    var commented = !!m[2] || inBlock[i];
    // collect body until the matching closing `});` at the same indentation
    var indent = m[1].length;
    var body = [];
    for (var j = i + 1; j < lines.length; j++) {
      var l = lines[j];
      var close = l.match(/^(\s*)(\/\/\s*)?\}\);/);
      if (close && close[1].length <= indent + (m[2] ? 0 : 0) && Math.abs(close[1].length - indent) <= 1) break;
      body.push(l);
    }
    var name = (m[4] + (m[5] ? ' ' + m[5].trim() : '')).replace(/\( \+ rate\.basal.*$/, '(<basal> -> <rounded>), 6 cases: 0.83, 0.86, 1.83, 1.86, 10.83, 10.86');
    var asserts = body.filter(function (l) { return /should|\.equal\(|\.match\(/.test(l) && !/^\s*\/\/.*console/.test(l); })
      .map(function (l) { return l.trim(); });
    var activeAsserts = asserts.filter(function (a) { return !/^\/\//.test(a); });
    var inputs = body.filter(function (l) { return /^\s*(\/\/\s*)?var (glucose_status|currenttemp|iob_data|profile\w*|meal_data|autosens_data|basal|inputs|current|currentTemp)\s*=/.test(l) || /^\s*profile\.\w+\s*=/.test(l); })
      .map(function (l) { return l.trim(); });
    tests.push({ file: file, line: i + 1, name: name, commented: commented,
                 inputs: inputs, asserts: commented ? asserts : activeAsserts });
  }
  return tests.map(function (t, k) { t.id = prefix + '-' + String(k + 1).padStart(2, '0'); return t; });
}

var all = [];
files.forEach(function (f) { all = all.concat(extract(f[0], f[1])); });
fs.writeFileSync(path.join(ROOT, 'docs/tests-inventory.json'), JSON.stringify(all, null, 1));
var byFile = {};
all.forEach(function (t) {
  var k = t.file; byFile[k] = byFile[k] || { active: 0, commented: 0 };
  byFile[k][t.commented ? 'commented' : 'active']++;
});
console.log(JSON.stringify(byFile, null, 1));
