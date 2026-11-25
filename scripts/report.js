#!/usr/bin/env node
// Collects the project's headline numbers from the build and writes docs/numbers.json.
// Run after `lake build`: node scripts/report.js
// Every number on site/index.html must come from this file. `theorems.total` counts
// LeanAID/Proofs only; `theorems.fixed` counts LeanAID/Fixed (docs/FIXED.md).
'use strict';
var fs = require('fs');
var path = require('path');
var cp = require('child_process');
var ROOT = path.resolve(__dirname, '..');
function sh(c) { return cp.execSync(c, { cwd: ROOT, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }); }

var inv = JSON.parse(fs.readFileSync(path.join(ROOT, 'docs/tests-inventory.json'), 'utf8'));
var cls = JSON.parse(fs.readFileSync(path.join(__dirname, 'test-classes.json'), 'utf8'));
var thm = JSON.parse(fs.readFileSync(path.join(__dirname, 'test-theorems.json'), 'utf8'));

var tests = { blocks: inv.length, byFile: {}, byClass: {} };
inv.forEach(function (t) {
  tests.byFile[t.file] = (tests.byFile[t.file] || 0) + 1;
  var c = (cls[t.id] || {}).class; tests.byClass[c] = (tests.byClass[c] || 0) + 1;
});
var ab = inv.filter(function (t) { var c = (cls[t.id] || {}).class; return c === 'A' || c === 'B'; });
var lifted = ab.filter(function (t) { return /^proved|general theorem proved|general lemma proved/.test((thm[t.id] || {}).status || ''); });
tests.classAB = ab.length;
tests.liftedToGeneralTheorems = lifted.length;
tests.notLifted = ab.filter(function (t) { return lifted.indexOf(t) < 0; }).map(function (t) { return t.id; });

// theorems in LeanAID/Proofs
var proofFiles = sh("find LeanAID/Proofs -name '*.lean'").trim().split('\n');
var nThm = 0;
proofFiles.forEach(function (f) { nThm += (fs.readFileSync(path.join(ROOT, f), 'utf8').match(/^theorem /gm) || []).length; });
// theorems in LeanAID/Fixed (the corrected version, docs/FIXED.md), counted separately
var fixedFiles = sh("find LeanAID/Fixed -name '*.lean'").trim().split('\n').filter(Boolean);
var nFixed = 0;
fixedFiles.forEach(function (f) { nFixed += (fs.readFileSync(path.join(ROOT, f), 'utf8').match(/^theorem /gm) || []).length; });
var headline = fs.readFileSync(path.join(__dirname, 'headline.txt'), 'utf8').split('\n')
  .filter(function (l) { return l.trim() && !/^\s*#/.test(l); });

// check.sh (forbidden constructs + axioms)
var check = sh('bash scripts/check.sh');
var axioms = {};
(check.match(/depends on axioms: \[[^\]]*\]/g) || []).forEach(function (m) {
  m.replace(/.*\[|\]/g, '').split(',').forEach(function (a) { a = a.trim(); if (a) axioms[a] = true; });
});
var sorries = (sh("grep -rnw sorry LeanAID App --include=*.lean | grep -v -- '--' || true").trim().split('\n').filter(Boolean)).length;

// conformance (selftest)
var self = sh('.lake/build/bin/aid-lean selftest');
var m = self.match(/selftest: (\d+)\/(\d+) conformance cases \((\d+) at rounding ties\)/);

var lines = function (dir) { return parseInt(sh("cat $(find " + dir + " -name '*.lean') | wc -l").trim(), 10); };

var out = {
  generated: new Date().toISOString(),
  oref0: '88cf032aa74ff25f69464a7d9cd601ee3940c0b3 (0.7.1)',
  tests: tests,
  theorems: { total: nThm, headline: headline.length, headlineNames: headline, fixed: nFixed },
  axioms: Object.keys(axioms).sort(),
  sorry: sorries,
  checkShOk: /check\.sh: OK/.test(check),
  conformance: m ? { passed: +m[1], total: +m[2], atRoundingTies: +m[3] } : null,
  linesOfLean: { core: lines('LeanAID/Core'), proofs: lines('LeanAID/Proofs'), spec: lines('LeanAID/Spec'),
    fixed: lines('LeanAID/Fixed') }
};
fs.writeFileSync(path.join(ROOT, 'docs/numbers.json'), JSON.stringify(out, null, 1) + '\n');
console.log(JSON.stringify(out, null, 1));
