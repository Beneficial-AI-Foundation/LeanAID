#!/usr/bin/env node
// The tests of the JavaScript fixes (docs/FIXED.md, "The same fixes in JavaScript").
//   bash scripts/fixes/apply.sh && TZ=UTC node scripts/fixes/test.js
// 1. oref0's own test suite (mocha, tests/*.js, as `make test` runs it) on the unpatched copy,
//    on a copy with each patch alone, and on the copy with all five patches. For every test
//    that passes unpatched and fails patched, it records whether one of the test's
//    determine_basal calls had an input that triggers the patch: for F-11 a glucose_status
//    without a numeric date, for F-12 a profile whose maxSafeBasal is not a positive number.
// 2. The finding reproductions with --fixed on the patched copy (scripts/findings/run.js).
// 3. The F-23 and F-24 probes on the patched copy (scripts/probe-lgs-nan.js,
//    scripts/probe-split-timespan.js).
// Writes scripts/fixes/test-results.json. Exit code 1 if a patched copy fails a test that
// the unpatched copy passes on an input that does not trigger the patch, or if a check fails.
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var fs = require('fs');
var path = require('path');
var cp = require('child_process');
var ROOT = path.resolve(__dirname, '../..');
var OUT = path.join(__dirname, 'out');
var FIXES = ['F-04', 'F-11', 'F-12', 'F-23', 'F-24'];

function copyWith(name, patches) {
  var dir = path.join(OUT, name);
  if (!fs.existsSync(dir)) {
    cp.execFileSync('rsync', ['-a', '--exclude', '.git', path.join(ROOT, 'vendor/oref0') + '/', dir + '/']);
    patches.forEach(function (f) {
      cp.execFileSync('patch', ['-s', '-p1', '-d', dir, '-i', path.join(__dirname, f + '.patch')]);
    });
  }
  return dir;
}

// mocha on a copy, with a hook that records, per test, the triggers seen in determine_basal calls.
function mocha(dir) {
  var hook = path.join(OUT, 'mocha-hook.js');
  fs.writeFileSync(hook, [
    "'use strict';",
    "var path = require('path');",
    "var dbPath = require.resolve(path.join(process.cwd(), 'lib/determine-basal/determine-basal'));",
    "var tbf = require(path.join(process.cwd(), 'lib/basal-set-temp'));",
    "var orig = require(dbPath);",
    "var seen = {}; var title = null;",
    "function wrapped(gs, ct, iob, profile) {",
    "  if (title) {",
    "    var s = seen[title] = seen[title] || {};",
    "    if (gs && !(typeof gs.date === 'number' && isFinite(gs.date))) s['F-11'] = true;",
    "    var m; try { m = profile && tbf.getMaxSafeBasal(profile); } catch (e) { m = NaN; }",
    "    if (profile && typeof profile.current_basal !== 'undefined' && !(isFinite(m) && m > 0)) s['F-12'] = true;",
    "  }",
    "  return orig.apply(this, arguments);",
    "}",
    "require.cache[dbPath].exports = wrapped;",
    "beforeEach(function () { title = this.currentTest.fullTitle(); });",
    "after(function () { require('fs').writeFileSync(process.env.HOOK_OUT, JSON.stringify(seen)); });"
  ].join('\n') + '\n');
  var hookOut = path.join(OUT, path.basename(dir) + '-triggers.json');
  var r = cp.spawnSync(path.join(dir, 'node_modules/.bin/mocha'), ['-R', 'json', '--file', hook].concat(
    fs.readdirSync(path.join(dir, 'tests')).filter(function (f) { return /\.js$/.test(f); }).map(function (f) { return 'tests/' + f; })),
    { cwd: dir, encoding: 'utf8', maxBuffer: 1 << 28, env: Object.assign({}, process.env, { HOOK_OUT: hookOut }) });
  var j = JSON.parse(r.stdout.slice(r.stdout.indexOf('{\n')));
  var trig = fs.existsSync(hookOut) ? JSON.parse(fs.readFileSync(hookOut, 'utf8')) : {};
  return { stats: { tests: j.stats.tests, passes: j.stats.passes, failures: j.stats.failures },
    failed: j.failures.map(function (x) { return x.fullTitle; }), triggers: trig };
}

var results = { suite: {}, newFailures: {}, ok: true };
var base = mocha(copyWith('oref0', []));
results.suite.unpatched = base.stats;
var runs = FIXES.map(function (f) { return [f, [f]]; }).concat([['all five', FIXES]]);
runs.forEach(function (x) {
  var name = x[0], patches = x[1];
  var dir = name === 'all five' ? path.join(OUT, 'oref0-fixed') : copyWith('oref0-' + name, patches);
  var m = mocha(dir);
  results.suite[name] = m.stats;
  var nf = m.failed.filter(function (t) { return base.failed.indexOf(t) < 0; });
  var fixedNow = base.failed.filter(function (t) { return m.failed.indexOf(t) < 0; });
  var explained = nf.filter(function (t) { return patches.some(function (f) { return (base.triggers[t] || {})[f]; }); });
  var unexplained = nf.filter(function (t) { return explained.indexOf(t) < 0; });
  results.newFailures[name] = { count: nf.length, onTriggerInputs: explained.length, otherwise: unexplained,
    passingNow: fixedNow, tests: nf };
  if (unexplained.length) results.ok = false;
  console.log('oref0 tests, ' + name + ': ' + m.stats.passes + ' pass, ' + m.stats.failures + ' fail (unpatched ' +
    base.stats.passes + ' / ' + base.stats.failures + '); ' + nf.length + ' newly failing, ' + explained.length +
    ' of them on inputs that trigger the patch' + (unexplained.length ? '; NOT EXPLAINED: ' + unexplained.join('; ') : ''));
});

function run(cmd, args, env) {
  var r = cp.spawnSync(cmd, args, { cwd: ROOT, encoding: 'utf8', env: Object.assign({}, process.env, env || {}) });
  return r.stdout;
}
var f = run(process.execPath, ['scripts/findings/run.js', '--fixed']);
results.findings = (f.match(/^summary: (.*)$/m) || [])[1];
console.log('findings --fixed: ' + results.findings);
if (results.findings !== '{"f04":"ABSENT","f11":"ABSENT","f12":"ABSENT"}') results.ok = false;
var lgs = run(process.execPath, ['scripts/probe-lgs-nan.js', path.join(OUT, 'oref0-fixed')], { TZ: 'UTC' });
results.f23probe = lgs.split('\n').filter(function (l) { return /JSON as sent/.test(l); }).map(function (l) { return l.trim(); });
console.log('F-23 probe on the patched copy: ' + results.f23probe.join(' | '));
if (results.f23probe.some(function (l) { return /null/.test(l); })) results.ok = false;
var q6 = run(process.execPath, ['scripts/probe-split-timespan.js', path.join(ROOT, 'vendor/oref0'), path.join(OUT, 'oref0-fixed')], { TZ: 'UTC' });
results.f24probe = (q6.match(/^patched copy .*$/m) || ['missing'])[0].replace(ROOT + '/', '');
console.log('F-24 probe: ' + results.f24probe);
if (!/identical to the fix in memory in 8 of 8 cases/.test(results.f24probe)) results.ok = false;
fs.writeFileSync(path.join(__dirname, 'test-results.json'), JSON.stringify(results, null, 1) + '\n');
console.log('scripts/fixes/test.js: ' + (results.ok ? 'OK' : 'FAILED'));
process.exit(results.ok ? 0 : 1);
