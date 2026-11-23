// Combine the istanbul runs of scripts/coverage/run.sh into docs/coverage.json and
// docs/COVERAGE.md.
//   node scripts/coverage/report.js [N] [S] [M]
// N, S: cases and seed of scripts/difftest/run.js; M: cases of scripts/difftest/iob.js (seed S).
// A branch is one outcome of an `if`, `?:`, `switch` case or one operand of
// `&&` / `||`, as istanbul 0.4.5 counts them. Branches that no source reaches are listed
// with the argument from scripts/coverage/unreachable.json if there is one.
var fs = require('fs');
var path = require('path');
var ROOT = path.resolve(__dirname, '../..');
var OUT = path.join(ROOT, 'scripts/coverage/out');
var LIB = path.join(ROOT, 'vendor/oref0/lib');
var N = process.argv[2] || '100000';
var S = process.argv[3] || '1';
var M = process.argv[4] || '10000';

// The sources, in the order of the table columns. `dir` is the istanbul output directory.
var SOURCES = [
  { key: 'oref0Tests', dir: 'oref0-tests', label: 'oref0 tests',
    what: 'oref0\'s own mocha suite (`tests/*.test.js`)' },
  { key: 'difftest', dir: 'difftest', label: 'difftest',
    what: '`scripts/difftest/run.js`, ' + N + ' random determine-basal cases (seed ' + S + '), with ready-made IOB and meal data' },
  { key: 'targeted', dir: 'targeted', label: 'targeted',
    what: '`scripts/difftest/targeted.js`: the hand-made determine-basal cases of `scripts/difftest/targeted.jsonl`' },
  { key: 'iobtest', dir: 'iobtest', label: 'IOB difftest',
    what: '`scripts/difftest/iob.js`, ' + M + ' random pump histories, carb histories and profiles (seed ' + S + ') ' +
      'and the hand-made cases of `scripts/difftest/iob-targeted.jsonl`, through lib/iob, lib/meal/history.js and basalLookup' }
];

function load(dir) {
  var f = path.join(OUT, dir, 'coverage.json');
  if (!fs.existsSync(f)) return null;
  var raw = JSON.parse(fs.readFileSync(f, 'utf8'));
  var m = {};
  Object.keys(raw).forEach(function (k) {
    var i = k.indexOf('/vendor/oref0/lib/');
    if (i >= 0) m[k.slice(i + '/vendor/oref0/lib/'.length)] = raw[k];
  });
  return m;
}
// Several istanbul runs may make up one source (directories dir, dir-2, dir-3, ...).
function loadSource(s) {
  var runs = fs.readdirSync(OUT).filter(function (d) { return d === s.dir || d.indexOf(s.dir + '-') === 0; })
    .map(load).filter(Boolean);
  if (!runs.length) return null;
  var m = {};
  runs.forEach(function (r) {
    Object.keys(r).forEach(function (f) {
      if (!m[f]) { m[f] = JSON.parse(JSON.stringify(r[f])); return; }
      Object.keys(r[f].b).forEach(function (k) { r[f].b[k].forEach(function (v, i) { m[f].b[k][i] += v; }); });
    });
  });
  return m;
}
var data = {};
SOURCES.forEach(function (s) { data[s.key] = loadSource(s); });
var sources = SOURCES.filter(function (s) { return data[s.key]; });
var unreachable = JSON.parse(fs.readFileSync(path.join(__dirname, 'unreachable.json'), 'utf8'));

// files modelled in Lean (docs/DESIGN.md); the others are listed for reference
var MODELLED = ['determine-basal/determine-basal.js', 'basal-set-temp.js', 'round-basal.js',
  'glucose-get-last.js', 'iob/index.js', 'iob/history.js', 'iob/calculate.js', 'iob/total.js',
  'meal/history.js', 'profile/basal.js'];

function hits(v, k, i) { return v && v.b[k] ? v.b[k][i] > 0 : false; }

var files = [];
sources.forEach(function (s) { Object.keys(data[s.key]).forEach(function (f) { if (files.indexOf(f) < 0) files.push(f); }); });
files.sort();

var result = { generated: new Date().toISOString(), oref0: 'vendor/oref0 (0.7.1)',
  sources: sources.map(function (s) { return { key: s.key, what: s.what }; }), files: {} };

var srcCache = {};
function srcLines(f) { return srcCache[f] || (srcCache[f] = fs.readFileSync(path.join(LIB, f), 'utf8').split('\n')); }

files.forEach(function (f) {
  var map = null;
  sources.forEach(function (s) { if (!map && data[s.key][f]) map = data[s.key][f].branchMap; });
  var src = srcLines(f);
  var r = { modelled: MODELLED.indexOf(f) >= 0, branches: 0, combined: 0, by: {}, missed: [] };
  sources.forEach(function (s) { r.by[s.key] = data[s.key][f] ? 0 : null; });
  Object.keys(map).forEach(function (k) {
    map[k].locations.forEach(function (loc, i) {
      r.branches++;
      var any = false;
      sources.forEach(function (s) {
        if (hits(data[s.key][f], k, i)) { r.by[s.key]++; any = true; }
      });
      if (any) { r.combined++; return; }
      var line = map[k].line;
      var key = f + ':' + line + ':' + map[k].type + ':' + i;
      r.missed.push({ line: line, type: map[k].type, outcome: i, source: (src[line - 1] || '').trim().slice(0, 120),
        unreachable: unreachable[key] ? true : false });
    });
  });
  result.files[f] = r;
});

fs.writeFileSync(path.join(ROOT, 'docs/coverage.json'), JSON.stringify(result, null, 1) + '\n');

function pct(x, n) { return n ? (100 * x / n).toFixed(1) + ' %' : '–'; }
function cell(x, n) { return x === null ? 'not reached' : x + ' (' + pct(x, n) + ')'; }

var md = [];
md.push('# Branch coverage of oref0');
md.push('');
md.push('Generated by `bash scripts/coverage/run.sh ' + N + ' ' + S + ' ' + M + '` (istanbul 0.4.5, declared by oref0)');
md.push('on ' + result.generated.slice(0, 10) + '. Source: `vendor/oref0/lib` (0.7.1). A branch is one outcome');
md.push('of an `if`, `?:`, `switch` case, or one operand of `&&` / `||`. Full data: `docs/coverage.json`.');
md.push('');
md.push('Sources:');
md.push('');
sources.forEach(function (s) { md.push('- **' + s.label + '**: ' + s.what + '.'); });
md.push('');
md.push('Every case of the three differential sources is also run through `aid-lean` and compared with');
md.push('oref0 (`docs/difftest.json`, `docs/iobtest.json`, `scripts/difftest/targeted.js`).');
md.push('');
var head = '| file | branches | ' + sources.map(function (s) { return s.label; }).join(' | ') + ' | combined | unreachable |';
var rule = '|---|--:|' + sources.map(function () { return '--:'; }).join('|') + '|--:|--:|';
function row(f) {
  var r = result.files[f];
  var u = r.missed.filter(function (m) { return m.unreachable; }).length;
  return '| `' + f + '` | ' + r.branches + ' | ' + sources.map(function (s) { return cell(r.by[s.key], r.branches); }).join(' | ') +
    ' | ' + r.combined + ' (' + pct(r.combined, r.branches) + ') | ' + u + ' |';
}
md.push('## Files modelled in Lean');
md.push('');
md.push(head);
md.push(rule);
var other = [];
files.forEach(function (f) { if (result.files[f].modelled) md.push(row(f)); else other.push(f); });
md.push('');
var open = [];
files.forEach(function (f) {
  var r = result.files[f];
  if (r.modelled) r.missed.forEach(function (m) { if (!m.unreachable) open.push(f + ':' + m.line + ' ' + m.type + ' ' + m.outcome); });
});
md.push(open.length ? '**' + open.length + ' branches of the modelled files are reached by no source and have no argument for being unreachable:** ' + open.join(', ') + '.'
  : 'Every branch of the modelled files is reached by at least one source, except those argued unreachable below.');
md.push('');
md.push('## Branches of the modelled files that no source reaches');
md.push('');
md.push('Outcome 0 is the `then` side of an `if` (or the first operand of `&&` / `||`), 1 the `else` side (or the second operand), and so on.');
md.push('Each argument quotes the lines it relies on, copied from `vendor/oref0/lib` by `scripts/coverage/report.js`; the arguments are in');
md.push('`scripts/coverage/unreachable.json`.');
md.push('');
files.forEach(function (f) {
  var r = result.files[f];
  if (!r.modelled || !r.missed.length) return;
  md.push('### `' + f + '` (' + r.missed.length + ')');
  md.push('');
  r.missed.forEach(function (m) {
    var key = f + ':' + m.line + ':' + m.type + ':' + m.outcome;
    var u = unreachable[key];
    md.push('**Line ' + m.line + ', ' + m.type + ', outcome ' + m.outcome + '**: `' + m.source + '`');
    md.push('');
    if (!u) { md.push('Not reached, and no argument that it is unreachable.'); md.push(''); return; }
    md.push((u.kind === 'not-transcribed' ? 'Not part of the transcription. ' : 'Unreachable (' + u.scope + '). ') + u.why);
    md.push('');
    md.push('```js');
    u.quote.forEach(function (q) {
      var lines = srcLines(q[0]);
      md.push('// ' + q[0]);
      for (var n = q[1]; n <= q[2]; n++) md.push(String(n).padStart(4) + '  ' + lines[n - 1]);
    });
    md.push('```');
    md.push('');
  });
});
md.push('## Other files loaded by the tests (not modelled)');
md.push('');
md.push(head);
md.push(rule);
other.forEach(function (f) { md.push(row(f)); });
md.push('');
fs.writeFileSync(path.join(ROOT, 'docs/COVERAGE.md'), md.join('\n'));

files.forEach(function (f) {
  var r = result.files[f];
  if (!r.modelled) return;
  var u = r.missed.filter(function (m) { return m.unreachable; }).length;
  console.log(f + ': combined ' + r.combined + '/' + r.branches + ' (' + pct(r.combined, r.branches) + '), ' + u +
    ' argued unreachable, ' + (r.missed.length - u) + ' open');
});
console.log('wrote docs/coverage.json, docs/COVERAGE.md');
