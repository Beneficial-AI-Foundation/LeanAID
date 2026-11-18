// Regression cases for the IEEE-754 model: runs `aid-lean batch` on the inputs kept
// in regression-no-tie.jsonl (F-14; compared byte for byte with the stored oref0
// output) and worst-rate-diffs.jsonl (F-15; the issued rate compared with the stored
// oref0 rate). Exit 1 on any difference. Run from the repository root (after `lake build aid-lean`):
//   TZ=UTC node scripts/difftest/regress.js
var fs = require('fs'), path = require('path'), cp = require('child_process');
var ROOT = path.join(__dirname, '..', '..');
var files = ['regression-no-tie.jsonl', 'worst-rate-diffs.jsonl'];
var cases = [];
files.forEach(function (f) {
  fs.readFileSync(path.join(__dirname, f), 'utf8').split('\n').filter(Boolean).forEach(function (l) {
    var d = JSON.parse(l); d.file = f; cases.push(d);
  });
});
var OUT = path.join(__dirname, 'out');
fs.mkdirSync(OUT, { recursive: true });
var inFile = path.join(OUT, 'regress.jsonl');
fs.writeFileSync(inFile, cases.map(function (c) { return JSON.stringify(c.input); }).join('\n') + '\n');
var lean = cp.execFileSync(path.join(ROOT, '.lake/build/bin/aid-lean'), ['batch', inFile],
  { encoding: 'utf8', maxBuffer: 1 << 28 }).split('\n');
var bad = 0;
cases.forEach(function (c, i) {
  var same = c.oref0 !== undefined ? lean[i] === c.oref0
    : JSON.stringify(JSON.parse(lean[i]).rate) === JSON.stringify(c.oref0Rate);
  if (!same) bad++;
  var what = c.oref0 !== undefined ? 'output' : 'rate';
  console.log((same ? 'same ' : 'DIFFERENT ') + what + ': ' + c.file + ' case ' + c.case);
});
console.log(cases.length - bad + '/' + cases.length + ' regression cases agree with oref0');
process.exit(bad ? 1 : 0);
