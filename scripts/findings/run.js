'use strict';
// Runs f04.js, f11.js and f12.js against one lib/ directory.
// Usage: node scripts/findings/run.js [path/to/lib] [--fixed]   (default vendor/oref0/lib)
// Dependencies (lodash, ...) are taken from vendor/oref0/node_modules via NODE_PATH,
// so a cloned descendant's lib/ can be tested without installing anything.
// Exit code: 0 if every finding ran (any verdict), 3 if a script failed to run.
var path = require('path');
var cp = require('child_process');
var repo = path.resolve(__dirname, '..', '..');
// --fixed: the patched copy of scripts/fixes/apply.sh by default, and each script in its --fixed
// mode (docs/FIXED.md); the expected summary is then ABSENT for all three.
var fixed = process.argv.indexOf('--fixed') >= 0;
var args = process.argv.slice(2).filter(function (a) { return a !== '--fixed'; });
var lib = path.resolve(args[0] || (fixed ? path.join(repo, 'scripts', 'fixes', 'out', 'oref0-fixed', 'lib')
                                         : path.join(repo, 'vendor', 'oref0', 'lib')));
var np = [path.join(repo, 'vendor', 'oref0', 'node_modules')];
if (process.env.NODE_PATH) np.push(process.env.NODE_PATH);
var env = Object.assign({}, process.env, {NODE_PATH: np.join(path.delimiter)});
console.log('lib: ' + lib);
var bad = 0, summary = {};
['f04', 'f11', 'f12'].forEach(function (f) {
  var r = cp.spawnSync(process.execPath, [path.join(__dirname, f + '.js'), lib].concat(fixed ? ['--fixed'] : []),
                       {env: env, encoding: 'utf8'});
  process.stdout.write(r.stdout);
  if (r.status === null || r.status > 2) { bad = 1; process.stdout.write(r.stderr); }
  summary[f] = ['PRESENT', 'ABSENT', 'INCONCLUSIVE'][r.status] || 'ERROR';
});
console.log('summary: ' + JSON.stringify(summary));
process.exit(bad ? 3 : 0);
