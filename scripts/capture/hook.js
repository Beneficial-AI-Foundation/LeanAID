// Mocha --require hook: records every call of the in-scope oref0 functions made by
// oref0's own tests, with deep copies of the arguments (taken before the call, since
// oref0 mutates some of them) and of the result, tagged with the running test.
// Writes scripts/capture/out/<suite>.json when mocha exits.
//
// It does not modify vendor/oref0: it wraps module exports in Node's require cache.
'use strict';
var path = require('path');
var fs = require('fs');

var ROOT = path.resolve(__dirname, '../../vendor/oref0');
var OUT = path.resolve(__dirname, 'out');
var records = [];
var currentTest = null;
var seq = 0;
var depth = 0; // only top-level calls (made by the test itself) are recorded

function clone(x) {
  if (x === undefined) return { __undefined: true };
  return JSON.parse(JSON.stringify(x, function (k, v) {
    if (v === undefined) return { __undefined: true };
    if (typeof v === 'number' && !isFinite(v)) return { __number: String(v) };
    return v;
  }));
}
// Dates become ISO strings in JSON; keep them distinguishable.
function cloneArgs(args) {
  return Array.prototype.map.call(args, function (a) {
    if (a instanceof Date) return { __date: a.getTime() };
    return clone(a);
  });
}

function wrap(modPath, name, getFn, setFn) {
  var full = require.resolve(path.join(ROOT, modPath));
  var mod = require(full);
  var orig = getFn(mod);
  var wrapped = function () {
    var args = cloneArgs(arguments);
    var result, threw = null;
    depth++;
    try { result = orig.apply(this, arguments); }
    catch (e) { threw = String(e); }
    depth--;
    if (depth === 0) records.push({ seq: seq++, fn: name, test: currentTest, args: args,
                   result: threw ? null : (result instanceof Date ? { __date: result.getTime() } : clone(result)),
                   threw: threw });
    if (threw) throw new Error(threw);
    return result;
  };
  setFn(mod, wrapped, full);
}

function replaceExports(full, value) { require.cache[full].exports = value; }

// Order matters: wrap leaves first is NOT wanted (we only want top-level calls),
// so we load the real modules first, then wrap their exports.
wrap('lib/round-basal', 'round_basal', function (m) { return m; },
  function (m, w, full) { replaceExports(full, w); });
wrap('lib/determine-basal/determine-basal', 'determine_basal', function (m) { return m; },
  function (m, w, full) { replaceExports(full, w); });
wrap('lib/basal-set-temp', 'setTempBasal', function (m) { return m.setTempBasal; },
  function (m, w) { m.setTempBasal = w; });
wrap('lib/iob', 'iob', function (m) { return m; },
  function (m, w, full) { replaceExports(full, w); });
wrap('lib/glucose-get-last', 'getLastGlucose', function (m) { return m; },
  function (m, w, full) { replaceExports(full, w); });
wrap('lib/meal/history', 'findMealInputs', function (m) { return m; },
  function (m, w, full) { replaceExports(full, w); });
wrap('lib/profile/basal', 'basalLookup', function (m) { return m.basalLookup; },
  function (m, w) { m.basalLookup = w; });
wrap('lib/profile/basal', 'maxDailyBasal', function (m) { return m.maxDailyBasal; },
  function (m, w) { m.maxDailyBasal = w; });

// Root-level hooks are installed by roothooks.js (mocha 5 has no --require hooks).
global.__capture = {
  begin: function (t) { currentTest = t.fullTitle(); },
  end: function (t) {
    records.push({ seq: seq++, fn: '__result', test: currentTest, state: t.state,
                   err: t.err ? String(t.err) : null });
    currentTest = null;
  }
};

process.on('exit', function () {
  fs.mkdirSync(OUT, { recursive: true });
  var suite = process.env.CAPTURE_NAME || 'capture';
  fs.writeFileSync(path.join(OUT, suite + '.json'), JSON.stringify(records, null, 1));
});
