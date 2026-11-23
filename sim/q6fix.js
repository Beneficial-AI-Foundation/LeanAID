// The fix for QUIRK Q6 / FINDINGS F-24, applied in memory. The oref0 checkout is not
// changed. In splitTimespan (lib/iob/history.js lines 51-80) the flag `splitFound` is
// shared by all pieces of one pass, so a piece that does not split is dropped once an
// earlier piece of the pass has split. The fix gives each piece its own flag and keeps
// `splitFound` as the condition for another pass.
//
//   require('./q6fix').load(O)     -> calcTempTreatments with the fix
//   require('./q6fix').install(O)  -> also puts it into require's cache, so that lib/iob
//                                     and lib/meal, required afterwards, use it
// RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var path = require('path');
var fs = require('fs');
var Module = require('module');

function once(s, a, b) {
  if (s.split(a).length !== 2) { throw new Error('q6fix: patch anchor not found once: ' + a); }
  return s.replace(a, b);
}

function patchedSource(src) {
  var s = once(src, '_.forEach(results,function split(o) {',
    '_.forEach(results,function split(o) { var thisSplit = false;');
  var n = 0;
  s = s.replace(/splitFound = true;(\s*)return false;/g, function (m, ws) {
    n += 1;
    return 'splitFound = true; thisSplit = true;' + ws + 'return false;';
  });
  if (n !== 1) { throw new Error('q6fix: patch anchor "splitFound = true; return false;" found ' + n + ' times'); }
  return once(s, 'if (!splitFound) resultArray = resultArray.concat([o]);',
    'if (!thisSplit) resultArray = resultArray.concat([o]);');
}

function compile(O) {
  var file = fs.realpathSync(path.join(O, 'lib/iob/history.js'));   // require's cache uses real paths
  var m = new Module(file, module);
  m.filename = file;
  m.paths = Module._nodeModulePaths(path.dirname(file));
  m._compile(patchedSource(fs.readFileSync(file, 'utf8')), file);
  m.loaded = true;
  return m;
}

exports.load = function (O) { return compile(O).exports; };

exports.install = function (O) {
  var m = compile(O);
  require.cache[m.filename] = m;
  if (require(path.join(O, 'lib/iob/history')) !== m.exports) {
    throw new Error('q6fix: lib/iob/history does not resolve to the fixed module');
  }
  return m.exports;
};
