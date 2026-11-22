'use strict';
// Builds an oref0-shaped lib/ of shims over webpack bundles (as shipped by iAPS in
// FreeAPS/Resources/javascript/bundle/, library type 'var', names freeaps_<entry>), so the
// Part 1 scripts can run on the bundled code unchanged. Each shim evaluates one bundle in a
// fresh vm context and exports the global it defines. Nothing in the bundle dir is changed.
// Usage: node scripts/findings/make-bundle-lib.js <bundle dir> <output lib dir> [prefix]
var fs = require('fs'), path = require('path');
var bundle = path.resolve(process.argv[2]), out = path.resolve(process.argv[3]);
var prefix = process.argv[4] || 'freeaps_';
var map = {
  'basal-set-temp.js': ['basal-set-temp.js', 'basalSetTemp'],
  'determine-basal/determine-basal.js': ['determine-basal.js', 'determineBasal'],
  'glucose-get-last.js': ['glucose-get-last.js', 'glucoseGetLast']
};
Object.keys(map).forEach(function (rel) {
  var src = path.join(bundle, map[rel][0]), name = prefix + map[rel][1];
  if (!fs.existsSync(src)) { console.log('missing ' + src); return; }
  var dst = path.join(out, rel);
  fs.mkdirSync(path.dirname(dst), {recursive: true});
  fs.writeFileSync(dst,
    "var vm = require('vm'), fs = require('fs');\n" +
    "// iAPS prepare/log.js defines process = { stderr: { write: printLog } }; same here\n" +
    "var ctx = {console: console, Date: Date, Math: Math, JSON: JSON, isNaN: isNaN, parseFloat: parseFloat,\n" +
    "  process: {stderr: {write: function (s) { return process.stderr.write(s); }}}};\n" +
    "vm.createContext(ctx);\n" +
    "vm.runInContext(fs.readFileSync(" + JSON.stringify(src) + ", 'utf8') + '\\n;this.__x = " + name + ";', ctx);\n" +
    "module.exports = ctx.__x;\n");
  console.log(rel + ' -> ' + src + ' (' + name + ')');
});
