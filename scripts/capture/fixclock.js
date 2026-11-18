// Freeze Date.now() and `new Date()` (no arguments) at a fixed instant so that tests
// which build timestamps from "now" produce the same inputs on every run.
'use strict';
var FIXED = Date.UTC(2026, 10, 18, 12, 0, 0); // 2026-11-18T12:00:00Z
var RealDate = Date;
function FixedDate() {
  if (!(this instanceof FixedDate)) return new RealDate(FIXED).toString();
  var args = Array.prototype.slice.call(arguments);
  if (args.length === 0) return new RealDate(FIXED);
  return new (Function.prototype.bind.apply(RealDate, [null].concat(args)))();
}
FixedDate.prototype = RealDate.prototype;
FixedDate.now = function () { return FIXED; };
FixedDate.UTC = RealDate.UTC;
FixedDate.parse = RealDate.parse;
global.Date = FixedDate;
