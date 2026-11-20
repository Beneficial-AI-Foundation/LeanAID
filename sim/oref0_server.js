// oref0 (the pinned vendor/oref0, unmodified on disk) as a long-running process for the
// closed-loop simulation. One JSON object per line on stdin, one per line on stdout.
//
//   {"cmd":"profile","inputs":{...}}  -> {"profile": <lib/profile generate(inputs)>}
//   {"cmd":"step", "pumphistory":[...], "carbhistory":[...], "glucose":[...],
//    "profile":{...}, "clock":"<ISO>", "currenttemp":{...}, "autosens":{...},
//    "microBolusAllowed":bool, "currentTime":<ms>}
//     -> {"meal": <lib/meal>, "glucose_status": <getLastGlucose>, "iob": <lib/iob array>, "suggestion": <JSON.stringify(rT)>}
//
// The step mirrors oref0's loop: oref0-meal (lib/meal), oref0-calculate-iob (lib/iob),
// oref0-determine-basal (getLastGlucose + determine_basal with basal-set-temp). Each
// input is parsed afresh, because lib/iob and lib/meal mutate their inputs; IOB and
// meal data pass through JSON between the steps, as the files of oref0's loop do.
// Run with TZ=UTC. RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
'use strict';
var path = require('path');
var readline = require('readline');
var O = path.join(__dirname, '..', 'vendor', 'oref0');
// OREF0_Q6_FIX=1: oref0 with the fix for QUIRK Q6 / FINDINGS F-24 (sim/q6fix.js, in memory).
// It must be installed before lib/iob and lib/meal are required.
if (process.env.OREF0_Q6_FIX === '1') { require('./q6fix').install(O); }
var generateProfile = require(path.join(O, 'lib/profile'));
var generateIob = require(path.join(O, 'lib/iob'));
var generateMeal = require(path.join(O, 'lib/meal'));
var getLastGlucose = require(path.join(O, 'lib/glucose-get-last'));
var determine_basal = require(path.join(O, 'lib/determine-basal/determine-basal'));
var tempBasalFunctions = require(path.join(O, 'lib/basal-set-temp'));

// oref0's modules print diagnostics on stderr; keep stdout for our protocol only.
var realLog = console.log;
console.log = console.error;

function copy(x) { return JSON.parse(JSON.stringify(x)); }

function step(m) {
  var meal = generateMeal({
    history: copy(m.pumphistory), profile: copy(m.profile), basalprofile: copy(m.profile.basalprofile),
    clock: m.clock, carbs: copy(m.carbhistory), glucose: copy(m.glucose)
  });
  meal = copy(meal);
  var iob = copy(generateIob({ history: copy(m.pumphistory), profile: copy(m.profile), clock: m.clock }));
  var gs = getLastGlucose(copy(m.glucose));
  var gsOut = copy(gs);
  var rT = determine_basal(gs, copy(m.currenttemp), copy(iob), copy(m.profile),
    m.autosens ? copy(m.autosens) : null, copy(meal), tempBasalFunctions,
    m.microBolusAllowed, null, new Date(m.currentTime));
  var out = typeof rT.error === 'undefined' ? JSON.stringify(rT) : JSON.stringify({ error: rT.error });
  return '{"meal":' + JSON.stringify(meal) + ',"glucose_status":' + JSON.stringify(gsOut) + ',"iob":' + JSON.stringify(iob) + ',"suggestion":' + out + '}';
}

var rl = readline.createInterface({ input: process.stdin, terminal: false });
rl.on('line', function (line) {
  if (!line.trim()) return;
  var res;
  try {
    var m = JSON.parse(line);
    if (m.cmd === 'profile') {
      var final_result = { stdout: '', err: '', return_val: 0 };
      res = JSON.stringify({ profile: generateProfile(final_result, m.inputs) });
    } else {
      res = step(m);
    }
  } catch (e) {
    res = JSON.stringify({ exception: String(e && e.stack || e) });
  }
  process.stdout.write(res + '\n');
});
