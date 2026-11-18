#!/usr/bin/env node
// Generates LeanAID/Proofs/Tests.lean: for each class A/B oref0 test,
//  * `<id>_test`: the test's own assertions on oref0's inputs, proved by kernel
//    evaluation (`decide +kernel`, not `native_decide`);
//  * `<id>_general`: the general theorem the test is an instance of, instantiated
//    on the test's input (when one is proved).
// Also writes scripts/test-theorems.json (theorem name and status per test).
'use strict';
var fs = require('fs');
var path = require('path');
var ROOT = path.resolve(__dirname, '..');
var inv = JSON.parse(fs.readFileSync(path.join(ROOT, 'docs/tests-inventory.json'), 'utf8'));
var cls = JSON.parse(fs.readFileSync(path.join(__dirname, 'test-classes.json'), 'utf8'));
var dbLean = fs.readFileSync(path.join(ROOT, 'LeanAID/Conformance/Data/DetermineBasalData.lean'), 'utf8');

// case name in DetermineBasalData for each test id (in order)
var caseOf = {};
var re = /\/-- (DB-\d+): [^\n]*-\/\ndef (c\d+) : DBCase/g, m;
while ((m = re.exec(dbLean))) { (caseOf[m[1]] = caseOf[m[1]] || []).push(m[2]); }

function jsNum(x) { x = String(x).trim(); return x.startsWith('-') ? '(-' + x.slice(1) + ' : JsNum)' : '(' + x + ' : JsNum)'; }
function pieces(regex) {
  var body = regex.replace(/^\//, '').replace(/\/[a-z]*$/, '');
  return body.split('.*').filter(function (p) { return p.length > 0; }).map(function (p) { return p.replace(/\\/g, ''); });
}
// Translate one assertion line to a Lean Bool over `r : Result`. null if unsupported.
function assertion(a) {
  var t = a.replace(/;\s*$/, '');
  var mm;
  if ((mm = t.match(/^output\.rate\.should\.equal\(([-\d.]+)\)$/))) return 'r.rate == some ' + jsNum(mm[1]);
  if ((mm = t.match(/^output\.rate\.should\.be\.above\(([-\d.]+)\)$/))) return '(r.rate.js >ʲ ' + jsNum(mm[1]) + ')';
  if ((mm = t.match(/^output\.rate\.should\.be\.below\(([-\d.]+)\)$/))) return '(r.rate.js <ʲ ' + jsNum(mm[1]) + ')';
  if ((mm = t.match(/^output\.duration\.should\.equal\(([-\d.]+)\)$/))) return 'r.duration == some ' + jsNum(mm[1]);
  if ((mm = t.match(/^output\.duration\.should\.be\.above\(([-\d.]+)\)$/))) return '(r.duration.js >ʲ ' + jsNum(mm[1]) + ')';
  if (/^\(typeof output\.rate\)\.should\.equal\('undefined'\)$/.test(t)) return 'r.rate.isNone';
  if (/^\(typeof output\.duration\)\.should\.equal\('undefined'\)$/.test(t)) return 'r.duration.isNone';
  if ((mm = t.match(/^output\.reason\.should\.match\((\/.*\/)\)$/)))
    return 'reasonHas r [' + pieces(mm[1]).map(function (p) { return JSON.stringify(p); }).join(', ') + ']';
  if ((mm = t.match(/^result\.error\.should\.equal\('(.*)'\)$/))) return 'r.error == some ' + JSON.stringify(mm[1]);
  return null;
}

// general theorem per test (name, Lean proof of the instance)
function instance(id, cn) {
  var I = 'DetermineBasalData.' + cn + '.input';
  var V = '(validInputB_sound (by decide +kernel))';
  var P = '(okOf (by decide +kernel))';
  switch (id) {
    case 'DB-18': case 'DB-65': case 'DB-66': case 'DB-67': case 'DB-68':
      return ['rate_le_roundBasal_maxSafeBasal',
        'theorem ' + nm(id) + '_general : ∀ p M r, ' + I + '.profile = some p → getMaxSafeBasal p = .fin M →\n' +
        '    (determineBasal ' + I + ').rate = some (.fin r) → 0 ≤ r ∧ r ≤ rbR M p.model :=\n' +
        '  fun _ _ _ hp hM hr => rate_le_roundBasal_maxSafeBasal ' + V + ' hp hM hr'];
    case 'DB-23': case 'DB-24': case 'DB-25':
      return ['low_glucose_suspend',
        'theorem ' + nm(id) + '_general : (determineBasal ' + I + ').units = none ∧\n' +
        '    ((determineBasal ' + I + ').rate = some 0 ∨ ((determineBasal ' + I + ').rate = none ∧\n' +
        '      ∃ c x, ' + I + '.currenttemp = some c ∧ c.rate = some (.fin x) ∧ (Binary64.rd x = x → x = 0))) :=\n' +
        '  low_glucose_suspend ' + V + ' ' + P + ' (Or.inl (by decide +kernel)) (Or.inr (by decide +kernel))'];
    case 'DB-22':
      return ['iob_at_max',
        'theorem ' + nm(id) + '_general : (determineBasal ' + I + ').units = none ∧\n' +
        '    ∃ b, (preOf ' + I + ').basal = .fin b ∧ ∀ r, (determineBasal ' + I + ').rate = some (.fin r) → 0 ≤ r ∧ r ≤ b :=\n' +
        '  iob_at_max (i := 3.5) (mi := 2.5) ' + V + ' ' + P + ' (by decide +kernel) (by decide +kernel) (by decide +kernel)'];
    case 'DB-08': case 'DB-13': case 'DB-14': case 'DB-26': case 'DB-27': case 'DB-28': case 'DB-34': case 'DB-64':
      return ['low_eventual_rate_le_basal',
        'theorem ' + nm(id) + '_general : ∃ b, (preOf ' + I + ').basal = .fin b ∧\n' +
        '    ∀ r, (determineBasal ' + I + ').rate = some (.fin r) → 0 ≤ r ∧ r ≤ b :=\n' +
        '  low_eventual_rate_le_basal ' + V + ' ' + P + ' (by decide +kernel)'];
    case 'DB-06': case 'DB-10': case 'DB-31': case 'DB-32': case 'DB-33': case 'DB-36': case 'DB-37': case 'DB-38': case 'DB-69': case 'DB-70':
      return ['dbDose_neutral',
        'theorem ' + nm(id) + '_general : ∃ rT\', dbDose (dbPredict ' + I + ' (preOf ' + I + ')) =\n' +
        '    neutralTemp (dbPredict ' + I + ' (preOf ' + I + ')) rT\' := by\n' +
        '  obtain ⟨rT\', -, -, h⟩ := dbDose_neutral (c := dbPredict ' + I + ' (preOf ' + I + '))\n' +
        '    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)\n' +
        '    (by first | exact Or.inl (by decide +kernel) | exact Or.inr (by decide +kernel))\n' +
        '  exact ⟨rT\', h⟩'];
    case 'DB-44': case 'DB-45':
      return ['cgmError_no_increase',
        'theorem ' + nm(id) + '_general : ∀ p gs, ' + I + '.profile = some p → ' + I + '.glucose_status = some gs →\n' +
        '    (determineBasal ' + I + ').units = none ∧\n' +
        '    ((∃ ct, ' + I + '.currenttemp = some ct ∧ (ct.rate.js >ʲ profileCurrentBasal p) = true ∧\n' +
        '        (determineBasal ' + I + ').rate = some (profileCurrentBasal p)) ∨\n' +
        '     (determineBasal ' + I + ').rate = some 0 ∨\n' +
        '     ((determineBasal ' + I + ').rate = none ∧ ∀ ct, ' + I + '.currenttemp = some ct →\n' +
        '        (ct.rate.js >ʲ profileCurrentBasal p) = false)) := by\n' +
        '  intro p gs hp hgs\n' +
        '  have hp\' := hp; have hgs\' := hgs\n' +
        '  injection hp with hp; injection hgs with hgs; subst hp; subst hgs\n' +
        '  exact cgmError_no_increase hp\' (by decide +kernel) hgs\' (by decide +kernel)'];
    case 'DB-43':
      return ['missing_current_basal',
        'theorem ' + nm(id) + '_general : (determineBasal ' + I + ').error = some "Error: could not get current basal rate" ∧\n' +
        '    (determineBasal ' + I + ').rate = none ∧ (determineBasal ' + I + ').units = none :=\n' +
        '  missing_current_basal (Or.inl rfl)'];
  }
  return null;
}
function nm(id) { return id.replace('-', '_'); }

var out = [];
out.push('/-');
out.push('  LeanAID.Proofs.Tests — oref0\'s class A and B unit tests as theorems (M6).');
out.push('  GENERATED by scripts/gen_test_theorems.js. Do not edit.');
out.push('');
out.push('  For each test: `<id>_test` states the test\'s own assertions about oref0\'s');
out.push('  inputs and is proved by kernel evaluation; `<id>_general`, when present, is the');
out.push('  general theorem the test is an instance of, applied to the same input.');
out.push('  Regex assertions on `reason` are checked as "these literal pieces occur in');
out.push('  order" (each `.*` of the regex separates pieces; a literal `.` is required).');
out.push('-/');
out.push('import LeanAID.Proofs.Lifted');
out.push('import LeanAID.Proofs.ValidCheck');
out.push('import LeanAID.Conformance.Data.DetermineBasalData');
out.push('import LeanAID.Conformance.Data.SmallData');
out.push('');
out.push('namespace LeanAID.Proofs.Tests');
out.push('');
out.push('open LeanAID LeanAID.Proofs LeanAID.Conformance JsNum');
out.push('');
out.push('def prefixL : List Char → List Char → Bool');
out.push('  | [], _ => true');
out.push('  | _ :: _, [] => false');
out.push('  | a :: as, b :: bs => a == b && prefixL as bs');
out.push('');
out.push('/-- The rest of `s` after the first occurrence of `p`. -/');
out.push('def afterL (p : List Char) : List Char → Option (List Char)');
out.push('  | [] => if p.isEmpty then some [] else none');
out.push('  | c :: cs => if prefixL p (c :: cs) then some ((c :: cs).drop p.length) else afterL p cs');
out.push('');
out.push('/-- The literal pieces occur in `s` in this order. -/');
out.push('def piecesL (s : List Char) : List (List Char) → Bool');
out.push('  | [] => true');
out.push('  | p :: ps => match afterL p s with');
out.push('    | some rest => piecesL rest ps');
out.push('    | none => false');
out.push('');
out.push('def reasonHas (r : Result) (ps : List String) : Bool := piecesL (r.reason.getD "").toList (ps.map String.toList)');
out.push('');
out.push('/-- The prelude\'s result, for inputs on which it succeeds. -/');
out.push('def preOf (inp : DBInputs) : Pre := match dbPrelude inp with | .ok p => p | .error _ => default');
out.push('');
out.push('theorem okOf {inp : DBInputs} (h : (dbPrelude inp).isOk = true) : dbPrelude inp = .ok (preOf inp) := by');
out.push('  unfold preOf; cases hp : dbPrelude inp <;> simp_all [Except.isOk, Except.toBool]');
out.push('');

var status = {};
inv.forEach(function (t) {
  var c = cls[t.id] || {};
  if (t.commented || (c.class !== 'A' && c.class !== 'B')) return;
  if (!/^DB-/.test(t.id) || ['DB-01', 'DB-02', 'DB-03', 'DB-04', 'DB-05'].indexOf(t.id) >= 0) return;
  var cns = caseOf[t.id] || [];
  if (cns.length === 0) { status[t.id] = { status: 'no captured call' }; return; }
  var cn = cns[0];
  if (t.id === 'DB-28') cn = cns[1] || cns[0];   // two tests share this title
  var asserts = t.asserts.map(assertion);
  if (asserts.some(function (x) { return x === null; })) { status[t.id] = { status: 'assertion not translated' }; return; }
  out.push('/-- ' + t.id + ': ' + t.name.replace(/-\//g, '- /') + ' -/');
  out.push('theorem ' + nm(t.id) + '_test :');
  out.push('    let r := determineBasal DetermineBasalData.' + cn + '.input');
  out.push('    (' + (asserts.length ? asserts.join(' &&\n      ') : 'true') + ') = true := by');
  out.push('  decide +kernel');
  out.push('');
  var g = instance(t.id, cn);
  if (g) {
    out.push(g[1]);
    out.push('');
    status[t.id] = { theorem: g[0] + ' (' + nm(t.id) + '_general)', status: 'proved: general theorem + instance; test assertions by evaluation (' + nm(t.id) + '_test)' };
  } else {
    status[t.id] = { theorem: nm(t.id) + '_test', status: 'test assertions proved by evaluation; general theorem not proved (planned)' };
  }
});
out.push('end LeanAID.Proofs.Tests');
fs.writeFileSync(path.join(ROOT, 'LeanAID/Proofs/Tests.lean'), out.join('\n') + '\n');
fs.writeFileSync(path.join(__dirname, 'test-theorems.gen.json'), JSON.stringify(status, null, 1));
console.log('Tests.lean: ' + Object.keys(status).length + ' tests');
