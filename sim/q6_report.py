"""Report for FINDINGS F-24 (QUIRK Q6), from the runs of sim/q6_runs.py.

RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.

Open loop (shadow): along each oref0 run, oref0 with the Q6 fix ran on the same input.
  - Any difference: the whole IOB array (48 points, lastTemp, lastBolusTime) or the
    suggestion (including forecasts and reason text) differs.
  - IOB difference: |iob[0] fixed - iob[0] oref0| > 0.0005 U (IOB is printed to 3 decimals).
  - Action difference: rate, duration or microbolus units differ (the reason text and the
    predictions are not compared).
Closed loop: oref0 against oref0-q6fix, paired by patient and meal seed.
Each basal schedule of sim/q6_runs.py is reported on its own.

Writes sim/out/q6-report.json and prints the tables of docs/SIM.md.
Usage: .venv/bin/python sim/q6_report.py
"""
import json
import os
import statistics as st
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'sim'))
import harness  # noqa: E402
from q6_runs import OUT, SEEDS, DAYS, BASALS  # noqa: E402

GROUPS = ['child', 'adolescent', 'adult']
METRICS = ['tir_70_180', 'below_70', 'below_54', 'above_180', 'mean_bg', 'min_bg', 'insulin_per_day']


def load(p, ctrl, seed, basal):
    rid = harness.run_id(p, ctrl, DAYS, seed, 'none', basal)
    with open(os.path.join(OUT, rid + '.summary.json')) as f:
        return json.load(f)


def action(r):
    return (r.get('rate'), r.get('duration'), r.get('units') or 0)


def report(basal):
    shadow = {g: dict(steps=0, iob_diff=0, action_diff=0, max_iob_diff=0.0, rate_diffs=[],
                      iob_diffs=[], runs_with_iob_diff=0, runs_with_action_diff=0, runs=0) for g in GROUPS}
    pairs = []
    examples = []
    anydiff = dict(steps=0, runs=0, suggestion_steps=0, suggestion_runs=0, action_steps=0)
    for seed in SEEDS:
        for p in harness.PATIENTS:
            g = p.split('#')[0]
            a = load(p, 'oref0', seed, basal)
            b = load(p, 'oref0-q6fix', seed, basal)
            q = a['q6_shadow']
            s = shadow[g]
            s['runs'] += 1
            s['steps'] += q['compared']
            n_iob = n_act = 0
            n_sug = sum(1 for d in q['diffs'] if not d['same_decision'])
            anydiff['steps'] += len(q['diffs'])
            anydiff['runs'] += bool(q['diffs'])
            anydiff['suggestion_steps'] += n_sug
            anydiff['suggestion_runs'] += n_sug > 0
            for d in q['diffs']:
                di = None
                if d['iob'] is not None and d['iob_fixed'] is not None:
                    di = d['iob_fixed'] - d['iob']
                if di is not None and abs(di) > 0.0005:
                    n_iob += 1
                    s['iob_diffs'].append(di)
                    s['max_iob_diff'] = max(s['max_iob_diff'], abs(di))
                if action(d['oref0']) != action(d['fixed']):
                    n_act += 1
                    ro, rf = d['oref0'].get('rate'), d['fixed'].get('rate')
                    if isinstance(ro, (int, float)) and isinstance(rf, (int, float)):
                        s['rate_diffs'].append(rf - ro)
                    if len(examples) < 10:
                        examples.append(dict(d, patient=p, seed=seed))
            anydiff['action_steps'] += n_act
            s['iob_diff'] += n_iob
            s['action_diff'] += n_act
            s['runs_with_iob_diff'] += n_iob > 0
            s['runs_with_action_diff'] += n_act > 0
            pairs.append({'patient': p, 'group': g, 'seed': seed,
                          **{m: [a[m], b[m]] for m in METRICS}, 'steps': a['steps']})

    def summ(xs):
        if not xs:
            return None
        return {'n': len(xs), 'mean': st.mean(xs), 'min': min(xs), 'max': max(xs)}

    out = {'open_loop': {}, 'closed_loop': {}, 'pairs': pairs, 'action_diff_examples': examples,
           'setup': {'seeds': SEEDS, 'days': DAYS, 'basal_schedule': harness.BASAL_SCHEDULES[basal]}}
    print('## basal schedule', basal)
    print('Open loop (oref0 runs, fixed oref0 in shadow)')
    print('| group | runs | steps | steps with IOB diff | max IOB diff | steps with other action | rate diff (fixed - oref0) |')
    print('|---|--:|--:|--:|--:|--:|---|')
    tot = dict(runs=0, steps=0, iob_diff=0, action_diff=0)
    for g in GROUPS + ['all']:
        if g == 'all':
            s = {k: sum(shadow[x][k] for x in GROUPS) for k in ('runs', 'steps', 'iob_diff', 'action_diff',
                                                               'runs_with_iob_diff', 'runs_with_action_diff')}
            s['max_iob_diff'] = max(shadow[x]['max_iob_diff'] for x in GROUPS)
            s['rate_diffs'] = sum((shadow[x]['rate_diffs'] for x in GROUPS), [])
            s['iob_diffs'] = sum((shadow[x]['iob_diffs'] for x in GROUPS), [])
        else:
            s = shadow[g]
        rd = summ(s['rate_diffs'])
        out['open_loop'][g] = {k: v for k, v in s.items() if k not in ('rate_diffs', 'iob_diffs')}
        out['open_loop'][g]['rate_diff'] = rd
        out['open_loop'][g]['iob_diff_summary'] = summ(s['iob_diffs'])
        print('| %s | %d | %d | %d (%.2f %%; %d runs) | %.3f U | %d (%.2f %%; %d runs) | %s |' % (
            g, s['runs'], s['steps'], s['iob_diff'], 100.0 * s['iob_diff'] / max(1, s['steps']), s['runs_with_iob_diff'],
            s['max_iob_diff'], s['action_diff'], 100.0 * s['action_diff'] / max(1, s['steps']), s['runs_with_action_diff'],
            ('mean %+.3f, min %+.3f, max %+.3f U/h (n=%d)' % (rd['mean'], rd['min'], rd['max'], rd['n'])) if rd else '-'))
    print()
    print('Closed loop: oref0-q6fix minus oref0, paired by patient and seed')
    print('| group | pairs | ' + ' | '.join(METRICS) + ' |')
    print('|---|--:|' + '--:|' * len(METRICS))
    for g in GROUPS + ['all']:
        ps = [x for x in pairs if g == 'all' or x['group'] == g]
        row = {}
        for m in METRICS:
            d = [x[m][1] - x[m][0] for x in ps]
            row[m] = summ(d)
            row[m]['pairs_changed'] = sum(abs(v) > 1e-9 for v in d)
        out['closed_loop'][g] = row
        def fmt(m):
            r = row[m]
            scale = 100.0 if m in ('tir_70_180', 'below_70', 'below_54', 'above_180') else 1.0
            return '%+.2f [%+.2f, %+.2f]' % (r['mean'] * scale, r['min'] * scale, r['max'] * scale)
        print('| %s | %d | ' % (g, len(ps)) + ' | '.join(fmt(m) for m in METRICS) + ' |')
    band = max(abs(x[m][1] - x[m][0]) * x['steps'] for x in pairs
               for m in ('tir_70_180', 'below_70', 'below_54', 'above_180'))
    out['closed_loop_max_band_shift_steps'] = round(band, 6)
    out['any_difference'] = anydiff
    print('any difference (IOB array, suggestion): %d steps in %d runs; suggestion: %d steps in %d runs; action: %d steps' % (
        anydiff['steps'], anydiff['runs'], anydiff['suggestion_steps'], anydiff['suggestion_runs'], anydiff['action_steps']))
    print('largest change in a glucose band: %.0f steps; pairs with any change: %d of %d' % (
        band, sum(any(abs(x[m][1] - x[m][0]) > 1e-9 for m in METRICS) for x in pairs), len(pairs)))
    print()
    return out


def main():
    out = {b: report(b) for b in BASALS}
    with open(os.path.join(ROOT, 'sim', 'out', 'q6-report.json'), 'w') as f:
        json.dump(out, f, indent=1)


if __name__ == '__main__':
    main()
