"""Report of the second F-12 fix on virtual patients (docs/FIXED.md, "Virtual patients").

Compares, with the F-12 fault (30 patients, 2 days, meal seed 1):
  oref0                     sim/out/runs-fixed/        (the runs of sim/run_fixed.py)
  aid-lean --fixed, F-12 v1 sim/out/runs-fixed/        (first version, commit 92c50dc)
  aid-lean --fixed, F-12 v2 sim/out/runs-fixed-f12v2/  (second version)
Writes sim/out/f12v2-report.json and prints Markdown tables: the group metrics, the monitor's
violations by rule, and per patient the time below 54 mg/dL against oref0. For every patient
whose time below 54 or R8 count is above oref0's, it lists the steps concerned (from the step
logs, gitignored).

Usage: .venv/bin/python sim/f12v2_report.py
RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
"""
import gzip
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'sim'))
import harness  # noqa: E402
from fixed_report import METRICS, group, load  # noqa: E402

V1 = os.path.join(ROOT, 'sim', 'out', 'runs-fixed')
V2 = os.path.join(ROOT, 'sim', 'out', 'runs-fixed-f12v2')
ARMS = [('oref0', V1, 'oref0'), ('F-12 v1', V1, 'aid-lean-fixed'), ('F-12 v2', V2, 'aid-lean-fixed')]


def steps_with(d, p, rule_or_low):
    """Steps of the v2 run of patient p with a violation of the given rule, or BG < 54."""
    f = os.path.join(d, harness.run_id(p, 'aid-lean-fixed', 2, 1, 'f12') + '.jsonl.gz')
    out = []
    if not os.path.exists(f):
        return out
    with gzip.open(f, 'rt') as h:
        for line in h:
            row = json.loads(line)
            if rule_or_low == 'below54':
                hit = isinstance(row.get('bg'), (int, float)) and row['bg'] < 54
            else:
                hit = rule_or_low in (row.get('violations') or [])
            if hit:
                s = row.get('aid_lean') or {}
                out.append({'k': row.get('k'), 'time': row.get('time'), 'bg': row.get('bg'), 'cgm': row.get('cgm'),
                            'rate': s.get('rate'), 'duration': s.get('duration'),
                            'reason_end': (s.get('reason') or '')[-140:]})
    return out


def main():
    runs = {name: load(d, c, 'f12') for name, d, c in ARMS}
    rep = {'groups': {name: group(r) for name, r in runs.items()}, 'per_patient': {}, 'worse_than_oref0': {}}
    o, v2 = runs['oref0'], runs['F-12 v2']
    for p in harness.PATIENTS:
        rep['per_patient'][p] = {name: ({m: r[p][m] for m in METRICS + ['min_bg']} | {'violations': r[p]['violations']}
                                       if p in r else None) for name, r in runs.items()}
        if p in o and p in v2:
            worse = {}
            if v2[p]['below_54'] > o[p]['below_54']:
                worse['below_54'] = {'oref0': o[p]['below_54'], 'v2': v2[p]['below_54'],
                                     'steps_below_54': steps_with(V2, p, 'below54')}
            if v2[p]['violations'].get('R8', 0) > o[p]['violations'].get('R8', 0):
                worse['R8'] = {'oref0': o[p]['violations'].get('R8', 0), 'v2': v2[p]['violations'].get('R8', 0),
                               'steps': steps_with(V2, p, 'R8')}
            if worse:
                rep['worse_than_oref0'][p] = worse
    both = [p for p in harness.PATIENTS if p in o and p in v2]
    rep['pairs'] = {
        'runs': len(both),
        'more_time_below_54_than_oref0': sum(1 for p in both if v2[p]['below_54'] > o[p]['below_54']),
        'less_time_below_54_than_oref0': sum(1 for p in both if v2[p]['below_54'] < o[p]['below_54']),
        'same_time_below_54_as_oref0': sum(1 for p in both if v2[p]['below_54'] == o[p]['below_54']),
    }
    with open(os.path.join(ROOT, 'sim', 'out', 'f12v2-report.json'), 'w') as h:
        json.dump(rep, h, indent=1)
    print('| controller | runs | TIR 70-180 | <70 | <54 | >180 | mean BG | U/day | lowest BG | runs with any <54 |')
    print('|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|')
    for name, g in rep['groups'].items():
        if g:
            print(f"| {name} | {g['runs']} | {100 * g['tir_70_180']:.1f} % | {100 * g['below_70']:.2f} % | "
                  f"{100 * g['below_54']:.2f} % | {100 * g['above_180']:.1f} % | {g['mean_bg']:.1f} | "
                  f"{g['insulin_per_day']:.1f} | {g['lowest_bg']:.0f} | {g['runs_with_below_54']} |")
    rules = sorted({k for g in rep['groups'].values() if g for k in g['violations']})
    print()
    print('| controller | ' + ' | '.join(rules) + ' | total |')
    print('|---|' + '--:|' * (len(rules) + 1))
    for name, g in rep['groups'].items():
        if g:
            print(f"| {name} | " + ' | '.join(str(g['violations'].get(r, 0)) for r in rules) +
                  f" | {sum(g['violations'].values())} |")
    print()
    print('| patient | <54 oref0 | <54 v1 | <54 v2 | v2 vs oref0 | R8 oref0 | R8 v2 |')
    print('|---|--:|--:|--:|---|--:|--:|')
    for p in harness.PATIENTS:
        pp = rep['per_patient'][p]
        if not all(pp.values()):
            continue
        a, b, c = pp['oref0']['below_54'], pp['F-12 v1']['below_54'], pp['F-12 v2']['below_54']
        cmp = 'more' if c > a else ('less' if c < a else 'same')
        print(f"| {p} | {100 * a:.2f} % | {100 * b:.2f} % | {100 * c:.2f} % | {cmp} | "
              f"{pp['oref0']['violations'].get('R8', 0)} | {pp['F-12 v2']['violations'].get('R8', 0)} |")
    print()
    print(json.dumps(rep['pairs']))
    print('patients worse than oref0 (time below 54 or R8):', list(rep['worse_than_oref0']))


if __name__ == '__main__':
    main()
