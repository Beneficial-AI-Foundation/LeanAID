"""Report of sim/run_fixed.py (docs/FIXED.md, "Virtual patients").

Reads the summaries in sim/out/runs-fixed/ (oref0 and aid-lean-fixed; faults none, f11, f12;
30 patients, 2 days, meal seed 1) and, for comparison, the oref0 runs of docs/SIM.md in
sim/out/runs/. Writes sim/out/fixed-report.json and prints Markdown tables.

Usage: .venv/bin/python sim/fixed_report.py
RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
"""
import glob
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'sim'))
import harness  # noqa: E402

FIXED = os.path.join(ROOT, 'sim', 'out', 'runs-fixed')
OLD = os.path.join(ROOT, 'sim', 'out', 'runs')
FAULTS = ['none', 'f11', 'f12']
METRICS = ['tir_70_180', 'below_70', 'below_54', 'above_180', 'mean_bg', 'insulin_per_day']


def load(d, controller, fault):
    out = {}
    for p in harness.PATIENTS:
        f = os.path.join(d, harness.run_id(p, controller, 2, 1, fault) + '.summary.json')
        if os.path.exists(f):
            with open(f) as h:
                out[p] = json.load(h)
    return out


def group(runs):
    if not runs:
        return None
    n = len(runs)
    g = {m: sum(r[m] for r in runs.values()) / n for m in METRICS}
    g['runs'] = n
    g['lowest_bg'] = min(r['min_bg'] for r in runs.values())
    g['runs_with_below_54'] = sum(1 for r in runs.values() if r['below_54'] > 0)
    g['violations'] = {}
    for r in runs.values():
        for k, v in r['violations'].items():
            g['violations'][k] = g['violations'].get(k, 0) + v
    g['decisions_compared'] = sum(r['decisions_compared'] for r in runs.values())
    g['decisions_identical'] = sum(r['decisions_identical'] for r in runs.values())
    g['iob_identical'] = sum(r['iob_identical'] for r in runs.values())
    g['controller_errors'] = sum(r['controller_errors'] for r in runs.values())
    return g


def main():
    rep = {'groups': {}, 'per_patient': {}, 'same_as_sim_md': {}}
    for fault in FAULTS:
        o = load(FIXED, 'oref0', fault)
        f = load(FIXED, 'aid-lean-fixed', fault)
        old = load(OLD, 'oref0', fault)
        rep['groups'][fault] = {'oref0': group(o), 'aid-lean-fixed': group(f), 'oref0 (SIM.md runs)': group(old)}
        # do the oref0 runs repeat those of SIM.md exactly?
        same = [p for p in o if p in old and all(o[p][m] == old[p][m] for m in METRICS)]
        rep['same_as_sim_md'][fault] = {'compared': len([p for p in o if p in old]), 'identical': len(same)}
        rep['per_patient'][fault] = {p: {'oref0': {m: o[p][m] for m in METRICS + ['min_bg']} if p in o else None,
                                         'aid-lean-fixed': {m: f[p][m] for m in METRICS + ['min_bg']} if p in f else None}
                                     for p in harness.PATIENTS}
        both = [p for p in harness.PATIENTS if p in o and p in f]
        rep['groups'][fault]['pairs'] = {
            'runs': len(both),
            'identical_bg_metrics': sum(1 for p in both if all(o[p][m] == f[p][m] for m in METRICS)),
            'more_time_below_54_fixed': sum(1 for p in both if f[p]['below_54'] > o[p]['below_54']),
            'less_time_below_54_fixed': sum(1 for p in both if f[p]['below_54'] < o[p]['below_54']),
            'more_time_below_70_fixed': sum(1 for p in both if f[p]['below_70'] > o[p]['below_70']),
            'less_time_below_70_fixed': sum(1 for p in both if f[p]['below_70'] < o[p]['below_70']),
        }
    with open(os.path.join(ROOT, 'sim', 'out', 'fixed-report.json'), 'w') as h:
        json.dump(rep, h, indent=1)
    print('| fault | controller | runs | TIR 70-180 | <70 | <54 | >180 | mean BG | U/day | lowest BG | runs with any <54 | decisions identical to oref0 | monitor violations |')
    print('|---|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|')
    for fault in FAULTS:
        for c in ('oref0 (SIM.md runs)', 'oref0', 'aid-lean-fixed'):
            g = rep['groups'][fault][c]
            if not g:
                continue
            dec = (f"{g['decisions_identical']} / {g['decisions_compared']}" if c == 'aid-lean-fixed' else '')
            print(f"| {fault} | {c} | {g['runs']} | {100 * g['tir_70_180']:.1f} % | {100 * g['below_70']:.2f} % | "
                  f"{100 * g['below_54']:.2f} % | {100 * g['above_180']:.1f} % | {g['mean_bg']:.1f} | "
                  f"{g['insulin_per_day']:.1f} | {g['lowest_bg']:.0f} | {g['runs_with_below_54']} | {dec} | "
                  f"{sum(g['violations'].values())} |")
    print()
    print(json.dumps({k: rep['groups'][k]['pairs'] for k in FAULTS}, indent=1))
    print(json.dumps(rep['same_as_sim_md'], indent=1))


if __name__ == '__main__':
    main()
