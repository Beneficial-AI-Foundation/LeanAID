"""Part 4: aggregate the overnight runs into sim/out/report.json, sim/out/report.md and
plots in sim/out/plots/. Reads only sim/out/runs/ (summaries, and the step files for the
trace comparison and the violation details). docs/SIM.md is written from its output.

    .venv/bin/python sim/report.py
"""
import glob
import gzip
import json
import os
from collections import defaultdict

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RUNS = os.path.join(ROOT, 'sim', 'out', 'runs')
OUT = os.path.join(ROOT, 'sim', 'out')
PLOTS = os.path.join(OUT, 'plots')
GROUPS = ('adolescent', 'adult', 'child')
CTRLS = ('oref0', 'aid-lean', 'baseline')
METRICS = ('tir_70_180', 'below_70', 'below_54', 'above_180', 'above_250', 'mean_bg', 'cv', 'insulin_per_day')


def load_summaries():
    S = []
    for f in sorted(glob.glob(os.path.join(RUNS, '*.summary.json'))):
        with open(f) as fh:
            s = json.load(fh)
        s['group'] = s['patient'].split('#')[0]
        S.append(s)
    return S


def steps(run_id):
    with gzip.open(os.path.join(RUNS, run_id + '.jsonl.gz'), 'rt') as fh:
        return [json.loads(l) for l in fh]


def experiment(s):
    return (s['days'], s['meal_seed'], s['fault'])


def exp_name(e):
    d, seed, f = e
    return f'{d}d seed {seed} {f}'


def group_table(S):
    """experiment -> controller -> group|'all' -> {n, metric: mean over runs, min/max of TIR, worst min_bg}."""
    T = defaultdict(lambda: defaultdict(dict))
    by = defaultdict(list)
    for s in S:
        by[(experiment(s), s['controller'], s['group'])].append(s)
        by[(experiment(s), s['controller'], 'all')].append(s)
    for (e, c, g), L in by.items():
        row = {'n': len(L)}
        for m in METRICS:
            row[m] = float(np.mean([x[m] for x in L]))
        row['tir_min'] = min(x['tir_70_180'] for x in L)
        row['min_bg'] = min(x['min_bg'] for x in L)
        row['runs_below54'] = sum(1 for x in L if x['below_54'] > 0)
        row['violations'] = sum(sum(x['violations'].values()) for x in L)
        T[exp_name(e)][c][g] = row
    return T


def agreement(S):
    A = {'runs': 0, 'compared': 0, 'identical': 0, 'iob_identical': 0, 'differences': []}
    for s in S:
        if s['controller'] != 'aid-lean':
            continue
        A['runs'] += 1
        A['compared'] += s['decisions_compared']
        A['identical'] += s['decisions_identical']
        A['iob_identical'] += s['iob_identical']
        if s['first_difference'] is not None or s['decisions_identical'] != s['decisions_compared'] \
                or s['iob_identical'] != s['decisions_compared']:
            A['differences'].append({'run': s['run_id'], 'first': s['first_difference']})
        if s['controller_errors']:
            A.setdefault('errors', []).append((s['run_id'], s['controller_errors']))
    return A


def arm_traces(S):
    """Compare the oref0 arm and the aid-lean arm of the same patient/experiment step by step:
    true BG, CGM, delivered insulin and the applied decision."""
    idx = {(s['patient'], experiment(s), s['controller']): s for s in S}
    res = {'pairs': 0, 'identical': 0, 'steps': 0, 'diffs': []}
    for (p, e, c), s in sorted(idx.items()):
        if c != 'oref0' or (p, e, 'aid-lean') not in idx:
            continue
        a = steps(s['run_id'])
        b = steps(idx[(p, e, 'aid-lean')]['run_id'])
        res['pairs'] += 1
        res['steps'] += len(a)
        first = None
        if len(a) != len(b):
            first = ('length', len(a), len(b))
        else:
            for x, y in zip(a, b):
                if (x['bg'], x['cgm'], x['sgv'], x['delivered']) != (y['bg'], y['cgm'], y['sgv'], y['delivered']) \
                        or json.dumps(x['oref0'], sort_keys=True) != json.dumps(y['aid_lean'], sort_keys=True):
                    first = ('step', x['k'], x['time'])
                    break
        if first is None:
            res['identical'] += 1
        else:
            res['diffs'].append({'patient': p, 'experiment': exp_name(e), 'first': first})
    return res


def violations(S):
    """Every violation: per run the counts by rule, and per rule the steps (first 3 shown)."""
    V = []
    for s in S:
        if not s['violations']:
            continue
        rows = [r for r in steps(s['run_id']) if r['violations']]
        dec_key = 'aid_lean' if s['controller'] == 'aid-lean' else 'oref0'
        ex = []
        for r in rows[:3]:
            d = r.get(dec_key) or {}
            ex.append({'k': r['k'], 'time': r['time'], 'bg': round(r['bg'], 1), 'sgv': r['sgv'],
                       'rate': d.get('rate'), 'duration': d.get('duration'), 'rules': r['violations']})
        V.append({'run': s['run_id'], 'controller': s['controller'], 'fault': s['fault'], 'days': s['days'],
                  'counts': s['violations'], 'steps_with_violation': len(rows), 'examples': ex,
                  'configured_max_basal': s['configured_max_basal'], 'below_54': s['below_54'], 'min_bg': s['min_bg']})
    return V


def fault_effects(S):
    """Per fault and controller: mean change against the no-fault run of the same patient."""
    idx = {(s['patient'], experiment(s), s['controller']): s for s in S}
    E = defaultdict(lambda: defaultdict(list))
    for (p, e, c), s in idx.items():
        d, seed, f = e
        if f == 'none' or (p, (d, seed, 'none'), c) not in idx:
            continue
        b = idx[(p, (d, seed, 'none'), c)]
        for m in ('tir_70_180', 'below_70', 'below_54', 'mean_bg', 'insulin_per_day', 'min_bg', 'max_bg'):
            E[(f, c)][m].append(s[m] - b[m])
        E[(f, c)]['worse_below70'].append(1 if s['below_70'] > b['below_70'] + 1e-12 else 0)
    out = {}
    for (f, c), D in E.items():
        out[f'{f}/{c}'] = {m: (float(np.sum(v)) if m == 'worse_below70' else float(np.mean(v))) for m, v in D.items()}
        out[f'{f}/{c}']['n'] = len(D['tir_70_180'])
        out[f'{f}/{c}']['min_delta_min_bg'] = float(np.min(D['min_bg']))
    return out


# ---------------------------------------------------------------- plots

def plot_tir(S):
    main = [s for s in S if experiment(s) == (2, 1, 'none')]
    pats = sorted({s['patient'] for s in main}, key=lambda p: (p.split('#')[0], p))
    fig, ax = plt.subplots(figsize=(13, 4.5))
    w = 0.27
    cols = {'oref0': '#3b6fb6', 'aid-lean': '#e08a2c', 'baseline': '#8a8a8a'}
    for i, c in enumerate(CTRLS):
        d = {s['patient']: s for s in main if s['controller'] == c}
        x = np.arange(len(pats)) + (i - 1) * w
        ax.bar(x, [100 * d[p]['tir_70_180'] for p in pats], w, label=c, color=cols[c])
        ax.bar(x, [-100 * d[p]['below_70'] for p in pats], w, color=cols[c], alpha=0.5, hatch='//')
    ax.axhline(0, color='k', lw=0.6)
    ax.set_xticks(range(len(pats)))
    ax.set_xticklabels([p.replace('adolescent', 'adol') for p in pats], rotation=70, fontsize=8)
    ax.set_ylabel('% time in 70–180 (up) / below 70 (down, hatched)')
    ax.set_title('Main runs (2 days, meal seed 1): per patient, true BG. Simulation only, not for dosing.')
    ax.legend(loc='lower left', ncol=3)
    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS, 'tir_per_patient.png'), dpi=110)
    plt.close(fig)


def plot_bands(S):
    main = [s for s in S if experiment(s) == (2, 1, 'none')]
    fig, axes = plt.subplots(1, 3, figsize=(15, 4), sharey=True)
    for ax, c in zip(axes, CTRLS):
        B = np.array([[r['bg'] for r in steps(s['run_id'])] for s in main if s['controller'] == c])
        t = np.arange(B.shape[1]) * 5 / 60
        for lo, hi, a in ((5, 95, 0.2), (25, 75, 0.4)):
            ax.fill_between(t, np.percentile(B, lo, axis=0), np.percentile(B, hi, axis=0), color='#3b6fb6', alpha=a, lw=0)
        ax.plot(t, np.median(B, axis=0), color='#1d3a66', lw=1.2)
        ax.axhspan(70, 180, color='green', alpha=0.06)
        ax.axhline(54, color='red', lw=0.6, ls='--')
        ax.set_title(f'{c}: 30 patients (median, 25–75, 5–95 %)')
        ax.set_xlabel('hours')
    axes[0].set_ylabel('true BG (mg/dL)')
    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS, 'bg_bands_main.png'), dpi=110)
    plt.close(fig)


def plot_run_pair(S, patient, faults, fname, title, ctrl='oref0'):
    idx = {(s['patient'], experiment(s), s['controller']): s for s in S}
    fig, (a1, a2) = plt.subplots(2, 1, figsize=(13, 6), sharex=True, gridspec_kw={'height_ratios': [2, 1]})
    for f, col in zip(faults, ('#1d3a66', '#d1495b', '#2a9d8f')):
        s = idx.get((patient, (2, 1, f), ctrl))
        if s is None:
            continue
        R = steps(s['run_id'])
        t = np.array([r['k'] for r in R]) * 5 / 60
        a1.plot(t, [r['bg'] for r in R], color=col, lw=1.1, label=f'{f}: true BG')
        if f != 'none':
            a1.plot(t, [r['sgv'] for r in R], color=col, lw=0.6, ls=':', label=f'{f}: CGM given to controller')
        a2.plot(t, [12 * (r['delivered']['basal'] + r['delivered']['smb']) for r in R], color=col, lw=0.9, label=f)
        for k, g in s['meals']:
            a1.axvline(k / 60, color='#bbbbbb', lw=0.5)
    a1.axhspan(70, 180, color='green', alpha=0.06)
    a1.axhline(54, color='red', lw=0.6, ls='--')
    a1.set_ylabel('mg/dL')
    a1.legend(fontsize=7, ncol=3)
    a1.set_title(title)
    a2.set_ylabel('basal delivered (U/h)')
    a2.set_xlabel('hours (grey lines: meal starts)')
    a2.legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS, fname), dpi=110)
    plt.close(fig)


def plot_controllers(S, patient, fname):
    idx = {(s['patient'], experiment(s), s['controller']): s for s in S}
    fig, ax = plt.subplots(figsize=(13, 4))
    for c, col in zip(CTRLS, ('#3b6fb6', '#e08a2c', '#8a8a8a')):
        s = idx[(patient, (2, 1, 'none'), c)]
        R = steps(s['run_id'])
        ax.plot(np.array([r['k'] for r in R]) * 5 / 60, [r['bg'] for r in R], lw=1.6 if c == 'aid-lean' else 1.0,
                ls='--' if c == 'aid-lean' else '-', color=col, label=c)
    ax.axhspan(70, 180, color='green', alpha=0.06)
    ax.axhline(54, color='red', lw=0.6, ls='--')
    ax.set_title(f'{patient}, main run: true BG (oref0 and aid-lean lines coincide)')
    ax.set_xlabel('hours')
    ax.set_ylabel('mg/dL')
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(PLOTS, fname), dpi=110)
    plt.close(fig)


def main():
    os.makedirs(PLOTS, exist_ok=True)
    S = load_summaries()
    R = {
        'runs': len(S),
        'by_experiment': {exp_name(e): n for e, n in sorted(
            {experiment(s): sum(1 for x in S if experiment(x) == experiment(s)) for s in S}.items())},
        'groups': group_table(S),
        'agreement': agreement(S),
        'arm_traces': arm_traces(S),
        'violations': violations(S),
        'fault_effects': fault_effects(S),
        'per_run': [{k: s[k] for k in ('run_id', 'group', 'controller', 'days', 'meal_seed', 'fault', *METRICS,
                                       'min_bg', 'max_bg', 'violations', 'wall_seconds')} for s in S],
    }
    with open(os.path.join(OUT, 'report.json'), 'w') as fh:
        json.dump(R, fh, indent=1, default=str)
    plot_tir(S)
    plot_bands(S)
    worst = min((s for s in S if experiment(s) == (2, 1, 'none') and s['controller'] == 'oref0'),
                key=lambda s: s['min_bg'])['patient']
    plot_controllers(S, worst, 'controllers_' + worst.replace('#', '') + '.png')
    R['worst_patient_main_oref0'] = worst
    f12 = max((s for s in S if s['fault'] == 'f12' and s['controller'] == 'oref0'),
              key=lambda s: s['below_70'])['patient']
    plot_run_pair(S, f12, ('none', 'f12'), 'f12_' + f12.replace('#', '') + '.png',
                  f'F-12 (profile without max_basal), {f12}, oref0')
    f11 = max((s for s in S if s['fault'] == 'f11' and s['controller'] == 'oref0'),
              key=lambda s: abs(s['mean_bg'] - next(x for x in S if x['patient'] == s['patient'] and x['controller'] == 'oref0'
                                                    and experiment(x) == (2, 1, 'dropout'))['mean_bg']))['patient']
    plot_run_pair(S, f11, ('dropout', 'f11'), 'f11_' + f11.replace('#', '') + '.png',
                  f'F-11 (undated reading during dropout) against plain dropout, {f11}, oref0')
    def most_changed(fault, metric, sign):
        """The patient whose oref0 run changed `metric` most (in direction `sign`) against the no-fault run."""
        base = {s['patient']: s for s in S if experiment(s) == (2, 1, 'none') and s['controller'] == 'oref0'}
        return max((s for s in S if experiment(s) == (2, 1, fault) and s['controller'] == 'oref0'),
                   key=lambda s: sign * (s[metric] - base[s['patient']][metric]))['patient']

    mm = most_changed('missedmeal', 'tir_70_180', -1)
    plot_run_pair(S, mm, ('none', 'missedmeal'), 'missedmeal_' + mm.replace('#', '') + '.png',
                  f'Missed meal announcement, {mm}, oref0')
    cp = most_changed('compression', 'min_bg', -1)
    plot_run_pair(S, cp, ('none', 'compression'), 'compression_' + cp.replace('#', '') + '.png',
                  f'Compression low 02:00–02:20, {cp}, oref0')
    R['plot_patients'] = {'f12': f12, 'f11': f11, 'missedmeal': mm, 'compression': cp, 'controllers': worst}
    with open(os.path.join(OUT, 'report.json'), 'w') as fh:
        json.dump(R, fh, indent=1, default=str)
    print(json.dumps({k: R[k] for k in ('runs', 'by_experiment', 'agreement', 'plot_patients')}, indent=1, default=str))
    print('arm traces:', {k: v for k, v in R['arm_traces'].items() if k != 'diffs'}, R['arm_traces']['diffs'][:5])


if __name__ == '__main__':
    main()
