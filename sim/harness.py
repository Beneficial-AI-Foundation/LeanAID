"""Closed-loop simulation of oref0 and aid-lean with the simglucose virtual patients.

RESEARCH ARTIFACT. NOT FOR DOSING INSULIN. simglucose is an open reimplementation of
the 2008 UVA/Padova simulator, not FDA-accepted evidence.

One run = one patient, one controller, one meal seed, one fault, N simulated days.
Every 5 simulated minutes the harness
  1. reads the CGM (simglucose's GuardianRT sensor model, 5-minute samples, seeded),
  2. enters announced carbs and gives the meal bolus (carbs / carb ratio) if a meal
     starts now,
  3. builds oref0's inputs from the history so far (glucose entries, pump history,
     carb entries, profile, current temp) and calls BOTH oref0 (Node) and aid-lean
     (Lean) on exactly that input,
  4. applies the decision of the run's controller (temp basal, microbolus if any) to
     the simulated pump, and checks it with the safety monitor (sim/monitor.py),
  5. simulates 5 minutes of the patient minute by minute with the insulin delivered.
The baseline controller is simglucose's basal-bolus controller (BBController policy).

Output: sim/out/runs/<run_id>.jsonl.gz (one row per step, with the full controller
input and output) and sim/out/runs/<run_id>.summary.json (written last; a run whose
summary exists is complete).

Usage: .venv/bin/python sim/harness.py --patient adult#001 --controller oref0 --days 1
"""
import argparse
import datetime as dt
import gzip
import json
import logging
import math
import os
import subprocess
import sys
import time

import numpy as np
import pandas as pd
import pkg_resources
from simglucose.patient.t1dpatient import T1DPatient, Action
from simglucose.sensor.cgm import CGMSensor
from simglucose.simulation.scenario_gen import RandomScenario

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import monitor  # noqa: E402

logging.getLogger('simglucose').setLevel(logging.WARNING)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, 'sim', 'out', 'runs')
LEAN_BIN = os.path.join(ROOT, '.lake', 'build', 'bin', 'aid-lean')
NODE_SERVER = os.path.join(ROOT, 'sim', 'oref0_server.js')

START = dt.datetime(2026, 1, 1, 0, 0, 0, tzinfo=dt.timezone.utc)   # simulated start (a past date: see SIM.md, Q10)
STEP = 5                                        # minutes per loop cycle
WINDOW_MIN = 12 * 60                            # history window given to the controller
TARGET = 110                                    # mg/dL, min_bg = max_bg
DIA = 5                                         # hours, oref0's minimum for the rapid-acting curve
SENSOR = 'GuardianRT'                           # simglucose sensor with a 5-minute sample time

PATIENTS = ([f'adolescent#{i:03d}' for i in range(1, 11)] + [f'adult#{i:03d}' for i in range(1, 11)]
            + [f'child#{i:03d}' for i in range(1, 11)])

# Fault windows (minutes after midnight, simulated UTC time)
DROPOUT = [(3 * 60, 3 * 60 + 45), (15 * 60, 15 * 60 + 45)]   # no new CGM readings, twice a day
COMPRESSION = [(2 * 60, 2 * 60 + 20)]                        # CGM reads 40 mg/dL low, at night
FAULTS = ['none', 'dropout', 'compression', 'missedmeal', 'f11', 'f12']


def iso(t):
    return t.strftime('%Y-%m-%dT%H:%M:%S.000Z')


def round_to(x, inc):
    return round(round(x / inc) * inc, 10)


# ---------------------------------------------------------------- patient profile
def patient_params(name):
    p = pd.read_csv(pkg_resources.resource_filename('simglucose', 'params/vpatient_params.csv'))
    q = pd.read_csv(pkg_resources.resource_filename('simglucose', 'params/Quest.csv'))
    pp = p[p.Name == name].iloc[0]
    qq = q[q.Name == name].iloc[0]
    return dict(BW=float(pp.BW), u2ss=float(pp.u2ss), CR=float(qq.CR), CF=float(qq.CF))


def profile_inputs(name):
    """Inputs of oref0's lib/profile for a patient (see docs/SIM.md, "Profiles").
    basal: u2ss * BW / 6000 U/min (simglucose's steady-state basal, the formula of its
    BBController) * 60 = U/h, rounded to the 0.05 U/h pump increment;
    carb ratio: Quest.csv CR (g/U); ISF: Quest.csv CF (mg/dL/U) rounded to an integer;
    max_basal = 3 x basal; max_iob = 3 x basal + 60 g / CR, rounded to 0.1 U;
    DIA 5 h, target 110 mg/dL; everything else oref0's defaults."""
    pp = patient_params(name)
    basal = max(0.05, round_to(pp['u2ss'] * pp['BW'] / 6000 * 60, 0.05))
    cr = pp['CR']
    isf = float(round(pp['CF']))
    max_basal = round_to(3 * basal, 0.05)
    max_iob = round_to(3 * basal + 60.0 / cr, 0.1)
    return {
        'settings': {'insulin_action_curve': DIA, 'maxBasal': max_basal},
        'basals': [{'i': 0, 'start': '00:00:00', 'minutes': 0, 'rate': basal}],
        'targets': {'units': 'mg/dL', 'user_preferred_units': 'mg/dL',
                    'targets': [{'i': 0, 'start': '00:00:00', 'offset': 0, 'low': TARGET, 'high': TARGET,
                                 'min_bg': TARGET, 'max_bg': TARGET}]},
        'isf': {'units': 'mg/dL', 'user_preferred_units': 'mg/dL',
                'sensitivities': [{'i': 0, 'start': '00:00:00', 'sensitivity': isf, 'offset': 0, 'x': 0,
                                   'endOffset': 1440}]},
        'carbratio': {'units': 'grams', 'schedule': [{'i': 0, 'start': '00:00:00', 'offset': 0, 'ratio': cr}]},
        'temptargets': [],
        'max_iob': max_iob,
    }


# ---------------------------------------------------------------- meals
def meal_plan(patient_index, meal_seed, days):
    """Seeded random meals (simglucose's RandomScenario: breakfast, lunch, dinner and
    up to three snacks a day). Returns [(minute since start, grams)], meal times
    rounded to the 5-minute loop grid."""
    sc = RandomScenario(start_time=START, seed=1000 * meal_seed + patient_index)
    meals = []
    for d in range(days):
        s = sc.create_scenario() if d > 0 else sc.scenario
        for tm, g in zip(s['meal']['time'], s['meal']['amount']):
            if g > 0:
                meals.append((d * 1440 + int(round(float(tm) / STEP)) * STEP, float(g)))
    meals.sort()
    return meals


# ---------------------------------------------------------------- controller processes
class LineProc:
    def __init__(self, args, env=None):
        self.p = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL, text=True, bufsize=1, env=env)

    def call(self, obj):
        self.p.stdin.write(json.dumps(obj, separators=(',', ':')) + '\n')
        self.p.stdin.flush()
        line = self.p.stdout.readline()
        if not line:
            raise RuntimeError('controller process ended: ' + ' '.join(self.p.args))
        return json.loads(line)

    def close(self):
        try:
            self.p.stdin.close()
            self.p.wait(timeout=10)
        except Exception:
            self.p.kill()


def env_utc():
    e = dict(os.environ)
    e['TZ'] = 'UTC'
    return e


# ---------------------------------------------------------------- one run
def run_id(patient, controller, days, meal_seed, fault):
    return f'{patient.replace("#", "")}_{controller}_{days}d_seed{meal_seed}_{fault}'


def in_windows(minute, windows):
    m = minute % 1440
    return any(a <= m < b for a, b in windows)


def run(patient, controller, days=2, meal_seed=1, fault='none', out_dir=OUT, log_inputs=True, shadow=False):
    """shadow: also run aid-lean on every input of an oref0 run (always done in aid-lean runs,
    where oref0 runs on every input of aid-lean)."""
    assert controller in ('oref0', 'aid-lean', 'baseline') and fault in FAULTS
    os.makedirs(out_dir, exist_ok=True)
    rid = run_id(patient, controller, days, meal_seed, fault)
    rows_path = os.path.join(out_dir, rid + '.jsonl.gz')
    summary_path = os.path.join(out_dir, rid + '.summary.json')
    t_wall0 = time.time()
    pidx = PATIENTS.index(patient) + 1

    pat = T1DPatient.withName(patient)
    sensor = CGMSensor.withName(SENSOR, seed=10000 * meal_seed + pidx)
    meals = meal_plan(pidx, meal_seed, days)
    missed = set()
    if fault == 'missedmeal':                          # the largest meal of each day is not announced
        for d in range(days):
            day = [m for m in meals if d * 1440 <= m[0] < (d + 1) * 1440]
            if day:
                missed.add(max(day, key=lambda m: (m[1], -m[0])))
    meal_at = {}
    for m in meals:
        meal_at.setdefault(m[0], []).append(m)

    pinp = profile_inputs(patient)
    pp = patient_params(patient)
    node = lean = None
    if controller != 'baseline':
        node = LineProc(['node', NODE_SERVER], env=env_utc())
        if controller == 'aid-lean' or shadow:
            lean = LineProc([LEAN_BIN, 'serve'], env=env_utc())
        profile = node.call({'cmd': 'profile', 'inputs': pinp})['profile']
        configured_max_basal = profile['max_basal']
        if fault == 'f12':
            del profile['max_basal']                   # FINDINGS F-12: the profile has no max_basal
    else:
        profile = None
        configured_max_basal = pinp['settings']['maxBasal']
    sched_basal = pinp['basals'][0]['rate']            # U/h, what the pump runs without a temp

    glucose = []        # newest first, oref0 entry format
    pumphist = []       # newest first, Medtronic-style records (as in oref0's tests)
    carbhist = []       # newest first, Nightscout-style carb entries
    temp = None         # (rate U/h, start minute, duration min)
    last_real = None    # (minute, sgv) of the last CGM reading actually received
    stats = dict(steps=0, compared=0, identical=0, iob_identical=0, first_diff=None, violations={},
                 controller_errors=0, bolus_U=0.0, basal_U=0.0, smb_U=0.0)
    bgs = []
    rows = gzip.open(rows_path + '.tmp', 'wt') if log_inputs else None
    n_steps = days * 1440 // STEP

    for k in range(n_steps):
        minute = k * STEP
        now = START + dt.timedelta(minutes=minute)
        bg_true = float(pat.observation.Gsub)
        cgm_raw = float(sensor.measure(pat))               # patient.t % 5 == 0 here
        bgs.append(bg_true)
        row = {'k': k, 'time': iso(now), 'bg': bg_true, 'cgm': cgm_raw}

        # ---- CGM reading as the controller receives it (faults applied)
        sgv = int(round(cgm_raw))
        if fault == 'compression' and in_windows(minute, COMPRESSION):
            sgv = max(39, sgv - 40)
        dropped = fault in ('dropout', 'f11') and in_windows(minute, DROPOUT)
        if not dropped:
            glucose.insert(0, {'date': int(now.timestamp() * 1000), 'dateString': iso(now), 'sgv': sgv,
                               'glucose': sgv, 'type': 'sgv', 'device': 'simglucose'})
            last_real = (minute, sgv)
        row['sgv'] = None if dropped else sgv

        # ---- meals starting now: the patient eats; announced meals get carbs + bolus
        cho_now = 0.0
        bolus_now = 0.0
        for m in meal_at.get(minute, []):
            cho_now += m[1]
            if m in missed:
                row.setdefault('missed_meal_g', 0.0)
                row['missed_meal_g'] += m[1]
                continue
            if controller == 'baseline':
                continue
            b = math.floor(m[1] / pinp['carbratio']['schedule'][0]['ratio'] / 0.05 + 1e-9) * 0.05
            b = round(b, 2)
            carbhist.insert(0, {'carbs': m[1], 'created_at': iso(now), 'enteredBy': 'sim'})
            if b > 0:
                pumphist.insert(0, {'_type': 'Bolus', 'amount': b, 'programmed': b, 'unabsorbed': 0,
                                    'duration': 0, 'timestamp': iso(now)})
                bolus_now += b
        row['meal_g'] = cho_now or None
        row['meal_bolus'] = bolus_now or None

        # ---- controller
        smb_now = 0.0
        if controller == 'baseline':
            # simglucose BBController._bb_policy: basal u2ss*BW/6000 U/min; at a meal,
            # bolus = carbs/CR + (CGM > 150) * (CGM - 140)/CF (its default target 140)
            basal_rate = pp['u2ss'] * pp['BW'] / 6000 * 60
            if cho_now > 0:
                b = cho_now / pp['CR'] + (cgm_raw > 150) * (cgm_raw - 140) / pp['CF']
                bolus_now = max(0.0, b)
            temp = None
            sched_eff = basal_rate
        else:
            cutoff = now - dt.timedelta(minutes=WINDOW_MIN)
            ct_rate, ct_dur = 0, 0
            if temp is not None and minute < temp[1] + temp[2]:
                ct_rate, ct_dur = temp[0], temp[1] + temp[2] - minute
            currenttemp = {'duration': ct_dur, 'rate': ct_rate, 'temp': 'absolute'}
            glu = [g for g in glucose if g['date'] > cutoff.timestamp() * 1000]
            if fault == 'f11' and dropped and last_real is not None:
                # FINDINGS F-11: the last reading keeps arriving, without a timestamp
                glu = [{'sgv': last_real[1], 'glucose': last_real[1], 'type': 'sgv', 'device': 'simglucose'}] + glu
            inp = {
                'pumphistory': [r for r in pumphist if r['timestamp'] > iso(cutoff)],
                'carbhistory': [c for c in carbhist if c['created_at'] > iso(cutoff)],
                'glucose': glu, 'profile': profile, 'clock': iso(now), 'currenttemp': currenttemp,
                'autosens': {'ratio': 1}, 'microBolusAllowed': False, 'currentTime': int(now.timestamp() * 1000),
            }
            js = node.call(dict(inp, cmd='step'))
            if 'exception' in js:
                raise RuntimeError('oref0 exception at step %d: %s' % (k, js['exception']))
            lin = dict(inp, meal=js['meal'])
            del lin['carbhistory']
            ln = None
            same = iob_same = None
            if controller == 'aid-lean' or shadow:
                # aid-lean on the same input (meal data from oref0's lib/meal, see SIM.md)
                ln = lean.call(lin)
                js_s = json.dumps(js['suggestion'], separators=(',', ':'))
                ln_s = json.dumps(ln['suggestion'], separators=(',', ':'))
                same = js_s == ln_s
                iob_same = monitor.iob_equal(js['iob'], ln['iob'])
                stats['identical'] += same
                stats['iob_identical'] += iob_same
                stats['compared'] += 1
                if (not same or not iob_same) and stats['first_diff'] is None:
                    stats['first_diff'] = {'k': k, 'time': iso(now), 'input': lin, 'oref0': js['suggestion'],
                                           'aid_lean': ln['suggestion'], 'iob_same': iob_same,
                                           'oref0_iob0': js['iob'][0] if js['iob'] else None,
                                           'aid_lean_iob0': ln['iob'][0] if ln['iob'] else None}
            arm = js if controller == 'oref0' else ln
            rT = arm['suggestion']
            iob0 = arm['iob'][0] if arm['iob'] else {}
            # ---- safety monitor on the actual input and output of this arm
            newest_minute = last_real[0] if last_real else None
            viol = monitor.check(rT, profile=profile, configured_max_basal=configured_max_basal,
                                 glucose=glu, true_age_min=(minute - newest_minute) if newest_minute is not None else None,
                                 currenttemp=currenttemp, iob=iob0, gs=js['glucose_status'])
            for v in viol:
                stats['violations'][v] = stats['violations'].get(v, 0) + 1
            if 'error' in rT:
                stats['controller_errors'] += 1
            # ---- apply: as oref0's pump loop does
            if isinstance(rT.get('rate'), (int, float)) and isinstance(rT.get('duration'), (int, float)):
                r, d = float(rT['rate']), float(rT['duration'])
                if d <= 0:
                    temp = None
                    pumphist.insert(0, {'_type': 'TempBasalDuration', 'duration (min)': 0, 'timestamp': iso(now)})
                    pumphist.insert(0, {'_type': 'TempBasal', 'temp': 'absolute', 'rate': 0, 'timestamp': iso(now)})
                else:
                    temp = (r, minute, int(d))
                    pumphist.insert(0, {'_type': 'TempBasalDuration', 'duration (min)': int(d), 'timestamp': iso(now)})
                    pumphist.insert(0, {'_type': 'TempBasal', 'temp': 'absolute', 'rate': r, 'timestamp': iso(now)})
            u = rT.get('units')
            if isinstance(u, (int, float)) and u > 0:
                smb_now = float(u)
                pumphist.insert(0, {'_type': 'Bolus', 'amount': smb_now, 'programmed': smb_now, 'unabsorbed': 0,
                                    'duration': 0, 'timestamp': iso(now)})
            sched_eff = sched_basal
            row.update({'input': lin if log_inputs else None, 'oref0': js['suggestion'], 'aid_lean': ln['suggestion'] if ln else None,
                        'same': same, 'iob_same': iob_same, 'iob0': iob0, 'violations': viol})

        # ---- deliver and simulate 5 minutes
        delivered_basal = 0.0
        for j in range(STEP):
            mm = minute + j
            rate = temp[0] if (temp is not None and temp[1] <= mm < temp[1] + temp[2]) else sched_eff
            ins = rate / 60.0
            delivered_basal += ins
            if j == 0:
                ins += bolus_now + smb_now
            pat.step(Action(CHO=cho_now if j == 0 else 0.0, insulin=ins))
        stats['basal_U'] += delivered_basal
        stats['bolus_U'] += bolus_now
        stats['smb_U'] += smb_now
        row['delivered'] = {'basal': delivered_basal, 'bolus': bolus_now, 'smb': smb_now}
        stats['steps'] += 1
        if rows:
            rows.write(json.dumps(row, separators=(',', ':')) + '\n')

    if node:
        node.close()
    if lean:
        lean.close()
    if rows:
        rows.close()
        os.replace(rows_path + '.tmp', rows_path)
    b = np.array(bgs)
    summary = {
        'run_id': rid, 'patient': patient, 'controller': controller, 'days': days, 'meal_seed': meal_seed,
        'fault': fault, 'steps': stats['steps'],
        'meals': meals, 'missed_meals': sorted(missed),
        'tir_70_180': float(np.mean((b >= 70) & (b <= 180))), 'below_70': float(np.mean(b < 70)),
        'below_54': float(np.mean(b < 54)), 'above_180': float(np.mean(b > 180)),
        'above_250': float(np.mean(b > 250)), 'mean_bg': float(b.mean()), 'cv': float(b.std() / b.mean()),
        'min_bg': float(b.min()), 'max_bg': float(b.max()),
        'insulin_per_day': (stats['basal_U'] + stats['bolus_U'] + stats['smb_U']) / days,
        'basal_U': stats['basal_U'], 'bolus_U': stats['bolus_U'], 'smb_U': stats['smb_U'],
        'decisions_compared': stats['compared'],
        'decisions_identical': stats['identical'], 'iob_identical': stats['iob_identical'],
        'first_difference': stats['first_diff'],
        'violations': stats['violations'], 'controller_errors': stats['controller_errors'],
        'profile': profile, 'configured_max_basal': configured_max_basal,
        'wall_seconds': time.time() - t_wall0,
    }
    with open(summary_path + '.tmp', 'w') as f:
        json.dump(summary, f, indent=1)
    os.replace(summary_path + '.tmp', summary_path)
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--patient', required=True)
    ap.add_argument('--controller', required=True, choices=['oref0', 'aid-lean', 'baseline'])
    ap.add_argument('--days', type=int, default=2)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--fault', default='none', choices=FAULTS)
    ap.add_argument('--out', default=OUT)
    ap.add_argument('--force', action='store_true')
    ap.add_argument('--shadow', action='store_true', help='oref0 runs: also run aid-lean on every input')
    a = ap.parse_args()
    sp = os.path.join(a.out, run_id(a.patient, a.controller, a.days, a.seed, a.fault) + '.summary.json')
    if os.path.exists(sp) and not a.force:
        print('exists, skipped:', sp)
        return
    s = run(a.patient, a.controller, a.days, a.seed, a.fault, a.out, shadow=a.shadow)
    keys = ['run_id', 'tir_70_180', 'below_70', 'below_54', 'mean_bg', 'insulin_per_day', 'decisions_compared', 'decisions_identical',
            'iob_identical', 'steps', 'violations', 'controller_errors', 'wall_seconds']
    print(json.dumps({k: s[k] for k in keys}))


if __name__ == '__main__':
    main()
