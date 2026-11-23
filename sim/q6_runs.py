"""Runs for FINDINGS F-24 (QUIRK Q6): oref0 against oref0 with the Q6 fix.

RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.

For each of the 30 patients, meal seeds 1-3, 2 days, basal schedules 'steps' and 'flat':
  - controller oref0 with --shadow-q6 (the fixed oref0 runs on every input, open loop),
  - controller oref0-q6fix (the fixed oref0 doses, closed loop).
Data goes to sim/out/runs/q6/ (not committed). Then run sim/q6_report.py.

Usage: .venv/bin/python -W ignore sim/q6_runs.py [--workers 6]
"""
import argparse
import fcntl
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'sim'))
import harness  # noqa: E402

OUT = os.path.join(ROOT, 'sim', 'out', 'runs', 'q6')
SEEDS = [1, 2, 3]
DAYS = 2
BASALS = ['steps', 'flat']


def jobs():
    for basal in BASALS:
        for seed in SEEDS:
            for p in harness.PATIENTS:
                yield [p, 'oref0', seed, basal, ['--shadow-q6']]
                yield [p, 'oref0-q6fix', seed, basal, []]


def one(job):
    p, ctrl, seed, basal, extra = job
    cmd = [sys.executable, '-W', 'ignore', os.path.join(ROOT, 'sim', 'harness.py'), '--patient', p,
           '--controller', ctrl, '--days', str(DAYS), '--seed', str(seed), '--basal', basal,
           '--out', OUT] + extra
    r = subprocess.run(cmd, capture_output=True, text=True)
    status = 'ok' if r.returncode == 0 else 'FAILED %d: %s' % (r.returncode, r.stderr[-400:])
    print(p, ctrl, seed, basal, status, flush=True)
    return r.returncode


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=6)
    a = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    # One driver at a time: two drivers would run the same jobs and collide on the
    # harness's temporary files.
    lock = open(os.path.join(OUT, '.lock'), 'w')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        sys.exit('another q6_runs.py is running on ' + OUT)
    with ThreadPoolExecutor(a.workers) as ex:
        codes = list(ex.map(one, list(jobs())))
    print('runs:', len(codes), 'failed:', sum(c != 0 for c in codes))
    sys.exit(1 if any(codes) else 0)


if __name__ == '__main__':
    main()
