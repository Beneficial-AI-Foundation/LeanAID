"""Virtual patients with the corrected version (docs/FIXED.md, "Virtual patients").

Runs items 1 and 3 of docs/SIM.md with two controllers, oref0 and `aid-lean serve --fixed`
(controller `aid-lean-fixed`): 30 patients, 2 days, meal seed 1, faults none, f11 and f12.
That is 180 runs; the oref0 runs repeat those of SIM.md and should give the same numbers.
Output: sim/out/runs-fixed/ (summaries and step logs, gitignored), progress in
sim/out/runs-fixed/progress.log. Resumable: a run whose summary exists is skipped.

The number of worker processes is read before each start from sim/out/runs-fixed/WORKERS
(default: SIM_WORKERS, else 3), so it can be raised while the runner is going.
Then `sim/fixed_report.py` writes sim/out/fixed-report.json.

Usage: .venv/bin/python sim/run_fixed.py
RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
"""
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'sim'))
import harness  # noqa: E402

OUT = os.path.join(ROOT, 'sim', 'out', 'runs-fixed')
PROGRESS = os.path.join(OUT, 'progress.log')
PY = os.path.join(ROOT, '.venv', 'bin', 'python')
FAULTS = ['none', 'f12', 'f11']


def log(msg):
    line = time.strftime('%Y-%m-%d %H:%M:%S') + '  ' + msg
    with open(PROGRESS, 'a') as f:
        f.write(line + '\n')
    print(line, flush=True)


def workers():
    try:
        with open(os.path.join(OUT, 'WORKERS')) as f:
            return max(1, int(f.read().strip()))
    except (OSError, ValueError):
        return int(os.environ.get('SIM_WORKERS', '3'))


def jobs():
    js = []
    for c in ('oref0', 'aid-lean-fixed'):          # the oref0 runs are fast; do them first
        for fault in FAULTS:
            for p in harness.PATIENTS:
                js.append((p, c, fault))
    return js


def main():
    os.makedirs(OUT, exist_ok=True)
    todo = [j for j in jobs() if not os.path.exists(
        os.path.join(OUT, harness.run_id(j[0], j[1], 2, 1, j[2]) + '.summary.json'))]
    log(f'start: {len(todo)} runs to do, aid-lean {harness.LEAN_BIN}')
    running = {}
    t0 = time.time()
    while todo or running:
        while todo and len(running) < workers():
            p, c, fault = todo.pop(0)
            cmd = [PY, os.path.join(ROOT, 'sim', 'harness.py'), '--patient', p, '--controller', c,
                   '--days', '2', '--seed', '1', '--fault', fault, '--out', OUT]
            running[subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)] = (p, c, fault, time.time())
        time.sleep(2)
        for proc in list(running):
            if proc.poll() is not None:
                p, c, fault, ts = running.pop(proc)
                err = proc.stderr.read().decode(errors='replace')[-500:] if proc.returncode else ''
                log(f'{"done" if proc.returncode == 0 else "FAILED"} {p} {c} {fault} in {time.time() - ts:.0f} s'
                    + (f': {err}' if err else ''))
    log(f'all done in {time.time() - t0:.0f} s')


if __name__ == '__main__':
    main()
