"""Overnight runner for the virtual-patient experiment (milestone M11).

Runs the job list in priority order with a pool of worker processes:
  1. main:     30 patients, 2 days, seed 1, oref0 / aid-lean / baseline
  2. faults:   dropout, compression, missed meal; 30 patients, 2 days, oref0 / aid-lean
  3. findings: F-11 (undated reading during dropout), F-12 (no max_basal); same
  4. long:     30 patients, 7 days, oref0 / aid-lean, meal seed 1, then 2, 3, ...
Stops starting new runs DEADLINE_H hours after it began. Runs of items 1-3 still in
progress then are finished; runs of item 4 still in progress are discarded (killed,
partial files deleted). Both are logged. Resumable: a run whose summary file exists is
skipped. Progress, with real times from `date`, goes to sim/out/progress.log.
Then it stops: the report (part 4) is not started.
"""
import os
import signal
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'sim'))
import harness  # noqa: E402

OUT = os.path.join(ROOT, 'sim', 'out')
RUNS = os.path.join(OUT, 'runs')
PROGRESS = os.path.join(OUT, 'progress.log')
PY = os.path.join(ROOT, '.venv', 'bin', 'python')
DEADLINE_H = float(os.environ.get('SIM_HOURS', '12'))
WORKERS = int(os.environ.get('SIM_WORKERS', '7'))
MAX_SEED = 50


def now():
    return subprocess.run(['date'], capture_output=True, text=True).stdout.strip()


def log(msg):
    line = f'{now()}  {msg}'
    with open(PROGRESS, 'a') as f:
        f.write(line + '\n')
    print(line, flush=True)


def jobs():
    """(item, patient, controller, days, seed, fault), in priority order."""
    P = harness.PATIENTS
    for p in P:
        for c in ('aid-lean', 'oref0', 'baseline'):
            yield (1, p, c, 2, 1, 'none')
    for f in ('dropout', 'compression', 'missedmeal'):
        for p in P:
            for c in ('aid-lean', 'oref0'):
                yield (2, p, c, 2, 1, f)
    for f in ('f11', 'f12'):
        for p in P:
            for c in ('aid-lean', 'oref0'):
                yield (3, p, c, 2, 1, f)
    for seed in range(1, MAX_SEED + 1):
        for p in P:
            for c in ('aid-lean', 'oref0'):
                yield (4, p, c, 7, seed, 'none')


def summary_path(j):
    _, p, c, d, s, f = j
    return os.path.join(RUNS, harness.run_id(p, c, d, s, f) + '.summary.json')


def start(j):
    _, p, c, d, s, f = j
    errf = open(os.path.join(OUT, 'logs', harness.run_id(p, c, d, s, f) + '.log'), 'w')
    return subprocess.Popen([PY, '-W', 'ignore', os.path.join(ROOT, 'sim', 'harness.py'), '--patient', p,
                             '--controller', c, '--days', str(d), '--seed', str(s), '--fault', f, '--out', RUNS],
                            stdout=errf, stderr=subprocess.STDOUT, start_new_session=True), errf


def main():
    os.makedirs(RUNS, exist_ok=True)
    os.makedirs(os.path.join(OUT, 'logs'), exist_ok=True)
    t0 = time.time()
    deadline = t0 + DEADLINE_H * 3600
    log(f'run_all started: {WORKERS} workers, stops starting runs after {DEADLINE_H} h '
        f'(pid {os.getpid()}, git {subprocess.run(["git", "-C", ROOT, "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()})')
    pending = iter(jobs())
    running = {}       # pid -> (job, proc, file, t_start)
    skipped = done = failed = 0
    exhausted = False
    stopping = False
    while True:
        # reap
        for pid, (j, pr, ef, ts) in list(running.items()):
            rc = pr.poll()
            if rc is None:
                continue
            ef.close()
            del running[pid]
            rid = harness.run_id(*j[1:3], j[3], j[4], j[5])
            if rc == 0 and os.path.exists(summary_path(j)):
                done += 1
                log(f'done    item {j[0]} {rid} ({time.time() - ts:.0f} s)')
            else:
                failed += 1
                log(f'FAILED  item {j[0]} {rid} exit {rc} (see sim/out/logs/{rid}.log)')
        if not stopping and time.time() >= deadline:
            stopping = True
            log(f'{DEADLINE_H} h reached: starting no new runs')
            for pid, (j, pr, ef, ts) in list(running.items()):
                rid = harness.run_id(*j[1:3], j[3], j[4], j[5])
                if j[0] == 4:
                    os.killpg(pr.pid, signal.SIGTERM)
                    pr.wait()
                    ef.close()
                    del running[pid]
                    for ext in ('.jsonl.gz.tmp', '.summary.json.tmp'):
                        try:
                            os.remove(os.path.join(RUNS, rid + ext))
                        except FileNotFoundError:
                            pass
                    log(f'discarded (item 4, in progress at the deadline) {rid}')
                else:
                    log(f'finishing (item {j[0]}, in progress at the deadline) {rid}')
        # start
        while not stopping and not exhausted and len(running) < WORKERS:
            try:
                j = next(pending)
            except StopIteration:
                exhausted = True
                break
            if os.path.exists(summary_path(j)):
                skipped += 1
                continue
            pr, ef = start(j)
            running[pr.pid] = (j, pr, ef, time.time())
            log(f'start   item {j[0]} {harness.run_id(*j[1:3], j[3], j[4], j[5])}')
        if not running and (stopping or exhausted):
            break
        time.sleep(2)
    log(f'run_all finished: {done} runs done, {failed} failed, {skipped} skipped (already done); '
        f'{(time.time() - t0) / 3600:.2f} h')


if __name__ == '__main__':
    main()
