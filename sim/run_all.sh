#!/bin/bash
# Overnight virtual-patient runs (prompts/overnight-sim.md, part 3). Start with:
#   nohup caffeinate -i sim/run_all.sh > sim/out/run_all.log 2>&1 &
# Stops starting new runs after 12 hours (SIM_HOURS), resumable, progress in
# sim/out/progress.log. See sim/run_all.py. RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
set -u
cd "$(dirname "$0")/.."
mkdir -p sim/out
export TZ=UTC
echo "$(date)  run_all.sh started in $(pwd)"
test -x .lake/build/bin/aid-lean || { echo "$(date)  aid-lean not built (lake build aid-lean)"; exit 1; }
test -x .venv/bin/python || { echo "$(date)  .venv missing (see sim/requirements.txt)"; exit 1; }
.venv/bin/python -W ignore sim/run_all.py
echo "$(date)  run_all.sh finished (exit $?)"
