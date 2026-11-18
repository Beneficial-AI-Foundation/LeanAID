# Overnight experiment: virtual patients (milestone M11)

Goal: run oref0 (JavaScript) and `aid-lean` (Lean) in a closed loop with the simglucose
virtual patients, and compare them. Follow `AGENTS.md`. Never push.

The work has three parts. Parts 1 and 2 happen now, while the maintainer is at the
computer, so that any permission prompts can be answered. Part 3 runs unattended
overnight and must not need you or the maintainer.

## Part 1: set up (now)

1. Create `.venv/` with `python3 -m venv .venv` and install `simglucose` from PyPI (plus
   `matplotlib` and `pandas` if not pulled in). Record the exact versions in
   `sim/requirements.txt`. If Python 3.9 is too old for simglucose, stop and say so.
2. Write the harness in `sim/`. Every 5 simulated minutes:
   - read the simulated CGM value and build oref0's inputs from the history so far:
     glucose entries, pump history (temp basals and boluses actually delivered),
     profile, current temp, meal data;
   - call the controller, apply the temp basal (and microbolus, if any) to the pump;
   - log one row: time, true glucose, CGM, the full input given to the controller,
     its output, and the insulin delivered.
3. Controllers, all given exactly the same patient, meals, sensor noise and seed:
   - **oref0**: the pinned `vendor/oref0` in Node. Keep one Node process alive rather
     than starting Node at every step, if you can.
   - **aid-lean**: the compiled binary. Use Lean for every part LeanAID implements (at
     least `determine-basal`; also IOB if the Lean core has it, adding an
     `aid-lean iob` command if needed). Anything still computed by JavaScript in this
     arm (for example meal data) must be listed in the report.
   - **baseline**: simglucose's built-in basal-bolus controller, for context only.
4. Profile for each patient: basal, carb ratio and correction factor from simglucose's
   own patient parameters (say exactly how they are derived). Use oref0's defaults for
   the rest, with `max_basal` and `max_iob` set to sensible stated values. SMB off in the
   main runs.
5. Meals: a seeded random scenario per patient (the same for every controller). Meals
   are announced: carbs entered at meal time plus a meal bolus of carbs / carb ratio.
6. Safety monitor: at every step, check the properties we proved (rate never above
   maxSafeBasal, no extra insulin when glucose is low, and the others in
   `docs/REQUIREMENTS.md` that apply to a single decision) on the actual inputs and
   outputs of both arms. Count and log every violation. A violation is a finding, not
   something to hide.

## Part 2: smoke test (now)

Run one adult for 1 simulated day with each controller. Check: the oref0 and aid-lean
runs agree, glucose stays plausible, the logs and the monitor work. Measure how long one
simulated day takes per controller, and from that estimate the run time of each item
in part 3. The overnight run lasts 12 hours of real time: size the list so that items
1 to 3 finish well within that, and fill the rest of the 12 hours with item 4. Commit the harness ("Virtual patients: harness and smoke test").

## Part 3: the overnight run (unattended)

Write `sim/run_all.sh` and start it in the background so that it survives the agent
session ending and keeps the Mac awake:

```bash
nohup caffeinate -i sim/run_all.sh > sim/out/run_all.log 2>&1 &
```

The script must stop starting new runs 12 hours after it began (finish or discard the
run in progress, and say which in the log), be resumable (skip runs whose results file
already exists), write each run to its own file in `sim/out/`, and append progress with
real times (`date`) to `sim/out/progress.log`. Runs, in this order of priority:

1. **Main**: all 30 built-in patients (adolescents, adults, children), 2 days, oref0,
   aid-lean and baseline.
2. **Faults**, oref0 and aid-lean, all 30 patients, 2 days, one fault per run:
   - sensor dropout: no new CGM readings for 45 minutes, twice a day;
   - compression low: CGM reads 40 mg/dL too low for 20 minutes, at night;
   - missed meal announcement: one meal a day with no carbs entered and no bolus.
3. **Our findings in a closed loop**, oref0 and aid-lean:
   - F-11: during a sensor dropout, the last reading keeps arriving without a
     timestamp;
   - F-12: the profile has no `max_basal`.
   Report what each one does to glucose and to insulin delivered.
4. Until the 12 hours are up: longer runs (all 30 patients, 7 simulated days, oref0 and
   aid-lean), then more meal seeds for them, one seed at a time.

Then stop. Do not start part 4 overnight.

## Part 4: the report (next morning, when asked)

Write `docs/SIM.md` and plots in `sim/out/`:
- for each controller and group: time in range 70–180 mg/dL, time below 70 and below
  54, time above 180 and 250, mean glucose, coefficient of variation, and insulin per day;
- **whether oref0 and aid-lean made identical decisions at every step**, and the full
  glucose trace comparison; give the first step of any difference, with its input;
- every safety-monitor violation, in either arm;
- the fault and findings runs;
- limits: simglucose is an open reimplementation of the 2008 UVA/Padova simulator, not
  FDA-accepted evidence; the profiles are derived, not tuned by a clinician; 30 patients,
  2 days; nothing here says the algorithm is safe for people.

Add the real times to `docs/LOG.md`. Commit. Do not edit `site/index.html`; the page is
updated after the results are reviewed.
