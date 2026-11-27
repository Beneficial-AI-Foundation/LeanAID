# sim/ — virtual patients (milestone M11)

**Research artifact. Not for dosing insulin.** simglucose is an open reimplementation of
the 2008 UVA/Padova simulator, not FDA-accepted evidence; the patient profiles below
are derived from its parameters, not set by a clinician.

Closed loop: oref0 (Node, the pinned `vendor/oref0`, unmodified) and `aid-lean` (the
Lean binary) control simglucose's 30 virtual patients; simglucose's own basal-bolus
controller is the baseline.

| file | what |
|---|---|
| `harness.py` | one run: patient, controller, meal seed, fault, days |
| `monitor.py` | the per-step safety monitor (requirements R1, R2, R4, R6, R8–R12) |
| `oref0_server.js` | oref0 as one long-lived Node process (lib/profile, lib/meal, lib/iob, determine-basal) |
| `run_all.py`, `run_all.sh` | the job list of the virtual-patient runs |
| `report.py` | the report (part 4): `sim/out/report.json` and `sim/out/plots/`, written up in `docs/SIM.md` |
| `requirements.txt` | exact Python package versions (`.venv`, Python 3.9.6) |
| `regression-future-carbs.json` | an input on which aid-lean and oref0 differ (FINDINGS F-17) |
| `q6fix.js` | the fix for QUIRK Q6 (FINDINGS F-24), applied in memory to `lib/iob/history.js` |
| `q6_runs.py`, `q6_report.py` | the F-24 runs (oref0 against oref0 with the Q6 fix) and their report, `sim/out/q6-report.json`, written up in `docs/SIM.md` |

`aid-lean serve` (App/Serve.lean) reads one JSON input per line and computes IOB
(`LeanAID.Iob.generate`, lib/iob) and the decision (`LeanAID.determineBasal`) in Lean.

## One step (every 5 simulated minutes)

1. CGM: simglucose's `GuardianRT` sensor model (5-minute samples, seeded noise),
   rounded to an integer mg/dL, with the run's fault applied.
2. Meals: simglucose's `RandomScenario` (seeded; times rounded to the 5-minute grid).
   Announced: a carb entry (`carbs`, `created_at`) and a meal bolus of carbs / CR,
   rounded down to 0.05 U, at the meal's start. The patient model eats at its own rate.
3. Inputs, from the last 12 hours: glucose entries (newest first), pump history
   (Medtronic-style `TempBasal`/`TempBasalDuration`/`Bolus` records, as in oref0's
   tests), carb entries, the profile, the current temp, `autosens` ratio 1,
   `microBolusAllowed` false (SMB off).
4. oref0 runs on the input (lib/meal → meal data, lib/iob → IOB, determine-basal).
   In aid-lean runs, aid-lean also runs on exactly that input, with **meal data from
   oref0's lib/meal (JavaScript)**: COB is the one part of the aid-lean arm not
   computed by Lean. IOB and the decision are Lean's; both outputs are logged and
   compared (decision byte for byte, IOB array field by field).
5. The run's controller's decision is applied as oref0's pump loop does (a `rate` and
   `duration` set or cancel the temp; no `rate` leaves the pump as it is; `units` would
   be a bolus) and checked by the monitor.
6. The patient is simulated minute by minute for 5 minutes with the delivered insulin
   (temp or scheduled basal; boluses in the first minute).

The baseline is simglucose's `BBController` policy: basal `u2ss · BW / 6000` U/min,
and at a meal `carbs / CR + (CGM > 150) · (CGM − 140) / CF`.

## Profiles

From simglucose's `vpatient_params.csv` and `Quest.csv`, through oref0's own
`lib/profile` (so every other setting is oref0's default):

- basal = `u2ss · BW / 6000` U/min × 60 = U/h (the steady-state basal simglucose's
  BBController uses), rounded to the 0.05 U/h pump increment;
- carb ratio = `Quest.CR` (g/U); ISF = `Quest.CF` (mg/dL/U) rounded to an integer;
- `max_basal` = 3 × basal; `max_iob` = 3 × basal + 60 g / CR (three hours of basal
  plus a large-meal bolus), rounded to 0.1 U;
- DIA 5 h (oref0's minimum for its default rapid-acting curve), target 110 mg/dL;
- SMB off, autosens off (ratio 1), no temp targets.

## Faults (minutes of the simulated day, UTC)

- `dropout`: no new CGM readings 03:00–03:45 and 15:00–15:45;
- `compression`: CGM 40 mg/dL low (not below 39) 02:00–02:20;
- `missedmeal`: the largest meal of each day is eaten but not announced;
- `f11` (FINDINGS F-11): during the dropout windows the last reading keeps arriving
  with no date (`date`, `dateString` absent);
- `f12` (FINDINGS F-12): the profile has no `max_basal` (the monitor still checks R1
  against the configured value).

## Running

```bash
python3 -m venv .venv && .venv/bin/pip install -r sim/requirements.txt
lake build aid-lean
.venv/bin/python sim/harness.py --patient 'adult#001' --controller aid-lean --days 1
nohup caffeinate -i sim/run_all.sh > sim/out/run_all.log 2>&1 &
```

Each run writes `sim/out/runs/<run>.jsonl.gz` (one row per step: true BG, CGM, the
full controller input, both outputs, IOB, monitor result, insulin delivered) and,
last, `<run>.summary.json`. These are not committed (size).

## Options for FINDINGS F-24

- `--basal steps`: a basal schedule with six entries, 0.9 to 1.1 times the steady-state
  basal (`BASAL_SCHEDULES` in `harness.py`). The default `flat` is the schedule above. The
  pump follows the schedule minute by minute, and the harness sets oref0's `current_basal`
  for the simulated time on every step. The patient's insulin need does not change
  with it.
- `--controller oref0-q6fix`: oref0 with the fix for QUIRK Q6 (`sim/q6fix.js`). The oref0
  checkout is not changed on disk.
- `--shadow-q6`: also run oref0 with the fix on every input, and record each step where
  IOB or the decision differs (`q6_shadow` in the summary).
