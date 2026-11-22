# openaps/oref0: evidence

Repository: https://github.com/openaps/oref0 (checked 2026-11-22).

- `master` = `88cf032aa74ff25f69464a7d9cd601ee3940c0b3` (2022-06-18), the same commit as our
  pin `vendor/oref0` (0.7.1).
- `dev` = `d219baf9559d62a8bb0bd42014192a2d7c0839ef` (last commit 2026-03-09), analysed in
  full (source extracted from a blobless clone at that SHA, the same files as a depth-1 clone).
- All 33 branches were listed (one API call). The tree hashes of `lib/` and `bin/` were compared
  locally with `master` in a blobless bare clone (commits and trees only, 2.3 MB), not through
  the API. `carbsreq-parse-error` and `dependabot/pip/requests-2.32.0` have `lib/` and `bin/`
  identical to 0.7.1. The other 14 branches with commits after 0.7.1 change
  `lib/determine-basal/determine-basal.js` (and other files), but none changes
  `lib/basal-set-temp.js`, `lib/round-basal.js` or `lib/glucose-get-last.js`.

## Verdicts (tested: `node scripts/findings/run.js <branch lib/>`)

Every tested branch: F-04 PRESENT, F-11 PRESENT, F-12 PRESENT, with the same rates as on the
pin (0.83 → 0.85 U/h; undated → 3.5 U/h; missing limits → 5.9 U/h). Full output per branch
with SHA and last commit date: `branches-tests.txt` (17 branches: master, the two identical
ones, and the 14 with commits after 0.7.1 whose `lib/` differs).

## The three sites (`quoted-lines.txt`, dev line numbers; master in brackets)

- F-04: `lib/basal-set-temp.js:21-30`: `rate = maxSafeBasal` and then
  `suggestedRate = round_basal(rate, profile)`; `lib/round-basal.js:30-39` rounds to nearest.
  Also `determine-basal.js:1173-1177` [1162-1166] pre-rounds `round_basal(maxSafeBasal)` in the
  SMB branch before calling `setTempBasal` (which re-caps and re-rounds, same result).
- F-11: `determine-basal.js:149-150` [`150`]: `minAgo = round((systemTime - bgTime)/60/1000, 1)`;
  `:195` [187], `:206`, `:209` [198]: `minAgo > 12 || minAgo < -5`.
- F-12: `lib/basal-set-temp.js:10-16`: `Math.min(profile.max_basal, 3 * max_daily_basal,
  4 * current_basal)`; `:26` `rate > maxSafeBasal` (false for NaN).

## Can the triggers happen on an oref0 rig?

How the inputs are built (dev; same code on master):

- **Glucose** (`bin/oref0-determine-basal.js:95`): `glucose_status = getLastGlucose(glucose_data)`.
  `lib/glucose-get-last.js:1-3` takes the date as `entry.date || Date.parse(entry.display_time)
  || Date.parse(entry.dateString)`, so an entry without any of these has date NaN. But every
  delta is computed from that date (`:36-38`), so all deltas are 0, and determine-basal's
  flat-CGM check (`determine-basal.js:177-185`, `tooflat`) then refuses to raise the rate.
  Tested through oref0's own `glucose-get-last.js` (`scripts/findings/f11-pipeline.js`,
  output in `F-11-pipeline.txt`): dated newest reading → 3.5 U/h; undated newest reading →
  "CGM data is unchanged … no temp". The one exception is a device named `fakecgm`
  (`:179-181`, simulator mode), which is not a real setup. A `glucose_status` built by other
  code (as in Trio/iAPS or a caller of `lib/` without `glucose-get-last`) does not get this
  protection. **F-11 is defensive hardening for an oref0 rig.**
- **max_basal** (`lib/profile/basal.js:40-42`): `inputs.settings.maxBasal`, from
  `settings/settings.json`, written by `mdt settings` (a read of the Medtronic pump,
  `bin/oref0-pump-loop.sh:951-954`). `valid_settings` (`:955-959`) checks only that `maxBolus` is
  a number, not `maxBasal`; `lib/profile/index.js:147` rejects `max_basal < 0.1`, which is false
  for `undefined`. So a settings file without `maxBasal` would pass both checks and give F-12.
  A normal pump read always contains `maxBasal`, and the value is the pump's own Max Basal
  setting, which the Medtronic pump itself enforces on temp basals (pump behaviour, not
  checked in code here). **F-12 is defensive hardening for an oref0 rig with a Medtronic
  pump**; it matters to any other caller of `lib/` that builds the profile itself.
- **max_daily_basal** (`lib/profile/basal.js:33-36`): `Number(maxRate.rate) * 1000 / 1000` over
  the basal schedule; a non-numeric rate gives NaN, which passes the `=== 0` check at
  `lib/profile/index.js:143` and makes `maxSafeBasal` NaN (`Math.min` with a NaN is NaN).
- **F-04**: `max_basal` comes from the pump and is on the pump's grid, so it does not round up.
  But with autotune, `bin/oref0-get-profile.js:239-240` replaces the basal schedule by
  autotune's, whose rates are rounded to 0.001 U/h (`lib/autotune/index.js:188` and others),
  so `current_basal` and `max_daily_basal` are usually off the pump grid, and the limits
  `4 × current_basal` / `3 × max_daily_basal` round up in about 40 % of cases
  (`scripts/findings/f04-search.out.txt`). Even without autotune, on x23/x54 pumps
  `3 × max_daily_basal` can round up above 1 U/h (e.g. 3 × 0.375 = 1.125 → 1.15). The
  overshoot is at most half a pump increment (0.025 U/h below 1 U/h on default pumps; 0.025
  above 1 U/h), and the pump's own Max Basal still applies. **F-04 can occur in practice;
  low severity.**

## Suggested fixes (each applied alone to a copy of dev `lib/` under `upstream/`)

| fix | patch | Part 1 tests on the patched copy |
|---|---|---|
| F-04: round down when the rounded rate exceeds `maxSafeBasal` | `F-04.patch` | F-04 ABSENT (0.83 → 0.80 U/h), F-11/F-12 still PRESENT (`F-04-patched-tests.txt`) |
| F-11: `!(minAgo <= 12 && minAgo >= -5)` at the three checks | `F-11.patch` | F-11 ABSENT (undated → no temp), others PRESENT (`F-11-patched-tests.txt`) |
| F-12: if `maxSafeBasal` is not a finite positive number, cap at `current_basal` (cancel the temp if that is also invalid) and report the error | `F-12.patch` | F-12 ABSENT (→ 0.9 U/h = scheduled basal), others PRESENT (`F-12-patched-tests.txt`) |

F-04 fix, differential check (`scripts/findings/f04-fix-differential.js`, output
`F-04-differential.txt`): 3,944,160 `setTempBasal` calls (both pump grids); the unpatched code
exceeds `maxSafeBasal` in 526,342, the patched code in none, and the two differ in exactly
those 526,342 cases. The F-11 and F-12 fixes only change behaviour when `minAgo` or
`maxSafeBasal` is NaN (for finite values `!(m <= 12 && m >= -5)` equals `m > 12 || m < -5`).

**Not done: oref0's own test suite on the patched copies.** Running mocha on the clone's
`tests/` (with `vendor/oref0/node_modules`, nothing installed) was blocked twice by the
session's permission classifier; it needs the maintainer's permission. Until then, the
patches are tested only by the Part 1 scripts and the differential check above.
