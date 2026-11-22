# Artificial-Pancreas/iAPS: evidence

Repository: https://github.com/Artificial-Pancreas/iAPS (checked 2026-11-22; `git clone --depth 1`,
66 MB, then `git fetch --depth 1 origin dev`).

- `main` (default) = `486f85b271333dbd53685bc36aeed8b7a04d1c43` (2026-11-07).
- `dev` = `ea425ea81670e6fa9f5377f1f1e308b56dc25d2e` (2026-11-22). The bundles, the `prepare/`
  scripts and every Swift file quoted below are identical on `main` and `dev`
  (`git diff --stat` empty), so all verdicts apply to both.
- 20 other branches exist (`git ls-remote`: `alpha`, `release/8.3.9`, feature branches); not checked.

## What iAPS runs (verified from the code)

iAPS runs oref JavaScript in JavaScriptCore (`FreeAPS/Sources/APS/OpenAPS/JavaScriptWorker.swift`):
minified webpack bundles in `FreeAPS/Resources/javascript/bundle/` (`freeaps_determineBasal`,
`freeaps_basalSetTemp`, `freeaps_glucoseGetLast`, …), called from
`FreeAPS/Resources/javascript/prepare/determine-basal.js`: `glucose_status =
freeaps_glucoseGetLast(glucose)` (line 91), then `freeaps_determineBasal(...,
freeaps_basalSetTemp, ...)` with oref0's 10-argument signature (line 116). The bundles are built by
`scripts/webpack.config.js` from `OREF0_DIST_PATH` (default `./lib`, which is not in the repository):
**the JS source repository is not named anywhere in iAPS**, so the fixes below are shown on the
bundles.

## Verdicts (tested on the bundles; output `tests-main.txt`)

The bundles were loaded under Node through shims (`scripts/findings/make-bundle-lib.js`, one `vm`
context per bundle, with the `process.stderr.write` object that iAPS's `prepare/log.js` defines),
then `scripts/findings/run.js` was run unchanged.

| finding | verdict | rates |
|---|---|---|
| F-04 | **PRESENT** (tested) | max_basal 0.83 → 0.85 U/h; also end to end through `freeaps_determineBasal` |
| F-11 | **PRESENT** (tested) | undated → 3.5 U/h; dated 60 min ago → no temp |
| F-12 | **PRESENT** (tested) | missing `max_basal` and/or `max_daily_basal` → 5.9 U/h; control 3.5 |

Sites in the minified code (`quoted-lines.txt`): `basal-set-temp.js`
`a<0?a=0:a>l&&(a=l);var u=r(760)(a,n)` (cap then round to nearest, module 760 = round_basal);
`getMaxSafeBasal` = `Math.min(a.max_basal,e*a.max_daily_basal,r*a.current_basal)`;
`determine-basal.js` `f=n((g-new Date(e.date))/60/1e3,1)` and `if(v<=10||38===v||_>=3||f>12)return`.
iAPS's staleness check is only `minAgo > 12` (no future-date check, no "too old" reason), and like
trio-oref it has no flat-CGM early exit, so through its own `glucose-get-last` bundle an undated
newest reading is dosed (3.5 U/h; `tests-main.txt`, last block).

## Can the triggers happen in iAPS?

- **F-11: no (two independent barriers in Swift).** Glucose is read as `[BloodGlucose]`
  (`OpenAPS.swift:410-413`; `APSManager.swift:362`), and `BloodGlucose` requires `date: Decimal`
  and `dateString: Date` (`BloodGlucose.swift:48-49`, `:100-101`), so an entry without a date
  fails to decode ("Not enough glucose data", `APSManager.swift:362-366`). Separately,
  `APSManager.swift:368-373` stops the loop when the newest glucose is more than 12 min old
  ("Glucose data is stale"). Defensive hardening only.
- **F-12: only through user middleware.** `max_basal` comes from `settings.json`, an encoded
  `PumpSettings` whose `maxBasal: Decimal` is non-optional (`PumpSettings.swift:6`), via
  `prepare/profile.js:109` (`inputs.settings = pumpsettings_data`). But iAPS runs the user's own
  middleware JS on the profile before determine-basal (`OpenAPS.swift:108-119`,
  `prepare/middleware.js:15`, `:33`), so a middleware that deletes or miscomputes `max_basal`,
  `max_daily_basal` or `current_basal` produces F-12. In closed loop, the rate goes to the pump
  without any app-side cap (`APSManager.swift:815-818`: `pump.enactTempBasal(unitsPerHour: rate /
  concentration)`); the `min(rate, maxBasal)` at `APSManager.swift:522-523` is only in the manual
  `enactTempBasal` path. Defensive hardening (needs a user-written middleware error).
- **F-04: yes.** Max Basal is typed in a free `DecimalTextField` with a plain `.decimal`
  `NumberFormatter` (`PumpSettingsEditorRootView.swift:9-13`, `:38-42`), so values like 0.83 or
  2.33 can be entered; the value stored is what the pump manager returns from
  `syncDeliveryLimits` (`PumpSettingsEditorProvider.swift:45-69`), not checked here per pump
  driver. With such a value as the binding limit, the issued rate is up to 0.025 U/h above it,
  and the closed loop enacts it unchanged (above). Low severity.

## Suggested fixes (bundle versions; each applied alone to a copy under `upstream/`)

| fix | patch | Part 1 tests on the patched copy |
|---|---|---|
| F-04: if the rounded rate exceeds `maxSafeBasal`, round `maxSafeBasal` down to the pump step | `F-04-bundle.patch` | F-04 ABSENT (0.83 → 0.80), others PRESENT (`F-04-patched-tests.txt`) |
| F-11: `f>12` → `!(f<=12)` (NaN counts as stale; no future check added, to keep iAPS's behaviour otherwise) | `F-11-bundle.patch` | F-11 ABSENT (undated → no temp), others PRESENT |
| F-12: if `maxSafeBasal` is not a finite positive number, cap at `current_basal` (cancel if that is invalid too) | `F-12-bundle.patch` | F-12 ABSENT (→ 0.9 U/h), others PRESENT |

F-04 differential check on the bundle (`F-04-bundle-differential.txt`): 3,944,160 cases; unpatched
above the limit in 526,342, patched in none, and they differ only in those cases. In the iAPS
source the same changes are the oref0 patches in `docs/upstream/oref0/` (applied to whatever
repository `OREF0_DIST_PATH` points to). oref0's mocha tests were not run (see oref0 README).

## Contact

No `SECURITY.md`; `.github/` has `FUNDING.yml` and `workflows` only (no issue templates).
`README.md:111-112`: Discord (https://discord.com/invite/ptkk2Y264Z) and a Facebook group.
Whether GitHub issues or private vulnerability reporting are enabled was not checked.
