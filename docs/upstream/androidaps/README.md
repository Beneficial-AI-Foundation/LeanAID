# nightscout/AndroidAPS: evidence

Repository: https://github.com/nightscout/AndroidAPS (checked 2026-11-22; `git clone --depth 1`,
263 MB, then `git fetch --depth 1 origin dev`, 270 MB in total).

- `master` (default) = `f77abd9b82b308e8fc330da0d7a31370fb4a0f49` (2026-10-31).
- `dev` = `b5b3c1a402d336432d45d8b15cee231b13b56713` (2026-11-22). `SafetyPlugin.kt`,
  `GlucoseStatusSMB.kt`, `OapsProfile.kt` and `LoopPlugin.kt` are identical; the
  `DetermineBasal*.kt` files differ, but no changed line touches the three sites (the changes
  are in autotune and time-zone handling). The verdicts apply to both.

## What AndroidAPS runs (verified from the code)

Kotlin ports of determine-basal, one per algorithm plugin:
`plugins/aps/src/commonMain/kotlin/app/aaps/plugins/aps/openAPSSMB/DetermineBasalSMB.kt`,
`openAPSAutoISF/DetermineBasalAutoISF.kt`, `openAPSAMA/DetermineBasalAMA.kt`. oref JavaScript is
present only as test assets (`app/src/androidTest/assets/OpenAPS*/`), used to compare the ports
with the JS; it is not used by the app. Not built; checked by reading.

## Verdicts (by inspection; `quoted-lines.txt`)

| finding | SMB | AutoISF | AMA | evidence |
|---|---|---|---|---|
| F-04 | ABSENT | ABSENT | ABSENT | `round_basal` is the identity in all three ports (`DetermineBasalSMB.kt:43`, `DetermineBasalAutoISF.kt:39`, `DetermineBasalAMA.kt:35`), so the algorithm's rate is never rounded above `maxSafeBasal`. Rounding to the pump step happens afterwards in `SafetyPlugin.applyBasalConstraints` with `Round.floorTo` (`SafetyPlugin.kt:115-120`), commented "floor, not round-to-nearest, so a max-constrained rate is never rounded back UP above the limit". The loop applies these constraints to the algorithm result (`LoopPlugin.kt:600-603`). |
| F-11 | ABSENT | ABSENT | ABSENT (no age check in the port; see right) | `GlucoseStatusSMB.date: Long = 0L` (`GlucoseStatusSMB.kt:12`): never NaN, and a missing date (0) gives an age of decades, which `minAgo > 12` rejects (`DetermineBasalSMB.kt:240-256`; AutoISF `:237-253`). Before any port runs, `getGlucoseStatusData(allowOldData = false)` returns null when the newest reading is older than 7 min (`GlucoseStatusCalculatorSMB.kt:28-43`), and the plugins stop on null (`OpenAPSAMAPlugin.kt:117`, `:130`; `OpenAPSSMBPlugin.kt:256`, `:269`). The AMA port has no BG-age check of its own and relies on this. |
| F-12 | ABSENT | ABSENT | ABSENT | Kotlin's `min` with NaN would give NaN as in JS (`getMaxSafeBasal`, `DetermineBasalSMB.kt:132-133`), but the inputs are non-null `Double`s (`OapsProfile.kt`), with `max_basal = constraintsChecker.getMaxBasalAllowed(profile).value()` and `current_basal` from the pump (`OpenAPSSMBPlugin.kt:376-377`, `:409`), and `max_daily_basal` and the current basal are checked against hard limits before the algorithm runs (`:285-286`). After the algorithm, independent caps apply regardless of `maxSafeBasal`: `applyBasalConstraints` of the APS plugin (max basal from preferences, `max_basal_multiplier × basal`, `max_daily_multiplier × max daily basal`, `OpenAPSSMBPlugin.kt:502-524`) and of `SafetyPlugin` (hard limit, pump maximum, `SafetyPlugin.kt:103-113`). |

Note: `DetermineBasalSMB.setTempBasal` already falls back to the profile basal when the requested
*rate* is not finite (`:140-150`), but does not check `maxSafeBasal` itself. With NaN limits the
post-algorithm caps above still apply, so this is not a finding in practice; it could be mentioned
to the maintainers as a one-line consistency improvement, not as a report.

## Can the triggers happen in AndroidAPS?

No: dates are `Long` timestamps from the database with a separate 7-minute freshness filter;
limits come from validated preferences and the profile; and rounding after the algorithm is
downward. Nothing to report.

## Contact

No `SECURITY.md`. `.github/` has `ISSUE_TEMPLATE`; `README.md:6` links the Discord server
(https://discord.gg/4fQUWHZ4Mw).
