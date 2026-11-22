# nightscout/Trio: evidence

Repository: https://github.com/nightscout/Trio (checked 2026-11-22; `git clone --depth 1`, 59 MB;
then `git fetch --depth 1 origin dev`, 82 MB in total).

- `main` = `0b29cd53415e7f0e668677749cad8daf81c68c2f` (tag v1.0.2, 2026-10-07).
- `dev` = `d37fe347e0b0758510e58f9edb0bae14b8a3dc64` (2026-11-19).
- Other branches (`git ls-remote`, no API call): `archive/oref-swift-port`,
  `claude/trusting-curie-yk6dsa`, `enable-oref-as-non-testing-package`, `feat/docs-assistant`,
  `feat/snooze-sheet-thresholds`, `feat/tandem`, `feat/therapySettings-coreData`: feature
  branches, not checked.

## What Trio runs (verified from the code)

Trio no longer runs oref JavaScript. `OpenAPS.determineBasal` calls
`DeterminationGenerator.generate` (`Trio/Sources/APS/OpenAPS/OpenAPS.swift:689-719` on main;
line 690 on dev), the Swift port in `Trio/Sources/APS/OpenAPSSwift/`. `Trio/Resources` has no
`javascript/` folder and `Trio.xcodeproj/project.pbxproj` references no `.js` file. The JS
source `trio-oref/lib/` is kept in the repository (from `nightscout/trio-oref` branch `dev`,
commit `8282ce7`, per `oref0_source_version.txt`) and is used as the reference by the port's
tests (`TrioTests/OpenAPSSwiftTests/`). It is checked as a separate target
(`docs/upstream/trio-oref/`).

## Verdicts (Swift port, by inspection; main and dev identical at these lines)

| finding | verdict | evidence (`quoted-lines.txt`) |
|---|---|---|
| F-04 | **ABSENT** (by inspection) | `TempBasalFunctions.swift:17-24`: `roundBasal` returns the largest pump-supported rate `<= basalRate` (`supportedBasalRates.lazy.filter { $0 <= basalRate }.max() ?? 0`), or rounds down to 3 decimals if no pump is paired. `setTempBasal` caps first (`:55-60`) and then calls this, so the issued rate never exceeds `maxSafeBasal`. `APSManager.swift:826-834` (dev `:840-848`) enacts the rate without rounding again. |
| F-11 | **ABSENT** (by inspection) | The reading date is `BloodGlucose.dateString: Date`, non-optional and decoded with `decode` (`BloodGlucose.swift:105`; a reading without it fails to decode); `getGlucoseStatus` uses it (`DetermineBasal+Helpers.swift:31-45`) and `GlucoseStatus.date: Date` is non-optional (`GlucoseStatus.swift:17-18`). `minAgo` (`DetermineBasalGenerator.swift:595`) is therefore always a finite number, and the check `minAgo > 12 || minAgo < -5` (`:621`, `:638-639`; dev `:613`, `:630`) is never bypassed. |
| F-12 | **ABSENT** (by inspection) | `getMaxSafeBasalRate` (`TempBasalFunctions.swift:27-43`) throws `invalidBasalRateOnProfile` when `currentBasal`, `maxDailyBasal` or `maxBasal` is nil, instead of returning NaN; values are `Decimal` decoded from JSON, which has no NaN. `profile.maxBasal = pumpSettings.maxBasal` (`ProfileGenerator.swift:140`), where `PumpSettings.maxBasal: Decimal` is non-optional (`PumpSettings.swift:6`); `max_basal < 0.1` is rejected (`:157-160`). |

The in-tree JavaScript `trio-oref/lib/` gives PRESENT for all three (tested,
`trio-oref-intree-tests.txt`). That code is not executed by the app at these commits.

## Can the triggers happen in the Trio app?

No: the port's types rule out an undated reading and a missing limit, and its rounding is
downward. Nothing to report to Trio. (The port already contains the F-04 fix proposed for
oref0, in the comment at `TempBasalFunctions.swift:15-16`.)

## Contact

No `SECURITY.md`; `.github/` has `ISSUE_TEMPLATE` and `CODEOWNERS`. `README.md:105` and
`CONTRIBUTING.md:117` direct questions and design discussion to the Trio Discord
(https://discord.triodocs.org).
