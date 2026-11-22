# Which projects still have F-04, F-11 and F-12

Survey made 2026-11-22. Research artifact: nothing here is advice on dosing insulin. The findings
are described in `docs/FINDINGS.md`; the reproduction tests are in `scripts/findings/`. Evidence
for each target (commit SHAs, test outputs, quoted lines with line numbers, patches and their test
results) is in `docs/upstream/<target>/`. All downloads were deleted after use; to look again,
clone the same SHA.

**How each verdict was obtained.** *Tested*: `node scripts/findings/run.js <lib>` on the target's
JavaScript (for minified bundles, through `scripts/findings/make-bundle-lib.js`). *By inspection*:
Swift or Kotlin read and quoted, not built or run. PRESENT means the trigger input shows the defect
while the control behaves correctly (exact rule in `scripts/findings/*.js`).

## Targets and commits

| target | what runs | branch @ commit checked | how |
|---|---|---|---|
| [openaps/oref0](https://github.com/openaps/oref0) | JS (rigs) | `master` @ `88cf032` (= our pin, 0.7.1); the 14 branches with commits after 0.7.1, including `dev` @ `d219baf`; 2 more whose `lib/` and `bin/` equal 0.7.1 (17 in all, SHAs in `docs/upstream/oref0/branches-tests.txt`) | tested |
| [nightscout/Trio](https://github.com/nightscout/Trio) | Swift port (`Trio/Sources/APS/OpenAPSSwift/`) | `main` @ `0b29cd5` (v1.0.2); `dev` @ `d37fe34` | inspection |
| [nightscout/trio-oref](https://github.com/nightscout/trio-oref) | JS kept by Trio as reference for its port's tests; run by no app at these commits | `dev` @ `8282ce7`; `main` @ `a9bdbb1`; `several_Issues` @ `e9db31f` | tested |
| [Artificial-Pancreas/iAPS](https://github.com/Artificial-Pancreas/iAPS) | minified JS bundles in JavaScriptCore | `main` @ `486f85b`; `dev` @ `ea425ea` (same bundles) | tested |
| [Artificial-Pancreas/oref0](https://github.com/Artificial-Pancreas/oref0) | JS; almost certainly the source of iAPS's bundles (see `docs/upstream/forks/README.md`) | `iaps` @ `10bdfe3` | tested |
| [nightscout/AndroidAPS](https://github.com/nightscout/AndroidAPS) | Kotlin ports (SMB, AutoISF, AMA) | `master` @ `f77abd9`; `dev` @ `b5b3c1a` | inspection |
| [ivalkou/freeaps](https://github.com/ivalkou/freeaps) (FreeAPS X) | minified JS bundles; unchanged since 2022 (master) / 2023 (dev) | `master` @ `3a2908c`; `dev` @ `360a3b8` | tested |
| 47 forks of openaps/oref0 pushed since 2023-11-22 | JS | 36 identical to 0.7.1 in `lib/` and `bin/` (by identity); 11 different (tested) | see `docs/upstream/forks/` |

Not checked: feature branches of Trio (7), iAPS (20) and AndroidAPS; Trio releases before the
Swift port (which ran trio-oref as JS); forks of forks; `Jon-b-m/middleware` (iAPS middleware
examples, not an algorithm).

## Verdicts

| target | F-04 | F-11 | F-12 | evidence |
|---|---|---|---|---|
| openaps/oref0 master, dev, all branches | PRESENT (tested) | PRESENT (tested) | PRESENT (tested) | `docs/upstream/oref0/branches-tests.txt`; sites `lib/basal-set-temp.js:21-30`, `lib/determine-basal/determine-basal.js:187,198` (master) / `:195,206,209` (dev) |
| Trio (Swift port) | ABSENT (inspection) | ABSENT (inspection) | ABSENT (inspection) | rounds **down** (`TempBasalFunctions.swift:17-24`); dates non-optional (`BloodGlucose.swift:105`, `GlucoseStatus.swift:18`); nil limits throw (`TempBasalFunctions.swift:32-36`) |
| trio-oref dev, main, several_Issues | PRESENT (tested) | PRESENT (tested) | PRESENT (tested) | `docs/upstream/trio-oref/` |
| iAPS main = dev (bundles) | PRESENT (tested) | PRESENT (tested) | PRESENT (tested) | `docs/upstream/iaps/tests-main.txt`; minified sites quoted in `quoted-lines.txt` |
| Artificial-Pancreas/oref0 `iaps` | PRESENT (tested) | PRESENT (tested) | PRESENT (tested) | `docs/upstream/forks/Artificial-Pancreas-oref0/` |
| AndroidAPS SMB / AutoISF / AMA | ABSENT (inspection) | ABSENT (inspection) | ABSENT (inspection) | `round_basal` is the identity, then `Round.floorTo` (`SafetyPlugin.kt:115-120`); dates are `Long` and data older than 7 min is dropped (`GlucoseStatusCalculatorSMB.kt:40-43`); limits non-null and capped again after the algorithm (`OpenAPSSMBPlugin.kt:502-524`, `SafetyPlugin.kt:103-113`) |
| FreeAPS X master = dev (bundles) | PRESENT (tested) | PRESENT (tested) | PRESENT (tested) | `docs/upstream/freeaps/tests-master.txt` |
| 36 identical forks | PRESENT (by identity) | PRESENT (by identity) | PRESENT (by identity) | `docs/upstream/forks/identical.md` |
| 11 different forks | PRESENT (tested) | PRESENT (tested) | PRESENT (tested) | `docs/upstream/forks/README.md` |

## Can the trigger happen in practice?

The decisive question for each target. In short: the JavaScript has all three defects everywhere,
and the apps differ in whether their own code can feed it the trigger.

- **openaps/oref0 (rigs)** (`docs/upstream/oref0/README.md`)
  - F-04 **yes, low**: `max_basal` is read from the pump and is on the grid, but with autotune
    the basal schedule has 0.001 U/h precision (`lib/autotune/index.js:188`,
    `bin/oref0-get-profile.js:239-240`), so `4 × current_basal` / `3 × max_daily_basal` round
    up in about 40 % of values; on x23/x54 pumps `3 × max_daily_basal` can also round up above
    1 U/h. Overshoot at most 0.025 U/h; the pump's own Max Basal still applies.
  - F-11 **no, on a rig**: oref0's `glucose-get-last.js` gives zero deltas for an undated
    newest reading, and the flat-CGM check then refuses to dose (tested through the real
    function: "CGM data is unchanged", no temp). It is a second barrier, not a fix: any
    other caller of `determine-basal` that builds `glucose_status` itself, or removes the
    flat-CGM exit (trio-oref and iAPS did, see below), is exposed.
  - F-12 **only with a malformed settings file**: `max_basal` = `settings.json` `maxBasal` from
    a pump read; `valid_settings` checks only `maxBolus` and `profile/index.js:147`
    (`max_basal < 0.1`) passes `undefined`, so a file without `maxBasal` would get through, but
    a pump read always contains it, and the Medtronic pump enforces its own max basal (pump
    behaviour, not checked in code).
- **Trio, AndroidAPS**: not applicable (findings absent).
- **trio-oref**: the code has all three defects, and unlike oref0, the flat-CGM exit was removed
  (commit `2319a16`), so through its own `glucose-get-last` an undated reading is dosed. But no
  app runs this JS at the checked commits: Trio runs the Swift port.
- **iAPS** (`docs/upstream/iaps/README.md`)
  - F-04 **yes, low**: Max Basal is a free decimal field (`PumpSettingsEditorRootView.swift:9-13`,
    `:38-42`), so 0.83 can be entered; the closed loop enacts the algorithm's rate unchanged
    (`APSManager.swift:815-818`; the `min(rate, maxBasal)` at `:522-523` is only in the
    manual path).
  - F-11 **no**: glucose must decode as `BloodGlucose` with non-optional `date`/`dateString`
    (`BloodGlucose.swift:48-49`) and `APSManager.swift:368-373` stops the loop when glucose is
    older than 12 min. (The JS alone would dose: no flat-CGM exit, staleness check
    `minAgo > 12` only.)
  - F-12 **only through user middleware**: `maxBasal` is a non-optional `Decimal`, but iAPS runs
    the user's middleware JS on the profile before determine-basal (`OpenAPS.swift:108-119`,
    `prepare/middleware.js:15`, `:33`); a middleware mistake that leaves `max_basal`,
    `max_daily_basal` or `current_basal` non-numeric removes the cap, and the closed loop has
    no app-side cap behind it.
- **FreeAPS X**: same Swift barriers for F-11 (and its `glucose-get-last` throws on an undated
  reading); unmaintained.
- **Forks**: like oref0. In 3 groups of older forks `glucose-get-last` throws on an undated
  reading; the `iaps` fork behaves like iAPS's JS.

## Recommendations

Severity is our estimate. It rests on: how large the effect is when triggered (F-04: ≤ 0.025 U/h
above the limit; F-11: 3.5 U/h on stale/undated data in the test input; F-12: 5.9 U/h = 6.6 ×
scheduled basal in the test input, and up to 9.8 × `max_basal` in the closed-loop simulation,
`docs/SIM.md`) and on whether the app can produce the trigger (above).

| target | F-04 | F-11 | F-12 |
|---|---|---|---|
| openaps/oref0 | **report as hardening** (reachable with autotune / x23-x54, ≤ 0.025 U/h) | **report as hardening** (masked on rigs by the flat-CGM check; matters to every downstream user of `lib/`) | **report as hardening** (needs a settings file without `maxBasal`; pump limit behind it) |
| Trio | do not report (absent; the port already rounds down) | do not report (absent) | do not report (absent) |
| trio-oref | do not report (not run by any app checked; Trio's port is correct) | do not report, same reason; optionally mention to Trio that the reference JS lacks the flat-CGM exit | do not report, same reason |
| iAPS (+ Artificial-Pancreas/oref0 `iaps`) | **report as hardening** (reachable with a typed Max Basal, ≤ 0.025 U/h) | do not report (unreachable: two Swift barriers) | **report as hardening** (reachable only through user middleware; no app-side cap in closed loop) |
| AndroidAPS | do not report (absent; already floors) | do not report (absent) | do not report (absent) |
| FreeAPS X | do not report (unmaintained since 2022/2023, superseded by iAPS/Trio) | do not report | do not report |
| forks | do not report (personal; identical ones are fixed by fixing oref0) | do not report | do not report |

No finding is recommended as a safety issue. None is reachable with high effect in an app's
normal input path: F-11 and F-12 have large effects, but every app checked builds the inputs so
that the trigger cannot occur (or occurs only through user-written code or a malformed file),
and F-04, which is reachable, is at most half a pump step.

Drafts (one per issue): `docs/upstream/oref0-F-04.md`, `docs/upstream/oref0-F-11.md`,
`docs/upstream/oref0-F-12.md`, `docs/upstream/iaps-F-04.md`, `docs/upstream/iaps-F-12.md`.

## Channels

| project | security policy | channel | privately first? |
|---|---|---|---|
| openaps/oref0 | none (no `SECURITY.md`) | GitHub issues with the bug-report template (`.github/ISSUE_TEMPLATE/--bug-report.md`); `CONTRIBUTING.md:35` asks for issues and PRs | not needed: hardening, no reachable safety issue on rigs. Public issues also reach the downstream maintainers who copy `lib/`. |
| iAPS | none (no `SECURITY.md`; `.github/` has no issue templates) | Discord (`README.md:111`); GitHub issues on the repository not checked | not needed for these two (hardening); a short note on Discord before filing may help, since the JS source repo (`Artificial-Pancreas/oref0` `iaps`) is not linked from iAPS |
| Trio | none | Discord (`README.md:105`, `CONTRIBUTING.md:117`) | nothing to report |
| AndroidAPS | none | Discord (`README.md:6`), issue templates | nothing to report |

## Limits of this survey

- **oref0's own test suite was not run on the patched copies.** Running mocha on a clone's
  `tests/` (with `vendor/oref0/node_modules`, nothing installed) was blocked by this session's
  permission classifier; it needs the maintainer's go-ahead. The patches are tested by the
  Part 1 scripts on every JS target and, for F-04, by a differential check over 3.9 million
  `setTempBasal` calls (`docs/upstream/oref0/F-04-differential.txt`).
- Swift and Kotlin verdicts are by reading only (not built, as required).
- Pump-side behaviour (Medtronic max basal, LoopKit drivers' rounding) is stated from general
  knowledge where marked, not from code.
- Downloads: largest single target AndroidAPS, 263 MB (`--depth 1`), 270 MB after fetching `dev`;
  all under the 1 GB limit. `upstream/` was deleted at the end. GitHub API: 53 unauthenticated
  calls (`docs/upstream/api-calls.log`); branch lists and commit SHAs came from `git ls-remote`.
