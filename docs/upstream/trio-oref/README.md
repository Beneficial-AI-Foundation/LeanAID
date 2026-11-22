# nightscout/trio-oref: evidence

Repository: https://github.com/nightscout/trio-oref (checked 2026-11-22; `git clone --depth 1`,
3.1 MB). Default branch `dev` = `8282ce71a57d09a160e92ecd2baf28a70c89694d` (2025-11-19), the
commit copied into Trio's `trio-oref/` (Trio `oref0_source_version.txt`). Other branches
(`git ls-remote`): `main` `a9bdbb1` (2024-02-03), `several_Issues` `e9db31f` (2024-03-07),
`fix-bundle-naming` `f21a187` (merged into dev).

## Verdicts (tested: `node scripts/findings/run.js upstream/trio-oref/lib`, output `tests.txt`)

| branch | F-04 | F-11 | F-12 |
|---|---|---|---|
| dev `8282ce7` | PRESENT (0.83 → 0.85 U/h) | PRESENT (undated → 3.5 U/h; dated 60 min → no temp) | PRESENT (→ 5.9 U/h; control 3.5) |
| main `a9bdbb1`, several_Issues `e9db31f` | PRESENT | PRESENT | PRESENT (`other-branches-tests.txt`) |

`determine_basal` here takes five more arguments than oref0's; the test harness passes neutral
values (no override, no dynamic ISF; `scripts/findings/common.js`). `lib/basal-set-temp.js` and
`lib/round-basal.js` are byte-identical to oref0 0.7.1.

## Difference from oref0 that matters for F-11

oref0 has a second line of defence: an undated newest reading makes all deltas 0 in
`glucose-get-last.js`, and the flat-CGM check (`tooflat`) refuses to dose. trio-oref removed the
early exit for flat data (commit `2319a16`, "Remove short and long delta condition to avoid early
exit breaking loop", listed in Trio's `oref0_source_version.txt`): the flat case now only sets a
reason (`determine-basal.js:435-441`), and the early return (`:443`) covers only
`bg <= 10 || bg === 38 || noise >= 3 || minAgo > 12 || minAgo < -5`. So through trio-oref's own
`glucose-get-last.js` the undated newest reading is dosed: 3.5 U/h (`F-11-pipeline.txt`).

## Who runs this code?

At the checked commits, no shipped app executes trio-oref: Trio runs its Swift port (see
`docs/upstream/trio/README.md`) and keeps this JS as the reference for the port's tests. Older
Trio releases (before the Swift port) ran it as a bundle; those are not checked here. iAPS is
checked separately (`docs/upstream/iaps/`).

## Suggested fixes (each applied alone to a copy of `lib/` under `upstream/`)

| fix | patch | Part 1 tests on the patched copy |
|---|---|---|
| F-04 | `F-04.patch` | F-04 ABSENT (0.83 → 0.80), others PRESENT |
| F-11 | `F-11.patch` (lines 431 and 443) | F-11 ABSENT; through `glucose-get-last` the undated reading → "BG data is too old", no temp (`F-11-patched-tests.txt`) |
| F-12 | `F-12.patch` | F-12 ABSENT (→ 0.9 U/h), others PRESENT |

`basal-set-temp.js` and `round-basal.js` are identical to oref0's, so the F-04 differential check
in `docs/upstream/oref0/F-04-differential.txt` applies to this patch unchanged. oref0's own
mocha tests were not run on the patched copy (see `docs/upstream/oref0/README.md`).

## Contact

No `SECURITY.md`; `.github/ISSUE_TEMPLATE` exists; `CONTRIBUTING.md:35` asks for issues and
pull requests.
