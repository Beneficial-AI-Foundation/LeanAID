# ivalkou/freeaps (FreeAPS X): evidence

Repository: https://github.com/ivalkou/freeaps (referenced from the Trio and iAPS READMEs as their
origin; checked 2026-11-22; `git clone --depth 1`, 43 MB, then `git fetch --depth 1 origin dev`).
Not archived; `pushed_at` 2026-02-08 (one API call), but:

- `master` (default) = `3a2908c5cf664b5cb1fed2e63aadc89a3bd81761`, last commit 2022-06-11;
- `dev` = `360a3b881318419213b50a861f60d4fac601f947`, last commit 2023-11-18; no changes in the JS
  or in the Swift files quoted here relative to master.

So the algorithm code has not changed since 2022; iAPS and Trio are its maintained successors.

## Verdicts (tested on the bundles; `tests-master.txt`)

Same structure as iAPS: minified bundles in `FreeAPS/Resources/javascript/bundle/` run in
JavaScriptCore via `prepare/determine-basal.js`; loaded with `scripts/findings/make-bundle-lib.js`.

| finding | verdict | rates |
|---|---|---|
| F-04 | **PRESENT** (tested) | 0.83 → 0.85 U/h |
| F-11 | **PRESENT** (tested) | undated → 3.5 U/h; dated 60 min ago → no temp. The determine-basal bundle has oref0's full check `v>12||v<-5` (twice). |
| F-12 | **PRESENT** (tested) | → 5.9 U/h; control 3.5 |

## Can the triggers happen?

- F-11: no. FreeAPS X's own `glucose-get-last` bundle throws on an undated newest reading
  (`then.dateString` of undefined, `tests-master.txt`), so nothing is dosed; and on the Swift side
  `BloodGlucose.date: Decimal` / `dateString: Date` are non-optional (`BloodGlucose.swift:26-27`) and
  `APSManager.swift:245-247` stops the loop when glucose is older than 12 min.
- F-12: `PumpSettings.maxBasal: Decimal` is non-optional; the closed loop enacts the rate without an
  app-side cap (`APSManager.swift`, `enactSuggested`, quoted). Same picture as iAPS without the
  middleware path being checked here.
- F-04: as iAPS (typed Max Basal; not re-checked in this older code).

## Fixes

Bundle versions with this build's minified names (`F-xx-bundle.patch`), each applied alone to a copy:
F-04 → ABSENT, F-11 → ABSENT, F-12 → ABSENT, the other two still PRESENT (`F-xx-patched-tests.txt`).

## Recommendation input

Unmaintained since 2022 (master) / 2023 (dev), superseded by iAPS and Trio. Contact, if any:
GitHub Issues (`README.md:54`), Telegram groups (`README.md:87-88`); no `SECURITY.md`.
