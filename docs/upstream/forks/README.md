# Forks of openaps/oref0

Checked 2026-11-22. 397 direct forks listed through the API; 47 pushed since 2023-11-22. For each of
those 47, the default branch's `lib/` and `bin/` tree hashes were compared with 0.7.1 through the API
(`forks-compared.json`, call log in `../api-calls.log`).

- **36 identical** to 0.7.1: findings present by identity; listed in `identical.md` with commit,
  last push, stars, issues and refs. 33 of them have exactly 0.7.1 (commit `88cf032`) as default
  branch. None has stars; two have open issues (`austinjamesigwe` 2, `thomasvargiu` 1). None
  looks like an independently used product.
- **11 different**: cloned one at a time (`git clone --depth 1` of the default branch, 2.4–14 MB
  each), tested, and deleted. `jpcunningh`, `yp1ripe`, `Foxy7` and `tim2000s` have the same
  commit (`acb0150`, "0.7.0", oref0's 0.7.0 release) and identical trees, so one clone
  (`jpcunningh-oref0/`) covers all four.

## The 11 different forks (tested; one folder each with `compare.txt`, `tests.txt`, patches)

| fork (branch @ commit) | last commit | F-04 | F-11 | F-12 | undated newest reading through the fork's own `glucose-get-last` |
|---|---|---|---|---|---|
| Artificial-Pancreas/oref0 (`iaps` @ `10bdfe3`) | 2026-08-25 | PRESENT | PRESENT | PRESENT | **dosed, 3.5 U/h** (no flat-CGM exit; staleness check is `minAgo > 12` only) |
| KarmenM18/oref0 (`master` @ `3d43fe5`) | 2026-05-07 | PRESENT | PRESENT | PRESENT | refused (flat-CGM check) |
| vanzaam/oref0 (`master` @ `51dd608`) | 2025-10-10 | PRESENT | PRESENT | PRESENT | refused (flat-CGM check) |
| jamescurneen/oref0 (`master` @ `36b5aa9`) | 2023-12-12 | PRESENT | PRESENT | PRESENT | refused (flat-CGM check) |
| bjornoleh/oref0 (`bo` @ `b32929e`) | 2023-01-11 | PRESENT | PRESENT | PRESENT | refused (flat-CGM check) |
| jpcunningh, yp1ripe, Foxy7, tim2000s/oref0 (`master` @ `acb0150`, 0.7.0) | 2019-11-09 | PRESENT | PRESENT | PRESENT | `glucose-get-last` throws (`then.dateString` of undefined): no dosing |
| cluckj/oref0 (`master` @ `4d33c29`) | 2019-04-12 | PRESENT | PRESENT | PRESENT | throws: no dosing |
| N3FM/oref0 (`master` @ `aab29ed`) | 2018-06-20 | PRESENT | PRESENT | PRESENT | throws: no dosing |

Full SHAs are in each folder's `compare.txt`. "Last commit" is the default branch's; a fork's
`pushed_at` can be later (pushes to other branches). The F-04/F-11/F-12 fixes (same as for
openaps/oref0; the F-11 rewrite also covers the `minAgo > 12`-only form) were applied alone to a
copy of each fork's `lib/`: in every fork the fixed finding became ABSENT and the other two
stayed PRESENT (`F-xx-patched-tests.txt`, `F-xx.patch`).

N3FM (2018) ignores `determine_basal`'s `currentTime` argument and uses the system clock; the test
harness therefore uses the current time (to the minute) as its decision time.

## Which of these matter

- **Artificial-Pancreas/oref0 `iaps`** is almost certainly the source of iAPS's bundles: the
  organisation is iAPS's, the branch is `iaps`, the last commit is "backport upstream changes
  2026 08", and the code has the same staleness condition as the iAPS bundle
  (`bg <= 10 || bg === 38 || noise >= 3 || minAgo > 12`, minified `v<=10||38===v||_>=3||f>12`).
  Not compared byte for byte with the bundles. Reports for iAPS should go here/with iAPS.
- The others are personal forks with at most 1 star and no sign of distribution (`identical.md`,
  `compare.txt`). A rig built from them behaves like an oref0 rig for "can it happen"
  (pump-read `max_basal`; their `bin/oref0-pump-loop.sh` differs from 0.7.1's and was not read
  in detail; N3FM's and cluckj's older loop has no `valid_settings` with a `maxBolus` check).
  Not recommended as report targets.
