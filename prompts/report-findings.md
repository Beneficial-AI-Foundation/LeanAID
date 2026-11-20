# Reporting the findings: reproduction tests and a survey of oref0's descendants

Goal: prepare everything the maintainer needs to report findings F-04, F-11 and F-12
(see `docs/FINDINGS.md`) to the projects that still ship oref0's dosing logic. You
write tests and drafts; **the maintainer decides what to report and sends it.** Follow
`AGENTS.md`, with the one exception granted below. Never push, never post anything.

The three findings, in short:

- **F-11 (medium)**: a glucose reading with no date has age NaN; `minAgo > 12 || minAgo < -5`
  is false, so the staleness check is skipped and oref0 doses on it (3.5 U/h on the
  documented input, where the same reading dated 60 min ago is refused).
- **F-12 (medium)**: with `max_basal` or `max_daily_basal` missing, `maxSafeBasal` is
  NaN, `rate > maxSafeBasal` is always false, and no cap is applied (5.9 U/h on the
  documented input, 6.6 times the scheduled basal).
- **F-04 (low)**: `setTempBasal` caps to `maxSafeBasal` and then rounds to the pump step,
  which can round up (limit 0.83 → 0.85 U/h; 4.44 → 4.45 U/h in difftest case 28557).

## Exception to AGENTS.md for this task (granted by the maintainer)

- **Read-only** network access to GitHub is allowed: `git clone --depth 1` /
  `git fetch` of public repositories, and unauthenticated `curl` GET requests to
  `https://api.github.com` to list forks and branches. No tokens, no `gh`, no writes of
  any kind (no issues, comments, PRs, stars, forks).
- Put every clone under `upstream/` at the repository root and add `upstream/` to
  `.gitignore` before the first clone.
- You may run the JavaScript of a cloned oref0 descendant under Node **only** to run the
  reproduction tests of Part 1 against its `lib/`. Do not run its install scripts:
  reuse `vendor/oref0/node_modules` (via `NODE_PATH`) or, if a dependency is missing,
  `npm ci --ignore-scripts` with only the packages that project's `package.json`
  declares. Ask the maintainer before running anything else from a clone.
- Do not build Android, iOS or Kotlin/Swift projects. Check those by reading the code.

## Disk space and the rest of the computer

- Work only inside this repository folder. Do not create, change or delete anything
  outside it (no global `npm install`, no files in the home folder, no system caches you
  can avoid; use `npm ci --ignore-scripts --no-audit --no-fund` inside `upstream/` only).
- Download only what the analysis needs. Answering "can the trigger happen in this
  app?" means tracing how the app builds the algorithm's inputs, so the apps are checked
  from their **whole source code**; only history and build outputs are left out:
  - **apps and other projects checked in full** (oref0 `dev`, Trio, iAPS, AndroidAPS,
    and any project they take their oref code from): `git clone --depth 1` (full source,
    no history). Do not build them and do not install their dependencies, except as
    allowed above for running the Part 1 tests on JavaScript.
  - **forks of oref0**: first compare without downloading, using the GitHub API's tree
    hashes (`/repos/<owner>/<repo>/git/trees/<sha>?recursive=1`): if a fork's `lib/` and
    `bin/` trees are identical to 0.7.1, everything about it, including how it builds
    the inputs, is the same as the original, so the original's results apply. Only a
    fork whose `lib/` or `bin/` differs is cloned with `git clone --depth 1` (oref0 is a
    few MB without `node_modules`) and analysed in full like an app.
  - Unauthenticated GitHub API calls are limited to 60 per hour: keep a log of calls,
    prefer `raw.githubusercontent.com` and clones where they do the job, and wait for
    the limit to reset rather than finding ways around it.
- Keep `upstream/` under 2 GB. Check with `du -sh upstream` after each download; if it
  would go over, stop and ask the maintainer.
- Before deleting anything, save what must survive into `docs/`: the commit SHAs, the
  quoted lines, test outputs and each suggested fix as a `.patch` file in
  `docs/upstream/`.
- At the end, delete `upstream/` and nothing else: run `rm -rf ./upstream` from the
  repository root, after checking with `pwd` that you are in this repository. Never use
  `rm -rf` on any other path, and never delete files you did not create in this task.
  Report the space used at the peak and confirm that `upstream/` is gone.

## Part 1: reproduction tests (against the pinned oref0)

1. Write `scripts/findings/` with one Node script per finding (`f04.js`, `f11.js`,
   `f12.js`) and a runner `run.js`. Each script takes the path of an oref0-style `lib/`
   directory as its argument (default `vendor/oref0/lib`) and, for its finding:
   - runs the **trigger** input (the one in `docs/FINDINGS.md`) and the **control**
     input (the same situation without the defect: a dated reading 60 min old; the
     profile with `max_basal` present; a limit on the pump grid, such as 0.85);
   - prints a one-line verdict: `PRESENT` (trigger shows the defect and control behaves
     correctly), `ABSENT` (trigger behaves correctly), or `INCONCLUSIVE` (anything else,
     for example the control also misbehaves or the call throws), with the rates seen;
   - exits 0 for PRESENT, 1 for ABSENT, 2 for INCONCLUSIVE.
2. For F-04 also search, without changing anything, for realistic triggers: list
   `(current_basal, max_basal, max_daily_basal)` combinations with values a user could
   type (two decimals, typical ranges) where `maxSafeBasal` is off the pump grid and the
   issued rate exceeds it. Report how common this is, for example the share of
   `current_basal` values in 0.05–3.00 U/h whose `4 × current_basal` limit rounds up.
3. Run all three against `vendor/oref0/lib`; all three must be PRESENT. Do not edit
   `vendor/`. Add `scripts/findings/run.js` to `scripts/check.sh` only if it needs no
   network and runs in under 10 seconds.
4. Commit: "Findings: reproduction tests against oref0".

## Part 2: which projects still have the findings

1. Build the list of targets and record, for each, the repository URL, branch and the
   exact commit SHA you checked. Start with:
   - `openaps/oref0`: `master` (should match our 0.7.1 pin) and `dev`, and any other
     branch with commits after 0.7.1;
   - the active iOS and Android apps that use oref0's logic: Trio (`nightscout/Trio`
     and the repository its oref JavaScript comes from), iAPS, AndroidAPS
     (`nightscout/AndroidAPS`, which has ported the algorithm to Kotlin), and any
     other you find referenced from these projects' READMEs or docs;
   - forks of `openaps/oref0` from the GitHub API (`/repos/openaps/oref0/forks`,
     paginated, sorted by `pushed_at`), keeping those pushed in the last 3 years. For
     each, compare its `lib/` and `bin/` tree hashes with 0.7.1 through the API (see
     "Disk space"):
     - **identical**: the findings are present by identity (no need to run the tests),
       and the original's answer to "can it happen?" applies; list them with SHA, last push date, stars and whether they look used (releases,
       issues, recent commits elsewhere in the repository);
     - **different**: clone and analyse in full, as in step 2.
   Verify each claim about what a project uses (for example "Trio bundles oref0's JS")
   from its code, not from memory.
2. For each target and finding:
   - **JavaScript targets**: run `scripts/findings/run.js` against the target's `lib/`
     (or bundled JS); record the verdict.
   - **Ported targets** (Kotlin, Swift): find the code that corresponds to the three
     sites (the staleness check, `getMaxSafeBasal` and its use, `setTempBasal`'s cap
     then round) and decide by reading it, quoting the lines with file path and line
     numbers. Mark these verdicts "by inspection".
   - **Can the trigger happen in that app?** Find where the app builds the inputs:
     can a glucose value reach the algorithm without a date? Can `max_basal` or
     `max_daily_basal` be missing or non-numeric (settings migration, empty field,
     JSON parse)? Does the app add its own checks before or after the algorithm (for
     example a pump-side maximum, or a separate stale-data check)? Quote the code. This
     decides whether a finding is a safety bug in practice or defensive hardening.
3. Write `docs/UPSTREAM.md`:
   - a table: target × finding → PRESENT / ABSENT / INCONCLUSIVE (tested or by
     inspection), with commit SHA and links to the lines;
   - for each target, whether each trigger can occur in practice, with evidence;
   - a recommendation per target and finding: report as a safety issue, report as
     hardening, or do not report (fixed already, or unreachable), with the reason;
   - for each project to contact: its preferred channel for safety issues (look for
     `SECURITY.md`, a security contact, or the contributing guide), and whether the
     report should go privately first.
4. Draft the reports in `docs/upstream/<project>-<finding>.md`, one per issue to file,
   only for the combinations recommended in step 3. Each draft: a neutral title; what
   happens; the smallest reproduction (input and observed output, from Part 1); why it
   matters, with honest severity; a suggested fix; credit "found while transcribing
   oref0 into Lean 4 (LeanAID, Beneficial AI Foundation)". Suggested fixes:
   - F-04: after capping, round **down** to the pump step (or round the limit down
     before capping), so the issued rate never exceeds `maxSafeBasal`;
   - F-11: treat a missing or non-numeric reading date as stale (check
     `!(minAgo <= 12 && minAgo >= -5)` rather than `minAgo > 12 || minAgo < -5`);
   - F-12: if `maxSafeBasal` is not a finite positive number, refuse to raise the rate
     (cancel any high temp and report the error) rather than skipping the cap.
   Show each suggested fix as a patch against the target's code, applied **only to a
   copy under `upstream/`**, and run the Part 1 tests on the patched copy: the trigger
   must become ABSENT and oref0's own tests must still pass (`npm test`, with
   `--ignore-scripts` installs only). Never edit `vendor/`.
5. Commit: "Upstream survey and draft reports". Do not push.

## Honesty

- Say exactly which commit of which project each verdict is about, and how you got it
  (tested or by inspection).
- If a target cannot be checked (private, too large, code not found), say so in
  `docs/UPSTREAM.md`; do not guess.
- Severity is our estimate; say what it rests on. Do not overstate: if an app always
  supplies dates and settings, say the finding is defensive hardening there.
- Stop and ask the maintainer if anything requires credentials, running a target's code
  beyond Part 1's tests, or contacting anyone.
