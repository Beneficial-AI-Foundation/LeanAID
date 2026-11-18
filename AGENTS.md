# Rules for agents working in this repository

These rules apply to every agent session in LeanAID. The task itself is in
`prompts/kickoff.md`.

## Git and GitHub

- Work only inside this folder.
- Commit locally after each milestone, with a clear message. Do not add any
  `Co-Authored-By` line or other AI attribution to commit messages.
- **Never push.** Do not run `git push`, `gh`, or anything else that sends data to
  GitHub. The maintainer reviews and pushes.
- Never rewrite history that already exists (no `git rebase`, `git reset --hard`,
  `git push --force`, or amending commits you did not just make).

## Honesty

- Never claim something is proved unless `lake build` checks it with no `sorry`.
- Never weaken a theorem statement to make a proof go through without recording
  it in `docs/FINDINGS.md` and `docs/LOG.md`.
- Never edit oref0's sources or tests in `vendor/` to make the Lean code agree.
- The project page (`site/index.html`) may only state results that the build and
  test scripts actually produce. Mark anything else as planned.

## Safety

- This is a research artifact. Nothing here may be presented as fit for dosing
  insulin.
- Do not download or run code other than: the pinned oref0 checkout, Lean and its
  libraries via `lake`, npm packages oref0 itself declares, and the Python
  packages named in the kickoff prompt.
