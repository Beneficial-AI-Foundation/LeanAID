# Upstream survey helpers (docs/UPSTREAM.md)

Kept as the record of how the evidence in `docs/upstream/` was produced.

- `gh.sh <api path> <out>`: one unauthenticated GET to api.github.com, logged in `docs/upstream/api-calls.log`.
- `fixes.py <F-04|F-11|F-12> <lib dir>`: the suggested fixes as text replacements on an oref0-style `lib/`.
  (The F-11 rewrite was generalised during the survey; the `F-11.patch` files of openaps/oref0 and
  trio-oref come from the first version, which also added a comment line. Same logic.)
- `fixes_iaps_bundle.py`, `fixes_freeaps_bundle.py`: the same fixes in the minified names of the iAPS
  and FreeAPS X bundles.
- `patchtest.sh <target under upstream/> <lib path> <evidence dir>`: applies each fix alone to a copy
  and runs `scripts/findings/run.js` on it; writes `F-xx.patch` and `F-xx-patched-tests.txt`.
- `fork.sh <owner/repo> <branch> <commit>`: clone one fork into `upstream/`, compare with 0.7.1, test,
  patch, save to `docs/upstream/forks/<owner>-<repo>/`, delete the clone.

They write only inside the repository (`upstream/`, `docs/upstream/`). Only `rm -rf ./upstream/<name>`
is used for deletion.
