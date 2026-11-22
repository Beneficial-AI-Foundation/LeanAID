#!/bin/bash
# usage: patchtest.sh <target dir under upstream/> <lib path inside target> <evidence dir>
# For each finding: copy lib, apply the fix, write <evidence>/<finding>.patch and
# <evidence>/<finding>-patched-tests.txt. Pristine lib is never modified.
set -e
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
S=$(cd "$(dirname "$0")" && pwd)
T=$1; L=$2; E=$3
cd "$REPO/upstream/$T"
for f in F-04 F-11 F-12; do
  rm -rf "../$T-patched"   # path is upstream/<target>-patched, created here
  mkdir -p "../$T-patched/a" "../$T-patched/b"
  mkdir -p "../$T-patched/a/$(dirname "$L")" "../$T-patched/b/$(dirname "$L")"
  cp -R "$L" "../$T-patched/a/$L"; cp -R "$L" "../$T-patched/b/$L"
  python3 -I "$S/fixes.py" $f "../$T-patched/b/$L" > /dev/null || { echo "$f: fix does not apply"; continue; }
  (cd "../$T-patched" && diff -ru a b > "$REPO/$E/$f.patch" || true)
  {
    echo "# $f fix applied alone to a copy of $T/$L; Part 1 tests on the patched copy"
    node "$REPO/scripts/findings/run.js" "../$T-patched/b/$L" | sed "s#$REPO/upstream/##"
    if [ $f = F-11 ]; then echo "# F-11 through glucose-get-last (patched copy)"; NODE_PATH=$REPO/vendor/oref0/node_modules node "$REPO/scripts/findings/f11-pipeline.js" "../$T-patched/b/$L"; fi
  } > "$REPO/$E/$f-patched-tests.txt"
  grep summary "$REPO/$E/$f-patched-tests.txt" | sed "s/^/$f fix: /"
done
rm -rf "../$T-patched"
