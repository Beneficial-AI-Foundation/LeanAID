#!/usr/bin/env bash
# Applies the LeanAID fixes (docs/FIXED.md) to a COPY of the pinned oref0. vendor/ is never
# changed. Makes, in the gitignored folder scripts/fixes/out/:
#   oref0/        a copy of vendor/oref0 (without .git), unpatched
#   oref0-fixed/  the same copy with F-04, F-11, F-12, F-23 and F-24 applied, in that order
# and checks that each patch also applies alone to the unpatched copy.
# Usage: bash scripts/fixes/apply.sh
# RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
set -euo pipefail
cd "$(dirname "$0")/../.."
SRC=vendor/oref0
OUT=scripts/fixes/out
FIXES="F-04 F-11 F-12 F-23 F-24"
[ -d "$SRC/lib" ] || { echo "apply.sh: $SRC missing"; exit 1; }
rm -rf "$OUT/oref0" "$OUT/oref0-fixed"
mkdir -p "$OUT"
rsync -a --exclude .git "$SRC/" "$OUT/oref0/"
rsync -a --exclude .git "$SRC/" "$OUT/oref0-fixed/"
for f in $FIXES; do
  patch -s -p1 --dry-run -d "$OUT/oref0" < "scripts/fixes/$f.patch" \
    || { echo "apply.sh: $f.patch does not apply alone"; exit 1; }
  echo "apply.sh: $f.patch applies alone"
done
for f in $FIXES; do
  patch -s -p1 -d "$OUT/oref0-fixed" < "scripts/fixes/$f.patch" \
    || { echo "apply.sh: $f.patch does not apply after the others"; exit 1; }
done
find "$OUT/oref0-fixed" -name '*.orig' -delete
echo "apply.sh: $OUT/oref0-fixed has $FIXES"
n=$( (diff -ru "$OUT/oref0/lib" "$OUT/oref0-fixed/lib" || true) | grep -c '^[+-][^+-]' || true)
echo "apply.sh: $n lines added or removed in lib/"
