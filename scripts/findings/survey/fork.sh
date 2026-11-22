#!/bin/bash
# usage: fork.sh <owner/repo> <branch> <expected commit>
# Clone one fork, analyse, save evidence in docs/upstream/forks/<owner>-<repo>/, delete clone.
set -u
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
S=$(cd "$(dirname "$0")" && pwd)
cd "$REPO" || exit 1
[ "$(pwd)" = "$REPO" ] || exit 1
N=$1; B=$2; C=$3
T=fork-$(echo $N | tr / -)
E=docs/upstream/forks/$(echo $N | tr / -)
mkdir -p $E
rm -rf ./upstream/$T ./upstream/$T-patched
git clone -q --depth 1 --branch $B https://github.com/$N.git upstream/$T || { echo "clone failed"; exit 1; }
GOT=$(git -C upstream/$T rev-parse HEAD)
SIZE=$(du -sh upstream/$T | cut -f1)
{
  echo "# https://github.com/$N branch $B @ $GOT (expected $C) — clone size $SIZE"
  echo "# last commit: $(git -C upstream/$T log -1 --format='%ci %an: %s')"
  echo
  echo "## lib/ and bin/ compared with oref0 0.7.1 (vendor/oref0)"
  git diff --no-index --stat=200 vendor/oref0/lib upstream/$T/lib | tail -40
  git diff --no-index --stat=200 vendor/oref0/bin upstream/$T/bin | tail -20
  echo
  echo "## input-path files (same = identical to 0.7.1)"
  for f in lib/basal-set-temp.js lib/round-basal.js lib/glucose-get-last.js lib/profile/basal.js lib/profile/index.js lib/determine-basal/determine-basal.js bin/oref0-determine-basal.js bin/oref0-get-profile.js bin/oref0-pump-loop.sh; do
    if [ ! -e upstream/$T/$f ]; then echo "missing $f"; elif cmp -s vendor/oref0/$f upstream/$T/$f; then echo "same    $f"; else echo "DIFFERS $f"; fi
  done
  echo "tooflat early exit present: $(grep -c 'else if ( tooflat )' upstream/$T/lib/determine-basal/determine-basal.js) / staleness checks 'minAgo > 12 || minAgo < -5': $(grep -c 'minAgo > 12 || minAgo < -5' upstream/$T/lib/determine-basal/determine-basal.js)"
  echo "valid_settings checks maxBolus only: $(grep -A3 'function valid_settings' upstream/$T/bin/oref0-pump-loop.sh 2>/dev/null | grep -c maxBolus)"
} > $E/compare.txt 2>&1
{ node scripts/findings/run.js upstream/$T/lib | sed "s#$REPO/##"; echo "# F-11 through this fork's glucose-get-last"; NODE_PATH=$REPO/vendor/oref0/node_modules node scripts/findings/f11-pipeline.js upstream/$T/lib 2>&1 | cut -c1-220; } > $E/tests.txt 2>&1
SUM=$(grep '^summary' $E/tests.txt)
echo "$N @ ${GOT:0:7} size $SIZE $SUM"
if echo "$SUM" | grep -q PRESENT; then
  bash $S/patchtest.sh $T lib $E 2>&1 | sed 's/^/  /'
fi
rm -rf ./upstream/$T ./upstream/$T-patched
