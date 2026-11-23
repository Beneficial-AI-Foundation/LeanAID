#!/usr/bin/env bash
# Branch coverage of oref0's lib/ (vendor/oref0, 0.7.1) from four sources:
#   1. oref0's own mocha tests (tests/*.test.js);
#   2. the differential test of determine-basal (scripts/difftest/run.js, N random cases, seed S);
#   3. the targeted determine-basal cases (scripts/difftest/targeted.js);
#   4. the differential test of IOB, meal history and the basal schedule
#      (scripts/difftest/iob.js, M random cases, seed S, and scripts/difftest/iob-targeted.jsonl).
# Sources 2-4 also compare every case with aid-lean; the script stops if one of them fails.
# Uses istanbul 0.4.5, which oref0 itself declares in its devDependencies.
# Nothing in vendor/ is written: istanbul output goes to scripts/coverage/out/.
# scripts/difftest/run.js and iob.js rewrite docs/difftest.json and docs/iobtest.json; both are
# restored afterwards (the committed ones come from runs without istanbul).
#
#   bash scripts/coverage/run.sh [N=100000] [S=1] [M=10000]
#
# About 50 minutes with the defaults (8 CPUs). M is smaller than N because each IOB case costs
# aid-lean about 0.5 CPU-seconds (exponential curves); the 100,000-case IOB run is done
# without istanbul (docs/iobtest.json).
#
# Then scripts/coverage/report.js writes docs/coverage.json and docs/COVERAGE.md.
set -euo pipefail
N="${1:-100000}"
S="${2:-1}"
M="${3:-10000}"
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="$ROOT/scripts/coverage/out"
ISTANBUL="$ROOT/vendor/oref0/node_modules/.bin/istanbul"
export TZ=UTC

rm -rf "$OUT"
mkdir -p "$OUT"

echo "== oref0's own tests"
( cd "$ROOT/vendor/oref0" && "$ISTANBUL" cover --dir "$OUT/oref0-tests" --report json \
    ./node_modules/mocha/bin/_mocha -- -R dot tests/*.test.js > "$OUT/oref0-tests.log" 2>&1 ) || true
# oref0's suite has known failures (docs/TESTS.md); coverage is still written.
test -f "$OUT/oref0-tests/coverage.json"

echo "== differential test, N=$N seed=$S"
cp "$ROOT/docs/difftest.json" "$OUT/difftest.json.bak"
( cd "$ROOT" && "$ISTANBUL" cover --dir "$OUT/difftest" --report json \
    scripts/difftest/run.js -- "$N" "$S" > "$OUT/difftest.log" 2>&1 )
cp "$OUT/difftest.json.bak" "$ROOT/docs/difftest.json"

echo "== targeted determine-basal cases"
( cd "$ROOT" && "$ISTANBUL" cover --dir "$OUT/targeted" --report json \
    scripts/difftest/targeted.js > "$OUT/targeted.log" 2>&1 )

echo "== IOB differential test, M=$M seed=$S, and the targeted IOB cases"
test -f "$ROOT/docs/iobtest.json" && cp "$ROOT/docs/iobtest.json" "$OUT/iobtest.json.bak"
( cd "$ROOT" && "$ISTANBUL" cover --dir "$OUT/iobtest" --report json \
    scripts/difftest/iob.js -- "$M" "$S" > "$OUT/iobtest.log" 2>&1 )
test -f "$OUT/iobtest.json.bak" && cp "$OUT/iobtest.json.bak" "$ROOT/docs/iobtest.json"
( cd "$ROOT" && "$ISTANBUL" cover --dir "$OUT/iobtest-2" --report json \
    scripts/difftest/iob.js -- --file scripts/difftest/iob-targeted.jsonl > "$OUT/iobtest-2.log" 2>&1 )

node "$ROOT/scripts/coverage/report.js" "$N" "$S" "$M"
