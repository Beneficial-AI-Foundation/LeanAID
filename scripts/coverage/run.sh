#!/usr/bin/env bash
# Branch coverage of oref0's lib/ (vendor/oref0, 0.7.1) from two sources:
#   1. oref0's own mocha tests (tests/*.test.js);
#   2. our differential test (scripts/difftest/run.js, N random cases, seed S).
# Uses istanbul 0.4.5, which oref0 itself declares in its devDependencies.
# Nothing in vendor/ is written: istanbul output goes to scripts/coverage/out/.
# scripts/difftest/run.js rewrites docs/difftest.json; it is restored afterwards.
#
#   bash scripts/coverage/run.sh [N=100000] [S=1]      (about 10 minutes for N=100000)
#
# Then scripts/coverage/report.js writes docs/coverage.json and docs/COVERAGE.md.
set -euo pipefail
N="${1:-100000}"
S="${2:-1}"
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

node "$ROOT/scripts/coverage/report.js" "$N" "$S"
