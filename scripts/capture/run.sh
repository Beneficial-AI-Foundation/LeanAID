#!/usr/bin/env bash
# Run oref0's in-scope test files under the capture hook (TZ=UTC, fixed clock).
# Output: scripts/capture/out/<name>.json
set -euo pipefail
cd "$(dirname "$0")/../../vendor/oref0"
for t in determine-basal iob set-temp-basal basal get-last-glucose cobhistory; do
  CAPTURE_NAME=$t TZ=UTC node -r ../../scripts/capture/fixclock.js ./node_modules/.bin/_mocha \
    --require ../../scripts/capture/hook.js -R dot ../../scripts/capture/roothooks.js "tests/$t.test.js" 2>/dev/null | tail -3
done
