#!/bin/bash
# usage: gh.sh <api path> <outfile> ; unauthenticated GET, logged
LOG=$(cd "$(dirname "$0")/../../.." && pwd)/docs/upstream/api-calls.log
url="https://api.github.com$1"
code=$(curl -sS -o "$2" -D "$2.hdr" -w '%{http_code}' -H 'Accept: application/vnd.github+json' -H 'User-Agent: leanaid-survey' "$url")
rem=$(grep -i '^x-ratelimit-remaining' "$2.hdr" | tr -d '\r' | awk '{print $2}')
echo "$(date -u +%FT%TZ) GET $1 -> $code (remaining $rem)" >> $LOG
echo "$code remaining=$rem"
