#!/usr/bin/env bash
# Run every UPPAAL query of the abstraction (docs/uppaal-plan.md) and write
# uppaal/queries/results.json. Exits 1 if a result is not the expected one.
#
# Usage: scripts/uppaal.sh [--only ID ...]
# VERIFYTA names the verifyta binary (default: /opt/uppaal/lib/app/bin/verifyta.sh).
set -euo pipefail
cd "$(dirname "$0")/.."
VERIFYTA="${VERIFYTA:-/opt/uppaal/lib/app/bin/verifyta.sh}"
exec python3 -I uppaal/queries/check.py --verifyta "$VERIFYTA" "$@"
