#!/usr/bin/env bash
# Build a diagnostic copy of the Munta checker that prints the order in which Munta
# numbers the state variables (work item U4).
#
# Munta accepts only one order of the variable declarations (uppaal/munta/compat/README.md,
# "Input limits"): its precondition "Bounds first index" needs the declared bounds in
# the order of the variable numbers that `make_renaming` gives. This copy prints that
# order ("Var order: ...") right after `make_renaming`, before the check. It is used
# only to find the order. Every answer comes from the unpatched checker of
# uppaal/munta/setup_munta.sh.
#
# Usage: uppaal/munta/munta_order.sh   (after uppaal/munta/setup_munta.sh)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
V="$ROOT/vendor"
P="$V/Isabelle2020/contrib/polyml-5.8.1-20200228/x86_64-linux"
B="$V/munta-order"
rm -rf "$B" && mkdir -p "$B"
cp -r "$V/munta-build/ML" "$B/ML"
cp "$V/munta-build/polyc-nopie" "$B/polyc-nopie"
python3 -I - "$B/ML/Simple_Model_Checker.sml" <<'EOF'
import sys
p = sys.argv[1]
s = open(p).read()
old = '''               val _ = writeln "Renaming";'''
new = '''               val _ = writeln ("Var order: " ^ String.concatWith " "
                 (List.tabulate (List.length bounds,
                   fn i => inv_renum_vars (nat_of_integer (IntInf.fromInt i)))));
               val _ = writeln "Renaming";'''
assert s.count(old) == 1, "patch point not found"
open(p, "w").write(s.replace(old, new))
EOF
( cd "$B" && MUNTA_ML="$B/ML" LD_LIBRARY_PATH="$P" ./polyc-nopie -o munta \
    "$ROOT/uppaal/munta/munta_poly_build.sml" > build.log 2>&1 )
printf '#!/bin/sh\nLD_LIBRARY_PATH=%s exec %s/munta "$@"\n' "$P" "$B" > "$B/munta.sh"
chmod +x "$B/munta.sh"
echo "order printer: $B/munta.sh"
