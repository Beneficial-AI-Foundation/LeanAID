#!/usr/bin/env bash
# LeanAID static checks. Fails (exit 1) if:
#   * `sorry` appears in any Lean source;
#   * the core (LeanAID/Core) uses `partial`, `unsafe`, `@[extern]`,
#     `implemented_by`, `native_decide`, `Float`, or imports Mathlib;
#   * any module outside LeanAID/Conformance uses `native_decide`;
#   * any Lean source declares a new `axiom`;
#   * the binary shell or core imports Mathlib;
#   * a headline theorem depends on an axiom other than
#     propext, Classical.choice, Quot.sound.
# It prints `#print axioms` for every theorem listed in scripts/headline.txt.
set -u
cd "$(dirname "$0")/.."
fail=0

lean_files=$(find LeanAID App -name '*.lean' | sort)
core_files=$(find LeanAID/Core -name '*.lean' | sort)
nonconf_files=$(find LeanAID App -name '*.lean' -not -path 'LeanAID/Conformance/*' | sort)

# Strip line comments and block comments before searching, so that the
# documentation may mention the forbidden words.
strip() { perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$1"; }

check() { # $1 = description, $2 = regex, rest = files
  local desc="$1" re="$2"; shift 2
  local f hits
  for f in "$@"; do
    hits=$(strip "$f" | grep -nE "$re" || true)
    if [ -n "$hits" ]; then
      echo "FORBIDDEN ($desc) in $f:"; echo "$hits" | sed 's/^/    /'
      fail=1
    fi
  done
}

check "sorry"            '\bsorry\b'                 $lean_files
check "axiom"            '^\s*(private\s+|protected\s+)?axiom\b' $lean_files
check "native_decide"    '\bnative_decide\b'         $nonconf_files
check "partial"          '\bpartial\b'               $core_files
check "unsafe"           '\bunsafe\b'                $core_files
check "extern"           '@\[\s*extern'              $core_files
check "implemented_by"   '\bimplemented_by\b'        $core_files
check "Float"            '\bFloat(32)?\b'            $core_files
check "Mathlib import"   '^\s*import\s+Mathlib'      $core_files $(find App -name '*.lean')

if [ $fail -ne 0 ]; then
  echo "check.sh: forbidden constructs found"; exit 1
fi
echo "check.sh: no forbidden constructs in $(echo "$lean_files" | wc -l | tr -d ' ') Lean files"

# Axioms of headline theorems
if [ -s scripts/headline.txt ]; then
  tmp=$(mktemp -t leanaid-axioms).lean
  {
    echo "import LeanAID"
    grep -vE '^\s*(#|$)' scripts/headline.txt | while read -r thm; do echo "#print axioms $thm"; done
  } > "$tmp"
  out=$(lake env lean "$tmp" 2>&1); rc=$?
  rm -f "$tmp"
  echo "$out"
  if [ $rc -ne 0 ]; then echo "check.sh: could not print axioms"; exit 1; fi
  bad=$(echo "$out" | grep -oE "\[[^]]*\]" | tr -d '[]' | tr ',' '\n' | sed 's/^ *//' \
        | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' | grep -v '^$' || true)
  if [ -n "$bad" ]; then
    echo "check.sh: headline theorems depend on unexpected axioms: $bad"; exit 1
  fi
  n=$(grep -cvE '^\s*(#|$)' scripts/headline.txt)
  echo "check.sh: $n headline theorems use only propext, Classical.choice, Quot.sound"
fi
echo "check.sh: OK"
