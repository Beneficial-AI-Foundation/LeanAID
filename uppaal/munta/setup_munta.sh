#!/usr/bin/env bash
# Set up Munta for U0b in vendor/ (ignored by git).
#
# The script downloads Isabelle2020 and the AFP release afp-2021-02-01, and checks
# their SHA-256 sums. It clones Munta at the pinned commit and builds the `muntax`
# checker from the SML code in the Munta repository with the Poly/ML compiler of
# Isabelle2020. MLton is not used. With --regenerate, it also builds the Isabelle
# session TA_Code, which writes the SML code again from the proofs. That build
# takes hours.
#
# Usage: uppaal/munta/setup_munta.sh [--regenerate]
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
V="$ROOT/vendor"
MUNTA_COMMIT=62cb1a4a4dbcfcf62c365e90faba15b0012d5a12
ISA_URL=https://isabelle.in.tum.de/website-Isabelle2020/dist/Isabelle2020_linux.tar.gz
ISA_SHA=633aff864d6647bd175cf831e7513e3fd0cd06beacbf29a5c6c66d4de1522bae
AFP_URL=https://isa-afp.org/release/afp-2021-02-01.tar.gz
AFP_SHA=501bc33b7bbbd6ec8acfe3639ebb331bcb3b7dbc03c5864510fd1a32087b277d

fetch() {  # url sha dest
  if [ ! -f "$3" ]; then mkdir -p "$(dirname "$3")"; curl -sSL -o "$3" "$1"; fi
  echo "$2  $3" | sha256sum -c --quiet -
}

fetch "$ISA_URL" "$ISA_SHA" "$V/dl/isabelle/Isabelle2020_linux.tar.gz"
fetch "$AFP_URL" "$AFP_SHA" "$V/dl/afp/afp-2021-02-01.tar.gz"
[ -d "$V/Isabelle2020" ] || tar -xzf "$V/dl/isabelle/Isabelle2020_linux.tar.gz" -C "$V"
[ -d "$V/afp-2021-02-01" ] || tar -xzf "$V/dl/afp/afp-2021-02-01.tar.gz" -C "$V"
[ -d "$V/munta" ] || git clone -q https://github.com/wimmers/munta.git "$V/munta"
git -C "$V/munta" checkout -q "$MUNTA_COMMIT"

# Build the checker with Poly/ML. The bundled library is not position independent,
# so the link step gets -no-pie.
P="$V/Isabelle2020/contrib/polyml-5.8.1-20200228/x86_64-linux"
B="$V/munta-build"
rm -rf "$B" && mkdir -p "$B"
git -C "$V/munta" archive "$MUNTA_COMMIT" ML | tar -x -C "$B"
sed -e 's/^EXTRALDFLAGS=""/EXTRALDFLAGS="-no-pie"/' -e "s|^prefix=.*|prefix=\"$P\"|" \
  "$P/polyc" > "$B/polyc-nopie"
chmod +x "$B/polyc-nopie"
( cd "$B" && MUNTA_ML="$B/ML" LD_LIBRARY_PATH="$P" ./polyc-nopie -o munta \
    "$ROOT/uppaal/munta/munta_poly_build.sml" > build.log 2>&1 )
printf '#!/bin/sh\nLD_LIBRARY_PATH=%s exec %s/munta "$@"\n' "$P" "$B" > "$B/munta.sh"
chmod +x "$B/munta.sh"
echo "checker: $B/munta.sh"

if [ "${1:-}" = "--regenerate" ]; then
  # Isabelle2020 gets its own home directory, apart from any other Isabelle.
  mkdir -p "$V/isabelle-home" "$V/munta/OCaml"
  # The session TA_Code ends with ML_val tests that read benchmark files from the
  # author's machine (/Users/wimmers/...). They fail after the code export, so the
  # build exits with 2. Any other error stops this script.
  LOG="$V/isabelle-ta-code.log"
  touch "$LOG.start"
  ( cd "$V/munta" && HOME="$V/isabelle-home" ../Isabelle2020/bin/isabelle build -v \
      -j 3 -o threads=6 -d ../afp-2021-02-01/thys -d . TA_Code ) > "$LOG" 2>&1 || true
  if grep '^\*\*\* ' "$LOG" | grep -v -E 'exception Io|TextIO.openIn|/Users/wimmers|At command "ML_val"|line 284 of'; then
    echo "TA_Code: errors other than the author-local benchmark tests" >&2; exit 1
  fi
  if [ ! "$V/munta/ML/Simple_Model_Checker.sml" -nt "$LOG.start" ]; then
    echo "TA_Code did not write ML/Simple_Model_Checker.sml" >&2; exit 1
  fi
  if git -C "$V/munta" diff --quiet -- ML/Simple_Model_Checker.sml; then
    echo "regenerated ML/Simple_Model_Checker.sml is identical to the pinned commit"
  else
    echo "regenerated ML/Simple_Model_Checker.sml differs from the pinned commit" >&2; exit 1
  fi
fi
