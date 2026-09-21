#!/usr/bin/env bash
# Capture raw CIRGen output for the Phase 0 corpus.
# Requires the CIR-enabled build at ~/code/llvm-project-cir/build/bin/clang.
set -euo pipefail
CLANG="${CLANG:-$HOME/code/llvm-project-cir/build/bin/clang}"
OUTDIR="$(dirname "$0")/../tests/cir"
mkdir -p "$OUTDIR"
if [[ ! -x "$CLANG" ]]; then
  echo "CIR clang not found at $CLANG (build blocked, see docs/PINS.md)." >&2
  echo "Override with CLANG=/path/to/cir-clang $0" >&2
  exit 2
fi
"$CLANG" --version | head -3
for src in "$(dirname "$0")/../tests/c/"*.c; do
  base="$(basename "$src" .c)"
  echo "== $base =="
  # NOTE: -fclangir-disable-passes only exists on newer SHAs; plain -emit-cir
  # gives raw CIRGen-equivalent output on the Jan-2025 pin.
  "$CLANG" -fclangir -Xclang -emit-cir \
    "$src" -S -o "$OUTDIR/$base.cir"
done
echo "Wrote $OUTDIR/*.cir"
