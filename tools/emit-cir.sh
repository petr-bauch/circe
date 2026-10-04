#!/usr/bin/env bash
# Capture raw CIRGen output for the Phase 0 corpus.
# Requires the CIR-enabled build at ~/code/llvm-project-cir/build/bin/clang.
set -euo pipefail
CLANG="${CLANG:-$HOME/code/llvm-project-cir/build/bin/clang}"
# Run from the repo root so the source paths embedded in `loc(...)`
# are root-relative (`tests/c/...`, `tests/cpp/...`), matching the
# checked-in corpus.
cd "$(dirname "$0")/.."
OUTDIR="tests/cir"
mkdir -p "$OUTDIR"
if [[ ! -x "$CLANG" ]]; then
  echo "CIR clang not found at $CLANG (build blocked, see docs/PINS.md)." >&2
  echo "Override with CLANG=/path/to/cir-clang $0" >&2
  exit 2
fi
"$CLANG" --version | head -3
for src in tests/c/*.c; do
  base="$(basename "$src" .c)"
  echo "== $base =="
  # Raw CIRGen: disable the default CIR passes so the captured `.cir`
  # matches CIRGen output byte-for-byte (standardized on
  # `-clangir-disable-passes`, option B).
  "$CLANG" -fclangir -Xclang -emit-cir -Xclang -clangir-disable-passes \
    "$src" -S -o "$OUTDIR/$base.cir"
done
# M2 C++ corpus: same CIRGen capture, plus `-fno-exceptions` (pinned:
# without it, dtor defs carry `cir.try` + `personality` and new/delete
# carries `cleanup eh` regions; with it only `cleanup.scope` /
# `cleanup normal` + `trap` remain — see docs/ROADMAP.md M2).
# Empty until M2a lands (nullglob: no match expands to nothing).
shopt -s nullglob
for src in tests/cpp/*.cpp; do
  base="$(basename "$src" .cpp)"
  echo "== $base =="
  # N4d-iii: `std::span` needs `-std=c++20` (the only C++20 corpus
  # file; every other TU captures with the default std, byte-stable).
  stdflag=""
  case "$base" in span_*) stdflag="-std=c++20";; esac
  "$CLANG" -fclangir -Xclang -emit-cir -Xclang -clangir-disable-passes -fno-exceptions \
    $stdflag "$src" -S -o "$OUTDIR/$base.cir"
done
shopt -u nullglob
echo "Wrote $OUTDIR/*.cir"
