#!/usr/bin/env bash
# Phase 7 end-to-end check: Phase 5 pipeline + heap (`vec_alloc`) fragment.
# Usage: tools/check-phase7.sh [trials]
# 1. Delegates to tools/check-phase5.sh (build, regenerate, goldens,
#    typecheck, add/incr + choose/sum fuzzers, golden/rejection suites,
#    specs transfer).
# 2. Regenerates + diffs the vec golden, typechecks the emitted file,
#    builds the native vec driver, runs the vec differential fuzzer,
#    and runs the Phase 7 golden pipeline + heap rejection suite.
# 3. Asserts the emitted body the Phase 7 spec reasons about is exactly
#    the golden-pinned text, and typechecks the specs module.
# Mismatch policy: any in-subset C -> Lean divergence is P0; everything
# out of subset must reject loudly (never silently model memory).
set -euo pipefail
cd "$(dirname "$0")/.."

TRIALS="${1:-1000}"
WORKDIR="/tmp/opencode"
mkdir -p "$WORKDIR"
VEC_BIN="$WORKDIR/circe_vec_native"

tools/check-phase5.sh "$TRIALS"

echo "== regenerate out/ (vec) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (vec) =="
diff -u tests/golden/VecAlloc.lean out/VecAlloc.lean
echo "vec golden in sync"

echo "== typecheck emitted vec file =="
lake env lean out/VecAlloc.lean
echo "emitted vec file typechecks"

echo "== native vec driver =="
cc -O0 -Wall tests/c/vec_alloc.c tests/diff/driver_vec.c -o "$VEC_BIN"

echo "== differential test vec_alloc (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffVec.lean "$VEC_BIN" "$TRIALS"

echo "== golden pipeline + heap rejection suite =="
lake env lean --run tests/lean/GoldenPhase7.lean

echo "== emitted-body correspondence (vec Spec transfer) =="
grep -qF "vecFillSumU32 n.toNat" out/VecAlloc.lean
echo "emitted vec body matches Specs assumptions"

echo "== specs typecheck (vec) =="
grep -q "theorem vec_correct" Circe/Specs.lean
lake env lean Circe/Specs.lean
echo "specs typecheck"

echo "PHASE7-OK"
