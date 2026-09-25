#!/usr/bin/env bash
# Phase 4 end-to-end check: build, regenerate, goldens, typecheck,
# differential tests (add/incr + choose/sum), golden pipeline + rejections.
# Usage: tools/check-phase4.sh [trials]
set -euo pipefail
cd "$(dirname "$0")/.."

TRIALS="${1:-1000}"
WORKDIR="/tmp/opencode"
mkdir -p "$WORKDIR"
ADD_BIN="$WORKDIR/circe_add_native"
INCR_BIN="$WORKDIR/circe_incr_native"
CHOOSE_BIN="$WORKDIR/circe_choose_native"
SUM_BIN="$WORKDIR/circe_sum_native"

echo "== lake build =="
lake build

echo "== regenerate out/ =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (lake does not track include_str deps) =="
diff -u tests/golden/Add.lean out/Add.lean
diff -u tests/golden/Incr.lean out/Incr.lean
diff -u tests/golden/Choose.lean out/Choose.lean
diff -u tests/golden/SumArray.lean out/SumArray.lean
echo "goldens in sync"

echo "== typecheck emitted files =="
lake env lean out/Add.lean
lake env lean out/Incr.lean
lake env lean out/Choose.lean
lake env lean out/SumArray.lean
echo "emitted files typecheck"

echo "== native drivers =="
cc -O0 -Wall tests/c/add.c tests/diff/driver_add.c -o "$ADD_BIN"
cc -O0 -Wall tests/c/incr_ptr.c tests/diff/driver_incr.c -o "$INCR_BIN"
cc -O0 -Wall tests/c/choose_ptr.c tests/diff/driver_choose.c -o "$CHOOSE_BIN"
cc -O0 -Wall tests/c/sum_array.c tests/diff/driver_sum.c -o "$SUM_BIN"

echo "== differential test add/incr (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffPhase3.lean "$ADD_BIN" "$INCR_BIN" "$TRIALS"

echo "== differential test choose/sum (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffPhase4.lean "$CHOOSE_BIN" "$SUM_BIN" "$TRIALS"

echo "== golden pipeline + rejection suite =="
lake env lean --run tests/lean/GoldenPhase4.lean

echo "PHASE4-OK"
