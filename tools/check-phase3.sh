#!/usr/bin/env bash
# Phase 3 end-to-end check: build, regenerate, goldens, typecheck, differential test.
# Usage: tools/check-phase3.sh [trials]
set -euo pipefail
cd "$(dirname "$0")/.."

TRIALS="${1:-1000}"
WORKDIR="/tmp/opencode"
mkdir -p "$WORKDIR"
ADD_BIN="$WORKDIR/circe_add_native"
INCR_BIN="$WORKDIR/circe_incr_native"

echo "== lake build =="
lake build

echo "== regenerate out/ =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (lake does not track include_str deps) =="
diff -u tests/golden/Add.lean out/Add.lean
diff -u tests/golden/Incr.lean out/Incr.lean
echo "goldens in sync"

echo "== typecheck emitted files =="
lake env lean out/Add.lean
lake env lean out/Incr.lean
echo "emitted files typecheck"

echo "== native drivers =="
cc -O0 -Wall tests/c/add.c tests/diff/driver_add.c -o "$ADD_BIN"
cc -O0 -Wall tests/c/incr_ptr.c tests/diff/driver_incr.c -o "$INCR_BIN"

echo "== differential test (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffPhase3.lean "$ADD_BIN" "$INCR_BIN" "$TRIALS"

echo "PHASE3-OK"
