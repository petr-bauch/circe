#!/usr/bin/env bash
# Circe end-to-end check (single entry point; S0 rename of check-phase7.sh).
# Usage: tools/check.sh [trials]
# 1. Delegates to tools/check-phase7.sh (build, regenerate, goldens,
#    typecheck, add/incr + choose/sum fuzzers, golden/rejection suites,
#    heap fragment, specs transfer).
# 2. Regenerates + diffs the S1 caller goldens, typechecks the emitted
#    files, builds the native caller drivers, runs the call differential
#    fuzzer, and runs the call golden pipeline + rejection suite.
# 3. Regenerates + diffs the S2 struct golden, typechecks the emitted
#    file, builds the native struct driver, runs the struct differential
#    fuzzer, and runs the struct golden pipeline + rejection suite.
# 4. Asserts the emitted bodies the S1/S2 proofs reason about are exactly
#    the golden-pinned text.
# Mismatch policy: any in-subset C -> Lean divergence is P0; everything
# out of subset must reject loudly (never silently model memory).
set -euo pipefail
cd "$(dirname "$0")/.."

TRIALS="${1:-1000}"
WORKDIR="/tmp/opencode"
mkdir -p "$WORKDIR"
ADD_CALLER_BIN="$WORKDIR/circe_add_caller_native"
SUM_CALLER_BIN="$WORKDIR/circe_sum_caller_native"
STRUCT_BIN="$WORKDIR/circe_struct_native"

tools/check-phase7.sh "$TRIALS"

echo "== regenerate out/ (S1 callers) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (S1 callers) =="
diff -u tests/golden/AddCaller.lean out/AddCaller.lean
diff -u tests/golden/SumCaller.lean out/SumCaller.lean
echo "caller goldens in sync"

echo "== typecheck emitted caller files =="
lake env lean out/AddCaller.lean
lake env lean out/SumCaller.lean
echo "emitted caller files typecheck"

echo "== native caller drivers =="
cc -O0 -Wall tests/c/add.c tests/c/add_caller.c tests/diff/driver_add_caller.c -o "$ADD_CALLER_BIN"
cc -O0 -Wall tests/c/sum_array.c tests/c/sum_caller.c tests/diff/driver_sum_caller.c -o "$SUM_CALLER_BIN"

echo "== differential test callers (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffCalls.lean "$ADD_CALLER_BIN" "$SUM_CALLER_BIN" "$TRIALS"

echo "== golden pipeline + call rejection suite =="
lake env lean --run tests/lean/GoldenCalls.lean

echo "== emitted-body correspondence (S1 emit_correct transfer) =="
grep -qF "checkedAddI32 x y" out/AddCaller.lean
grep -qF "checkedAddI32 t z" out/AddCaller.lean
grep -qF "prefixSumU32 a.val a.val.length" out/SumCaller.lean
echo "emitted caller bodies match Emit assumptions"

echo "== regenerate out/ (S2 struct) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (S2 struct) =="
diff -u tests/golden/StructByValue.lean out/StructByValue.lean
echo "struct golden in sync"

echo "== typecheck emitted struct file =="
lake env lean out/StructByValue.lean
echo "emitted struct file typechecks"

echo "== native struct driver =="
cc -O0 -Wall tests/c/struct_by_value.c tests/diff/driver_struct.c -o "$STRUCT_BIN"

echo "== differential test struct (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffStruct.lean "$STRUCT_BIN" "$TRIALS"

echo "== golden pipeline + struct rejection suite =="
lake env lean --run tests/lean/GoldenStruct.lean

echo "== emitted-body correspondence (S2 emit_correct transfer) =="
grep -qF "pointTranslate p dx dy" out/StructByValue.lean
echo "emitted struct body matches Emit assumptions"

echo "CHECK-OK"
