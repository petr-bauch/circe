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
# 5. Regenerates + diffs the S3a control-flow goldens, typechecks the
#    emitted files, builds the native control-flow drivers, runs the
#    control-flow differential fuzzer, and runs the control-flow golden
#    pipeline + rejection suite.
# 6. Asserts the emitted bodies the S3a proofs reason about are exactly
#    the golden-pinned text.
# 7. Regenerates + diffs the S3b 64-bit goldens, typechecks the emitted
#    files, builds the native 64-bit drivers, runs the 64-bit
#    differential fuzzer (boundary values per width), and runs the
#    64-bit golden pipeline + rejection suite.
# 8. Asserts the emitted bodies the S3b proofs reason about are exactly
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
NESTED_BIN="$WORKDIR/circe_nested_native"
SKIP_BIN="$WORKDIR/circe_skip_native"
FIND_BIN="$WORKDIR/circe_find_native"
CLS_BIN="$WORKDIR/circe_cls_native"
ADD64_BIN="$WORKDIR/circe_add64_native"
ADDU64_BIN="$WORKDIR/circe_addu64_native"

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

echo "== regenerate out/ (S3a control flow) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (S3a control flow) =="
diff -u tests/golden/NestedSum.lean out/NestedSum.lean
diff -u tests/golden/SkipSum.lean out/SkipSum.lean
diff -u tests/golden/FindEq.lean out/FindEq.lean
diff -u tests/golden/Cls.lean out/Cls.lean
echo "control-flow goldens in sync"

echo "== typecheck emitted control-flow files =="
lake env lean out/NestedSum.lean
lake env lean out/SkipSum.lean
lake env lean out/FindEq.lean
lake env lean out/Cls.lean
echo "emitted control-flow files typecheck"

echo "== native control-flow drivers =="
cc -O0 -Wall tests/c/nested_sum.c tests/diff/driver_nested.c -o "$NESTED_BIN"
cc -O0 -Wall tests/c/skip_sum.c tests/diff/driver_skip.c -o "$SKIP_BIN"
cc -O0 -Wall tests/c/find_eq.c tests/diff/driver_find.c -o "$FIND_BIN"
cc -O0 -Wall tests/c/cls.c tests/diff/driver_cls.c -o "$CLS_BIN"

echo "== differential test control flow (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffFlow.lean "$NESTED_BIN" "$SKIP_BIN" "$FIND_BIN" "$CLS_BIN" "$TRIALS"

echo "== golden pipeline + control-flow rejection suite =="
lake env lean --run tests/lean/GoldenFlow.lean

echo "== emitted-body correspondence (S3a emit_correct transfer) =="
grep -qF "nestedSumU32 n.toNat m.toNat" out/NestedSum.lean
grep -qF "skipSumU32 n.toNat" out/SkipSum.lean
grep -qF "findEqOut a n.toNat k" out/FindEq.lean
grep -qF "if x == 0 then .ok 10" out/Cls.lean
echo "emitted control-flow bodies match Emit assumptions"

echo "== regenerate out/ (S3b 64-bit widths) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (S3b 64-bit widths) =="
diff -u tests/golden/Add64.lean out/Add64.lean
diff -u tests/golden/Addu64.lean out/Addu64.lean
echo "64-bit goldens in sync"

echo "== typecheck emitted 64-bit files =="
lake env lean out/Add64.lean
lake env lean out/Addu64.lean
echo "emitted 64-bit files typecheck"

echo "== native 64-bit drivers =="
cc -O0 -Wall tests/c/add64.c tests/diff/driver_add64.c -o "$ADD64_BIN"
cc -O0 -Wall tests/c/addu64.c tests/diff/driver_addu64.c -o "$ADDU64_BIN"

echo "== differential test 64-bit widths (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffWidth.lean "$ADD64_BIN" "$ADDU64_BIN" "$TRIALS"

echo "== golden pipeline + 64-bit rejection suite =="
lake env lean --run tests/lean/GoldenWidth.lean

echo "== emitted-body correspondence (S3b emit_correct transfer) =="
grep -qF "checkedAddI64 a b" out/Add64.lean
grep -qF ".ok (a + b)" out/Addu64.lean
echo "emitted 64-bit bodies match Emit assumptions"

echo "CHECK-OK"
