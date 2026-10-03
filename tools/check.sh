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
# 9. (S4) Regenerates the 14 `out/*_Spec.lean` stubs, asserts all exist
#    and typecheck, asserts `cir_simp` covers call-unfold / struct-field
#    / wider-width / vec rules, and evaluates every stub prop entry
#    (`_check`) to `true`.
# 10. (S5) Asserts the stage-2 tactics exist (`cir_fuel` + fuel bound
#    in `Circe.Eval`, `cir_choose` in `Circe.Emit`) and the `sum`/`vec`
#    emit-correctness + `choose` lens proofs use them.
# 11. (M1a) Regenerates + diffs the two-block golden, typechecks the
#    emitted files, builds the native two-block driver, runs the
#    two-block differential fuzzer, and runs the two-block golden
#    pipeline + rejection suite.
# 12. (M1b) Regenerates + diffs the `u64` heap golden, typechecks the
#    emitted files, builds the native `u64` driver, runs the `u64`
#    differential fuzzer, and runs the `u64` golden pipeline +
#    rejection suite (including mixed-width `AssertFail` checks).
# 13. (M1c) Regenerates + diffs the grown-block (`realloc`) golden,
#    typechecks the emitted files, builds the native grown-block driver,
#    runs the grown-block differential fuzzer, and runs the grown-block
#    golden pipeline + rejection suite (including the `realloc(p, 0)` /
#    `realloc(NULL, n)` spelling rejections + width `AssertFail` check).
# 14. (M1d) Builds the native leak driver, runs the leak differential
#    fuzzer (leaking C vs verified Lean: return values agree), and runs
#    the free-discipline golden pipeline + rejection suite (real leak
#    corpus, stripped-free acceptance for all four heap shapes, text
#    double-`free` rejection, token-level double-free/use-after-free
#    `AssertFail` checks).
# 15. (M2 setup) Asserts no checked-in C `.cir` contains the newly-gated
#    `cir.cleanup` / `cir.trap` ops and runs the module-validation golden
#    suite (`GoldenM2Setup`: trap/cleanup rejection, per-definition
#    `validateModule` on caller/heap modules with declarations skipped,
#    missing-fact wiring error). No new shapes admitted.
# 16. (M2a) Regenerates + diffs the const-method goldens, typechecks the
#    emitted files, builds the native C++ method driver, runs the
#    method differential fuzzer, and runs the method golden pipeline +
#    rejection suite (real C++ corpus with `-fno-exceptions`, no oracle
#    facts, coerce-deferral pin + method misshapen cases).
# 17. (M2b) Regenerates + diffs the ctor/dtor goldens, typechecks the
#    emitted files, builds the native C++ accumulator driver, runs the
#    accumulator differential fuzzer, and runs the accumulator golden
#    pipeline + rejection suite (real C++ corpus with `-fno-exceptions`,
#    one oracle fact for the int-only entry, exact call-multiset +
#    const-0 pins + cleanup-gate strictness cases).
# 18. (M2c) Regenerates + diffs the new/delete golden, typechecks the
#    emitted files, builds the native C++ box driver, runs the box
#    differential fuzzer, and runs the box golden pipeline + rejection
#    suite (real C++ corpus with `-fno-exceptions`, one oracle fact for
#    the int-only entry, 4-byte size + null-guard + call-multiset pins,
#    leak acceptance, double-delete gate, token checks).
# 19. (N2a) Typechecks the read-only sharing discipline (`Circe.ReadOnly`:
#    two-`sharedBorrow`-reader footprints + alias soundness, writer
#    exclusion) and runs the read-only golden rejection suite
#    (`GoldenReadOnly`: writer+reader still rejects loudly, two-reader
#    shape does not derive). No new corpus: text-gate admission is
#    N2b/N2c work.
# 20. (N2b) Runs the interior rejection catalog (`GoldenRejectCatalog`:
#    writer+reader / escaping-borrow / borrow-after-free each reject
#    with their per-cause message) and asserts the three cause tokens
#    are present in `Circe.Validator`.
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

echo "== regenerate out/ (S4 spec stubs) =="
lake env lean --run tools/GenOut.lean

echo "== spec stub existence + typecheck (25 stubs) =="
[ "$(ls out/*_Spec.lean | wc -l)" = 25 ] || { echo "expected 25 spec stubs"; exit 1; }
for f in out/*_Spec.lean; do lake env lean "$f"; done
echo "all 25 spec stubs typecheck"

echo "== cir_simp coverage (S4 growth) =="
grep -qF "addCallerFwd_as_calls, sumCallerFwd_is_call" Circe/Tactics.lean
grep -qF "pointTranslate_ok, pointTranslate_err_x" Circe/Tactics.lean
grep -qF "checkedAddI64_ok, checkedAddI64_err" Circe/Tactics.lean
grep -qF "vecFillSumU32_correct" Circe/Tactics.lean
grep -qF "vecReallocFillSumU32_correct" Circe/Tactics.lean
grep -qF "vecFillSumU64_correct" Circe/Tactics.lean
grep -qF "result_bind_assoc, result_pure_bind" Circe/Tactics.lean
grep -qF "pointSum, pointSum_ok, pointSum_err, methodSumFwd_ok," Circe/Tactics.lean
grep -qF "accTwo, accTwo_ok, accTwo_err_a, accTwo_err_b, accAddFwd_ok," Circe/Tactics.lean
grep -qF "boxThrough, boxThrough_ok" Circe/Tactics.lean
echo "cir_simp covers call-unfold, struct-field, method, ctor, wider-width, vec rules"

echo "== spec stub contents (signature + body ref + edges + prop entry) =="
grep -qF "_spec_fwd" out/SumArray_Spec.lean
grep -qF "_spec_edges" out/SumArray_Spec.lean
grep -qF "_spec_check" out/SumArray_Spec.lean
grep -qF "prefixSumU32" out/SumArray_Spec.lean
echo "spec stubs carry the required sections"

echo "== spec stub prop entries evaluate true =="
for f in out/*_Spec.lean; do
  check=$(grep -oE '[A-Za-z_0-9]+_spec_check' "$f" | head -1)
  tmp="$WORKDIR/spec_eval_tmp.lean"
  cp "$f" "$tmp"
  echo "#eval $check" >> "$tmp"
  lake env lean "$tmp" | grep -q '^true$' || { echo "spec check false: $f"; exit 1; }
done
echo "all 25 spec prop entries true"

echo "== S5 helpers present (Tactics stage 2) =="
grep -qF 'macro "cir_fuel"' Circe/Eval.lean
grep -qF "word32_lt_two32_of_fuel" Circe/Eval.lean
grep -qF 'macro "cir_choose"' Circe/Emit/Choose.lean
echo "cir_fuel + fuel bound (Eval) and cir_choose (Emit.Choose) present"

echo "== S5 adoption (sum/vec/choose proofs use the shared helpers) =="
grep -qF "word32_lt_two32_of_fuel _ hfuel" Circe/Emit/Sum.lean
grep -qF "cir_choose b" Circe/Emit/Choose.lean
grep -qr "by cir_fuel" Circe/Emit/
echo "sum/vec emit-correctness + choose lens proofs use S5 helpers"

echo "== regenerate out/ (M1a two-block heap) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (M1a two-block heap) =="
diff -u tests/golden/VecCopySum.lean out/VecCopySum.lean
echo "two-block golden in sync"

echo "== typecheck emitted two-block file =="
lake env lean out/VecCopySum.lean
lake env lean out/VecCopySum_Spec.lean
echo "emitted two-block files typecheck"

echo "== native two-block driver =="
VEC2_BIN="$WORKDIR/circe_vec2_native"
cc -O0 -Wall tests/c/vec_copy_sum.c tests/diff/driver_veccopy.c -o "$VEC2_BIN"

echo "== differential test two-block heap (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffVec2.lean "$VEC2_BIN" "$TRIALS"

echo "== golden pipeline + two-block rejection suite =="
lake env lean --run tests/lean/GoldenVec2.lean

echo "== emitted-body correspondence (M1a emit_correct transfer) =="
grep -qF "vecFillSumU32 n.toNat" out/VecCopySum.lean
grep -qF "vec_copy_sum_fwd" out/VecCopySum.lean
echo "emitted two-block body matches Emit assumptions"

echo "== regenerate out/ (M1b u64 heap) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (M1b u64 heap) =="
diff -u tests/golden/VecAllocU64.lean out/VecAllocU64.lean
echo "u64 golden in sync"

echo "== typecheck emitted u64 files =="
lake env lean out/VecAllocU64.lean
lake env lean out/VecAllocU64_Spec.lean
echo "emitted u64 files typecheck"

echo "== native u64 driver =="
VEC64_BIN="$WORKDIR/circe_vec64_native"
cc -O0 -Wall tests/c/vec_alloc_u64.c tests/diff/driver_vec64.c -o "$VEC64_BIN"

echo "== differential test u64 heap (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffVec64.lean "$VEC64_BIN" "$TRIALS"

echo "== golden pipeline + u64 rejection suite =="
lake env lean --run tests/lean/GoldenVec64.lean

echo "== emitted-body correspondence (M1b emit_correct transfer) =="
grep -qF "vecFillSumU64 n.toNat" out/VecAllocU64.lean
grep -qF "vec_alloc_u64_fwd" out/VecAllocU64.lean
echo "emitted u64 body matches Emit assumptions"

echo "== regenerate out/ (M1c grown-block heap) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (M1c grown-block heap) =="
diff -u tests/golden/VecRealloc.lean out/VecRealloc.lean
echo "grown-block golden in sync"

echo "== typecheck emitted grown-block files =="
lake env lean out/VecRealloc.lean
lake env lean out/VecRealloc_Spec.lean
echo "emitted grown-block files typecheck"

echo "== native grown-block driver =="
VECREALLOC_BIN="$WORKDIR/circe_vecrealloc_native"
cc -O0 -Wall tests/c/vec_realloc.c tests/diff/driver_vecrealloc.c -o "$VECREALLOC_BIN"

echo "== differential test grown-block heap (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffVecRealloc.lean "$VECREALLOC_BIN" "$TRIALS"

echo "== golden pipeline + grown-block rejection suite =="
lake env lean --run tests/lean/GoldenVecRealloc.lean

echo "== emitted-body correspondence (M1c emit_correct transfer) =="
grep -qF "vecReallocFillSumU32 n.toNat" out/VecRealloc.lean
grep -qF "vec_realloc_fwd" out/VecRealloc.lean
echo "emitted grown-block body matches Emit assumptions"

echo "== native leak driver (M1d free discipline) =="
VECLEAK_BIN="$WORKDIR/circe_vecleak_native"
cc -O0 -Wall tests/c/vec_alloc_leak.c tests/diff/driver_vecleak.c -o "$VECLEAK_BIN"

echo "== differential test leak (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffVecLeak.lean "$VECLEAK_BIN" "$TRIALS"

echo "== golden pipeline + free-discipline suite =="
lake env lean --run tests/lean/GoldenFreeDiscipline.lean

echo "== M2 setup gates (trap/cleanup + module validation) =="
# The C corpus must stay free of the newly-gated ops; the C++ corpus
# (tests/cpp/ → tests/cir/) legitimately carries `cleanup` / `trap`
# in the exact M2b entry shape, so it is excluded by construction.
excludes=()
for src in tests/cpp/*.cpp; do excludes+=(--exclude="$(basename "$src" .cpp).cir"); done
if grep -rl "cir.cleanup\|cir.trap" "${excludes[@]}" tests/cir/; then
  echo "newly-gated ops present in C corpus (breaks M2 setup gate)"
  exit 1
fi
echo "C corpus free of cir.cleanup / cir.trap"
lake env lean --run tests/lean/GoldenM2Setup.lean

echo "== regenerate out/ (M2a const-methods) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (M2a const-methods) =="
diff -u tests/golden/MethodSum.lean out/MethodSum.lean
diff -u tests/golden/PointSumRef.lean out/PointSumRef.lean
echo "method goldens in sync"

echo "== typecheck emitted method files =="
lake env lean out/MethodSum.lean
lake env lean out/PointSumRef.lean
lake env lean out/MethodSum_Spec.lean
lake env lean out/PointSumRef_Spec.lean
echo "emitted method files typecheck"

echo "== native method driver =="
METHOD_BIN="$WORKDIR/circe_method_native"
c++ -O0 -Wall tests/cpp/point_sum_ref.cpp tests/diff/driver_method.cpp -o "$METHOD_BIN"

echo "== differential test methods (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffMethod.lean "$METHOD_BIN" "$TRIALS"

echo "== golden pipeline + method rejection suite =="
lake env lean --run tests/lean/GoldenMethod.lean

echo "== emitted-body correspondence (M2a emit_correct transfer) =="
grep -qF "pointSum p" out/MethodSum.lean
grep -qF "pointSum p" out/PointSumRef.lean
echo "emitted method bodies match Emit assumptions"

echo "== regenerate out/ (M2b ctors/dtors) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (M2b ctors/dtors) =="
diff -u tests/golden/AccCtor.lean out/AccCtor.lean
diff -u tests/golden/AccAdd.lean out/AccAdd.lean
diff -u tests/golden/AccGet.lean out/AccGet.lean
diff -u tests/golden/AccDtor.lean out/AccDtor.lean
diff -u tests/golden/AccTwo.lean out/AccTwo.lean
echo "ctor/dtor goldens in sync"

echo "== typecheck emitted ctor/dtor files =="
lake env lean out/AccCtor.lean
lake env lean out/AccAdd.lean
lake env lean out/AccGet.lean
lake env lean out/AccDtor.lean
lake env lean out/AccTwo.lean
lake env lean out/AccCtor_Spec.lean
lake env lean out/AccAdd_Spec.lean
lake env lean out/AccGet_Spec.lean
lake env lean out/AccDtor_Spec.lean
lake env lean out/AccTwo_Spec.lean
echo "emitted ctor/dtor files typecheck"

echo "== native accumulator driver =="
ACC_BIN="$WORKDIR/circe_acc_native"
c++ -O0 -Wall tests/cpp/acc_two.cpp tests/diff/driver_acc.cpp -o "$ACC_BIN"

echo "== differential test accumulator (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffAcc.lean "$ACC_BIN" "$TRIALS"

echo "== golden pipeline + accumulator rejection suite =="
lake env lean --run tests/lean/GoldenAcc.lean

echo "== emitted-body correspondence (M2b emit_correct transfer) =="
grep -qF ".ok accCtor" out/AccCtor.lean
grep -qF "accAdd s v" out/AccAdd.lean
grep -qF "accGet s" out/AccGet.lean
grep -qF "accDtor t" out/AccDtor.lean
grep -qF "accTwo a b" out/AccTwo.lean
echo "emitted ctor/dtor bodies match Emit assumptions"

echo "== regenerate out/ (M2c new/delete) =="
lake env lean --run tools/GenOut.lean

echo "== golden diff (M2c new/delete) =="
diff -u tests/golden/BoxThrough.lean out/BoxThrough.lean
echo "new/delete golden in sync"

echo "== typecheck emitted new/delete files =="
lake env lean out/BoxThrough.lean
lake env lean out/BoxThrough_Spec.lean
echo "emitted new/delete files typecheck"

echo "== native box driver =="
BOX_BIN="$WORKDIR/circe_box_native"
c++ -O0 -Wall tests/cpp/box_through.cpp tests/diff/driver_box.cpp -o "$BOX_BIN"

echo "== differential test box (${TRIALS} trials) =="
lake env lean --run tests/lean/DiffBox.lean "$BOX_BIN" "$TRIALS"

echo "== golden pipeline + box rejection suite =="
lake env lean --run tests/lean/GoldenBox.lean

echo "== emitted-body correspondence (M2c emit_correct transfer) =="
grep -qF "boxThrough x" out/BoxThrough.lean
echo "emitted new/delete body matches Emit assumptions"

echo "== M3a mem model (flat block map + per-leaf transfer) =="
lake env lean Circe/Mem.lean
lake env lean Circe/Transfer.lean
grep -q "theorem memTransfer_add" Circe/Mem.lean
grep -q "theorem memTransfer_incr" Circe/Mem.lean
grep -q "theorem memTransfer_sum " Circe/Transfer.lean
grep -q "theorem memTransfer_sum_oob" Circe/Transfer.lean
grep -q "theorem memTransfer_vec " Circe/Transfer.lean
grep -q "def m3c_transfer_statement" Circe/Mem.lean
echo "mem model builds, per-leaf transfers present (add/incr/sum/sum-oob/vec)"

echo "== M3b derived noalias (text-derived, verdict-cache agreement) =="
lake env lean Circe/Validator.lean
lake env lean Circe/Derived.lean
lake env lean --run tests/lean/DerivedNoalias.lean
grep -q "def derivedNoalias" Circe/Validator.lean
grep -q "theorem derivedNoalias_all_noalias" Circe/Validator.lean
grep -q "theorem derivedNoalias_admitted_c" Circe/Validator.lean
grep -q "theorem oracleNoalias_choose" Circe/Derived.lean
grep -q "theorem oracleNoalias_sumCaller" Circe/Derived.lean
grep -q "theorem oracleNoalias_findEq" Circe/Derived.lean
grep -q "theorem derived_bridge_noalias" Circe/Derived.lean
echo "derived noalias builds, per-shape footprints + cache agreement green"

echo "== M3c loop-free transfers (choose/widths/cls/translate) =="
lake env lean Circe/Transfer.lean
grep -q "theorem memTransfer_choose" Circe/Transfer.lean
grep -q "theorem memTransfer_add64" Circe/Transfer.lean
grep -q "theorem memTransfer_addu64" Circe/Transfer.lean
grep -q "theorem memTransfer_cls" Circe/Transfer.lean
grep -q "theorem memTransfer_translate" Circe/Transfer.lean
grep -q "theorem oracleNoalias_add64" Circe/Derived.lean
grep -q "theorem oracleNoalias_addu64" Circe/Derived.lean
grep -q "theorem oracleNoalias_cls" Circe/Derived.lean
grep -q "theorem oracleNoalias_translate" Circe/Derived.lean
grep -q "theorem memEvalExpr_add_fget_var" Circe/Mem.lean
echo "loop-free C transfers green (choose/add64/addu64/cls/translate)"

echo "== M3c flow transfers (nested/skip/find_eq) =="
lake env lean Circe/Transfer.lean
grep -q "theorem memTransfer_nested" Circe/Transfer.lean
grep -q "theorem memTransfer_skip" Circe/Transfer.lean
grep -q "theorem memTransfer_findEq" Circe/Transfer.lean
grep -q "theorem memNestedOuter_correct" Circe/Transfer.lean
grep -q "theorem memSkipWhile_correct" Circe/Transfer.lean
grep -q "theorem memFindWhile_some" Circe/Transfer.lean
grep -q "theorem memFindWhile_none" Circe/Transfer.lean
grep -q "theorem oracleNoalias_nested" Circe/Derived.lean
grep -q "theorem oracleNoalias_skip" Circe/Derived.lean
echo "flow C transfers green (nested/skip/find_eq)"

echo "== M3c caller transfers (add_caller/sum_caller) =="
lake env lean Circe/Transfer.lean
grep -q "theorem memEvalProgFunc_addCaller" Circe/Transfer.lean
grep -q "theorem memTransferProg_addCaller" Circe/Transfer.lean
grep -q "theorem memEvalProgFunc_sumCaller" Circe/Transfer.lean
grep -q "theorem memTransferProg_sumCaller" Circe/Transfer.lean
grep -q "def memEvalProgStmt" Circe/Mem.lean
grep -q "def memEvalProgFunc" Circe/Mem.lean
grep -q "theorem memEvalProgStmt_callRet_ok" Circe/Mem.lean
grep -q "theorem memEvalProgStmt_callRet_err" Circe/Mem.lean
echo "caller C transfers green (add_caller/sum_caller)"

echo "== M3c heap transfers (vec_copy_sum) =="
lake env lean Circe/Transfer.lean
grep -q "theorem memVec2FillWhile_correct" Circe/Transfer.lean
grep -q "theorem memVec2CopyWhile_correct" Circe/Transfer.lean
grep -q "theorem memVec2SumWhile_correct" Circe/Transfer.lean
grep -q "theorem memEvalFuncFuel_vec2" Circe/Transfer.lean
grep -q "theorem memTransfer_vec2" Circe/Transfer.lean
grep -q "theorem oracleNoalias_vec2" Circe/Derived.lean
grep -q "theorem memFind_memStore_other" Circe/Mem.lean
grep -q "theorem memFind_memFree_other" Circe/Mem.lean
echo "heap C transfers green (vec_copy_sum)"

echo "== M3c heap transfers (vec_realloc) =="
grep -q "def memRealloc" Circe/Mem.lean
grep -q "theorem vrealloc_lockstep" Circe/Mem.lean
grep -q "theorem memEvalStmtFuel_vrealloc" Circe/Mem.lean
grep -q "theorem memVecReallocFillWhile_correct" Circe/Transfer.lean
grep -q "theorem memVecReallocExtWhile_correct" Circe/Transfer.lean
grep -q "theorem memVecReallocSumWhile_correct" Circe/Transfer.lean
grep -q "theorem memVecReallocStep_eval" Circe/Transfer.lean
grep -q "theorem memEvalFuncFuel_vecRealloc" Circe/Transfer.lean
grep -q "theorem memTransfer_vecRealloc" Circe/Transfer.lean
grep -q "theorem oracleNoalias_vecRealloc" Circe/Derived.lean
echo "heap C transfers green (vec_realloc)"

echo "== M3c heap transfers (vec_alloc_u64) =="
grep -q "structure Block64" Circe/Mem.lean
grep -q "def memFind64" Circe/Mem.lean
grep -q "def memAllocData64" Circe/Mem.lean
grep -q "def memLoad64" Circe/Mem.lean
grep -q "def memStore64" Circe/Mem.lean
grep -q "def memFree64" Circe/Mem.lean
grep -q "theorem vset64_lockstep" Circe/Mem.lean
grep -q "theorem vfree64_lockstep" Circe/Mem.lean
grep -q "theorem memEvalStmtFuel_let_vnew64" Circe/Mem.lean
grep -q "theorem memVec64FillWhile_correct" Circe/Transfer.lean
grep -q "theorem memVec64SumWhile_correct" Circe/Transfer.lean
grep -q "theorem memEvalFuncFuel_vec64" Circe/Transfer.lean
grep -q "theorem memTransfer_vec64" Circe/Transfer.lean
grep -q "theorem oracleNoalias_vec64" Circe/Derived.lean
echo "heap C transfers green (vec_alloc_u64)"

echo "== M3d C++ transfers (method/acc/box) =="
lake env lean Circe/Transfer.lean
grep -q "theorem memEvalProgStmt_cleanup" Circe/Mem.lean
grep -q "theorem memEvalStmtFuel_let_boxNew" Circe/Mem.lean
grep -q "theorem memEvalExpr_boxGet_hit" Circe/Mem.lean
grep -q "theorem vboxFree_lockstep" Circe/Mem.lean
grep -q "theorem memEvalStmtFuel_boxFree" Circe/Mem.lean
grep -q "theorem memEvalFuncFuel_methodSum" Circe/Transfer.lean
grep -q "theorem memTransfer_methodSum" Circe/Transfer.lean
grep -q "theorem memEvalProgFunc_pointSumRef" Circe/Transfer.lean
grep -q "theorem memTransferProg_pointSumRef" Circe/Transfer.lean
grep -q "theorem memEvalFuncFuel_accCtor" Circe/Transfer.lean
grep -q "theorem memTransfer_accAdd" Circe/Transfer.lean
grep -q "theorem memTransfer_accGet" Circe/Transfer.lean
grep -q "theorem memTransfer_accDtor" Circe/Transfer.lean
grep -q "theorem memEvalProgFunc_accTwo" Circe/Transfer.lean
grep -q "theorem memTransferProg_accTwo" Circe/Transfer.lean
grep -q "theorem memEvalFuncFuel_boxThrough" Circe/Transfer.lean
grep -q "theorem memTransfer_boxThrough" Circe/Transfer.lean
grep -q "theorem oracleNoalias_methodSum" Circe/Derived.lean
grep -q "theorem oracleNoalias_pointSumRef" Circe/Derived.lean
grep -q "theorem oracleNoalias_accTwo" Circe/Derived.lean
grep -q "theorem oracleNoalias_boxThrough" Circe/Derived.lean
echo "C++ transfers green (method/acc/box)"

echo "== N2a read-only sharing discipline (two sharedBorrow readers, no writers) =="
lake env lean Circe/ReadOnly.lean
lake env lean --run tests/lean/GoldenReadOnly.lean
grep -q "def IsReadOnlyParams" Circe/ReadOnly.lean
grep -q "theorem hasWriter_not_readOnly" Circe/ReadOnly.lean
grep -q "theorem writer_reader_excluded" Circe/ReadOnly.lean
grep -q "theorem twoReaderParams_readOnly" Circe/ReadOnly.lean
grep -q "theorem bindMemArgs_twoShared" Circe/ReadOnly.lean
grep -q "theorem twoShared_noalias" Circe/ReadOnly.lean
grep -q "theorem twoShared_consistent" Circe/ReadOnly.lean
grep -q "theorem twoShared_alias_sound" Circe/ReadOnly.lean
grep -q "GoldenReadOnly" tools/check.sh
echo "read-only discipline green (model footprints + writer+reader rejection)"

echo "== N2b interior rejection catalog (writer+reader / escaping-borrow / borrow-after-free) =="
lake env lean --run tests/lean/GoldenRejectCatalog.lean
grep -q "writer+reader" Circe/Validator.lean
grep -q "escaping-borrow" Circe/Validator.lean
grep -q "borrow-after-free" Circe/Validator.lean
grep -q "GoldenRejectCatalog" tools/check.sh
echo "rejection catalog green (per-cause messages + golden pins)"

echo "CHECK-OK"
