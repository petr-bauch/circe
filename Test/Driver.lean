/-
`circe-test`: the single parallel test driver (replaces `tools/check.sh`).

One process runs the whole gate: setup (regenerate `out/`, native builds)
then every golden diff, typecheck, differential fuzzer, golden suite,
and content assertion as parallel `IO` tasks — run-all-and-report (all
failures print, nonzero exit at the end) instead of `set -e` fail-fast.
Coverage is identical to `tools/check.sh [trials]` (same corpus, same
goldens, same fuzzers, same trials parameter, default 1000); the task
roster below IS the wiring, and `main` asserts every registered task
ran. `tools/check.sh` delegates here; the `check-phase*.sh` scripts stay
for compat.
-/
import DerivedNoalias
import DiffAcc
import DiffArith
import DiffArray
import DiffBox
import DiffCalls
import DiffFlow
import DiffMethod
import DiffMove
import DiffNorestrict
import DiffOptional
import DiffOverload
import DiffPhase3
import DiffPhase4
import DiffSpan
import DiffStruct
import DiffTadd
import DiffVec
import DiffVec2
import DiffVec64
import DiffVecLeak
import DiffVecRead
import DiffVecRealloc
import DiffReserve
import DiffInsert
import DiffErase
import DiffSort
import DiffView
import DiffWidth
import GoldenAcc
import GoldenAliasProbe
import GoldenArray
import GoldenArraySort
import GoldenArraySort8
import GoldenBox
import GoldenCalls
import GoldenFlow
import GoldenFreeDiscipline
import GoldenM2Setup
import GoldenMethod
import GoldenMove
import GoldenOptional
import GoldenOverload
import GoldenPhase4
import GoldenPhase6
import GoldenPhase7
import GoldenReadOnly
import GoldenRejectCatalog
import GoldenSpan
import GoldenStruct
import GoldenTadd
import GoldenVec2
import GoldenVec64
import GoldenVecRead
import GoldenVecRealloc
import GoldenView
import GoldenVecGrow
import GoldenWidth
import ScopeReport
import Circe.Parser

/-- Scratch dir for native binaries + spec-eval temporaries (mirrors
    `tools/check.sh` `$WORKDIR`). -/
def workdir : String := "/tmp/opencode"

/-- Run a command, throwing with its output on nonzero exit. -/
def sh (cmd : String) (args : Array String) : IO Unit := do
  let _ ← IO.Process.run { cmd := cmd, args := args }

/-- Run a command and return trimmed stdout, throwing on nonzero exit. -/
def shOut (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := cmd, args := args }
  pure out.trimAscii.toString

/-- `grep -qF`: fail unless `file` contains `needle` (fixed string). -/
def needHas (file needle : String) : IO Unit := do
  let text ← IO.FS.readFile file
  if !containsSubstr text needle then
    throw (IO.userError s!"missing {needle} in {file}")

/-- `diff -u` on file bytes: fail with sizes + first-difference context. -/
def needSameBytes (want got : String) : IO Unit := do
  let w ← IO.FS.readFile want
  let g ← IO.FS.readFile got
  if w == g then pure () else
    throw (IO.userError
      s!"golden mismatch: {want} ({w.length}B) vs {got} ({g.length}B)")

/-- `ls <dir>`, one entry per line. -/
def lsDir (dir : String) : IO (List String) := do
  let out ← shOut "ls" #[dir]
  pure ((out.splitOn "\n").filter (fun l => l != ""))

/-- Ends-with on strings (for file-suffix filters). -/
def endsWith (s suffix : String) : Bool :=
  suffix.length ≤ s.length &&
    (s.toList.drop (s.length - suffix.length) == suffix.toList)

/-- A named job; the roster in `main` is the whole gate. -/
abbrev Job := String × IO Unit

/-- Run jobs as parallel tasks, collecting per-job outcomes. -/
def runJobs (jobs : List Job) : IO (List (String × Except IO.Error Unit)) := do
  let tasks ← jobs.mapM (fun (n, a) => do
    let t ← IO.asTask a
    pure (n, t))
  tasks.mapM (fun (n, t) => pure (n, t.get))

/-- Typecheck one file with the project toolchain (`lake env lean`). -/
def typecheck (f : String) : IO Unit := sh "lake" #["env", "lean", f]

/-- Build one native driver binary. -/
def ccBuild (cc : String) (srcs : List String) (out : String) : IO Unit :=
  sh cc ((#["-O0", "-Wall"] ++ srcs.toArray) ++ #["-o", out])

/-! ## Roster tables (mirror `tools/check.sh`) -/

/-- Native binary path in the scratch dir. -/
def bin (n : String) : String := s!"{workdir}/{n}"

/-- Compiler, sources, output: every native driver `check.sh` builds. -/
def nativeBuilds : List (String × List String × String) :=
  [("cc", ["tests/c/add.c", "tests/diff/driver_add.c"], bin "circe_add_native"),
   ("cc", ["tests/c/incr_ptr.c", "tests/diff/driver_incr.c"], bin "circe_incr_native"),
   ("cc", ["tests/c/choose_ptr.c", "tests/diff/driver_choose.c"], bin "circe_choose_native"),
   ("cc", ["tests/c/sum_array.c", "tests/diff/driver_sum.c"], bin "circe_sum_native"),
   ("cc", ["tests/c/add.c", "tests/c/add_caller.c", "tests/diff/driver_add_caller.c"], bin "circe_add_caller_native"),
   ("cc", ["tests/c/sum_array.c", "tests/c/sum_caller.c", "tests/diff/driver_sum_caller.c"], bin "circe_sum_caller_native"),
   ("cc", ["tests/c/struct_by_value.c", "tests/diff/driver_struct.c"], bin "circe_struct_native"),
   ("cc", ["tests/c/nested_sum.c", "tests/diff/driver_nested.c"], bin "circe_nested_native"),
   ("cc", ["tests/c/skip_sum.c", "tests/diff/driver_skip.c"], bin "circe_skip_native"),
   ("cc", ["tests/c/find_eq.c", "tests/diff/driver_find.c"], bin "circe_find_native"),
   ("cc", ["tests/c/cls.c", "tests/diff/driver_cls.c"], bin "circe_cls_native"),
   ("cc", ["tests/c/cls_fall.c", "tests/diff/driver_cls_fall.c"], bin "circe_cls_fall_native"),
   ("cc", ["tests/c/cls_dense.c", "tests/diff/driver_cls_dense.c"], bin "circe_cls_dense_native"),
   ("cc", ["tests/c/cls_break.c", "tests/diff/driver_cls_break.c"], bin "circe_cls_break_native"),
   ("cc", ["tests/c/cls_add.c", "tests/diff/driver_cls_add.c"], bin "circe_cls_add_native"),
   ("cc", ["tests/c/add64.c", "tests/diff/driver_add64.c"], bin "circe_add64_native"),
   ("cc", ["tests/c/addu64.c", "tests/diff/driver_addu64.c"], bin "circe_addu64_native"),
   ("cc", ["tests/c/neg.c", "tests/diff/driver_neg.c"], bin "circe_neg_native"),
   ("cc", ["tests/c/sdiv.c", "tests/diff/driver_sdiv.c"], bin "circe_sdiv_native"),
   ("cc", ["tests/c/xor_u32.c", "tests/diff/driver_xor_u32.c"], bin "circe_xor_u32_native"),
   ("cc", ["tests/c/and_u32.c", "tests/diff/driver_and_u32.c"], bin "circe_and_u32_native"),
   ("cc", ["tests/c/or_u32.c", "tests/diff/driver_or_u32.c"], bin "circe_or_u32_native"),
   ("cc", ["tests/c/shl_u32.c", "tests/diff/driver_shl_u32.c"], bin "circe_shl_u32_native"),
   ("cc", ["tests/c/shr_u32.c", "tests/diff/driver_shr_u32.c"], bin "circe_shr_u32_native"),
   ("cc", ["tests/c/vec_alloc.c", "tests/diff/driver_vec.c"], bin "circe_vec_native"),
   ("cc", ["tests/c/vec_copy_sum.c", "tests/diff/driver_veccopy.c"], bin "circe_vec2_native"),
   ("cc", ["tests/c/vec_alloc_u64.c", "tests/diff/driver_vec64.c"], bin "circe_vec64_native"),
   ("cc", ["tests/c/vec_realloc.c", "tests/diff/driver_vecrealloc.c"], bin "circe_vecrealloc_native"),
   ("cc", ["tests/c/vec_alloc_leak.c", "tests/diff/driver_vecleak.c"], bin "circe_vecleak_native"),
   ("c++", ["tests/cpp/point_sum_ref.cpp", "tests/diff/driver_method.cpp"], bin "circe_method_native"),
   ("c++", ["tests/cpp/acc_two.cpp", "tests/diff/driver_acc.cpp"], bin "circe_acc_native"),
   ("c++", ["tests/cpp/box_through.cpp", "tests/diff/driver_box.cpp"], bin "circe_box_native"),
   ("c++", ["tests/cpp/overload_add.cpp", "tests/diff/driver_overload.cpp"], bin "circe_overload_native"),
   ("c++", ["tests/cpp/ns_add.cpp", "tests/diff/driver_ns_add.cpp"], bin "circe_ns_add_native"),
   ("c++", ["tests/cpp/move_int.cpp", "tests/diff/driver_move_int.cpp"], bin "circe_move_int_native"),
   ("c++", ["tests/cpp/move_acc.cpp", "tests/diff/driver_move_acc.cpp"], bin "circe_move_acc_native"),
   ("c++", ["tests/cpp/scope_early.cpp", "tests/diff/driver_scope_early.cpp"], bin "circe_scope_early_native"),
   ("c++", ["tests/cpp/tadd.cpp", "tests/diff/driver_tadd.cpp"], bin "circe_tadd_native"),
   ("c++", ["tests/cpp/array_sum.cpp", "tests/diff/driver_array_sum.cpp"], bin "circe_array_sum_native"),
   ("c++", ["tests/cpp/opt_deref.cpp", "tests/diff/driver_opt_deref.cpp"], bin "circe_opt_deref_native"),
   ("c++", ["-std=c++20", "tests/cpp/span_sum.cpp", "tests/diff/driver_span_sum.cpp"], bin "circe_span_sum_native"),
   ("c++", ["-std=c++17", "tests/cpp/view_sum.cpp", "tests/diff/driver_view_sum.cpp"], bin "circe_view_sum_native"),
   ("c++", ["-std=c++17", "tests/cpp/vec_reserve_sum.cpp", "tests/diff/driver_vec_reserve.cpp"], bin "circe_vec_reserve_native"),
   ("c++", ["-std=c++17", "tests/cpp/vec_insert_sum.cpp", "tests/diff/driver_vec_insert.cpp"], bin "circe_vec_insert_native"),
   ("c++", ["-std=c++17", "tests/cpp/vec_erase_sum.cpp", "tests/diff/driver_vec_erase.cpp"], bin "circe_vec_erase_native"),
   ("c++", ["tests/cpp/vec_read_sum.cpp", "tests/diff/driver_vec_read.cpp"], bin "circe_vec_read_native"),
   ("cc", ["tests/c/sum_norestrict.c", "tests/diff/driver_sum_norestrict.c"], bin "circe_sum_norestrict_native")]

/-- Golden pairs `(tests/golden/X, out/X)`: every `diff -u` in `check.sh`. -/
def goldenPairs : List (String × String) :=
  [("tests/golden/Add.lean", "out/Add.lean"),
   ("tests/golden/Incr.lean", "out/Incr.lean"),
   ("tests/golden/Choose.lean", "out/Choose.lean"),
   ("tests/golden/SumArray.lean", "out/SumArray.lean"),
   ("tests/golden/AddCaller.lean", "out/AddCaller.lean"),
   ("tests/golden/SumCaller.lean", "out/SumCaller.lean"),
   ("tests/golden/StructByValue.lean", "out/StructByValue.lean"),
   ("tests/golden/NestedSum.lean", "out/NestedSum.lean"),
   ("tests/golden/SkipSum.lean", "out/SkipSum.lean"),
   ("tests/golden/FindEq.lean", "out/FindEq.lean"),
   ("tests/golden/Cls.lean", "out/Cls.lean"),
   ("tests/golden/ClsFall.lean", "out/ClsFall.lean"),
   ("tests/golden/ClsFall_Spec.lean", "out/ClsFall_Spec.lean"),
   ("tests/golden/ClsDense.lean", "out/ClsDense.lean"),
   ("tests/golden/ClsDense_Spec.lean", "out/ClsDense_Spec.lean"),
   ("tests/golden/ClsBreak.lean", "out/ClsBreak.lean"),
   ("tests/golden/ClsBreak_Spec.lean", "out/ClsBreak_Spec.lean"),
   ("tests/golden/ClsAdd.lean", "out/ClsAdd.lean"),
   ("tests/golden/ClsAdd_Spec.lean", "out/ClsAdd_Spec.lean"),
   ("tests/golden/Add64.lean", "out/Add64.lean"),
   ("tests/golden/Addu64.lean", "out/Addu64.lean"),
   ("tests/golden/Neg.lean", "out/Neg.lean"),
   ("tests/golden/Neg_Spec.lean", "out/Neg_Spec.lean"),
   ("tests/golden/Sdiv.lean", "out/Sdiv.lean"),
   ("tests/golden/Sdiv_Spec.lean", "out/Sdiv_Spec.lean"),
   ("tests/golden/XorU32.lean", "out/XorU32.lean"),
   ("tests/golden/XorU32_Spec.lean", "out/XorU32_Spec.lean"),
   ("tests/golden/AndU32.lean", "out/AndU32.lean"),
   ("tests/golden/AndU32_Spec.lean", "out/AndU32_Spec.lean"),
   ("tests/golden/OrU32.lean", "out/OrU32.lean"),
   ("tests/golden/OrU32_Spec.lean", "out/OrU32_Spec.lean"),
   ("tests/golden/ShlU32.lean", "out/ShlU32.lean"),
   ("tests/golden/ShlU32_Spec.lean", "out/ShlU32_Spec.lean"),
   ("tests/golden/ShrU32.lean", "out/ShrU32.lean"),
   ("tests/golden/ShrU32_Spec.lean", "out/ShrU32_Spec.lean"),
   ("tests/golden/VecAlloc.lean", "out/VecAlloc.lean"),
   ("tests/golden/VecCopySum.lean", "out/VecCopySum.lean"),
   ("tests/golden/VecAllocU64.lean", "out/VecAllocU64.lean"),
   ("tests/golden/VecRealloc.lean", "out/VecRealloc.lean"),
   ("tests/golden/MethodSum.lean", "out/MethodSum.lean"),
   ("tests/golden/PointSumRef.lean", "out/PointSumRef.lean"),
   ("tests/golden/AccCtor.lean", "out/AccCtor.lean"),
   ("tests/golden/AccAdd.lean", "out/AccAdd.lean"),
   ("tests/golden/AccGet.lean", "out/AccGet.lean"),
   ("tests/golden/AccDtor.lean", "out/AccDtor.lean"),
   ("tests/golden/AccTwo.lean", "out/AccTwo.lean"),
   ("tests/golden/BoxThrough.lean", "out/BoxThrough.lean"),
   ("tests/golden/SumNorestrict.lean", "out/SumNorestrict.lean"),
   ("tests/golden/OverloadAdd.lean", "out/OverloadAdd.lean"),
   ("tests/golden/Add3.lean", "out/Add3.lean"),
   ("tests/golden/UseAdd.lean", "out/UseAdd.lean"),
   ("tests/golden/NsAdd.lean", "out/NsAdd.lean"),
   ("tests/golden/UseNsAdd.lean", "out/UseNsAdd.lean"),
   ("tests/golden/MoveInt.lean", "out/MoveInt.lean"),
   ("tests/golden/MoveCtor.lean", "out/MoveCtor.lean"),
   ("tests/golden/MoveAcc.lean", "out/MoveAcc.lean"),
   ("tests/golden/ScopeEarly.lean", "out/ScopeEarly.lean"),
   ("tests/golden/Tadd32.lean", "out/Tadd32.lean"),
   ("tests/golden/Tadd64.lean", "out/Tadd64.lean"),
   ("tests/golden/UseTadd32.lean", "out/UseTadd32.lean"),
   ("tests/golden/UseTadd64.lean", "out/UseTadd64.lean"),
   ("tests/golden/ArrayRef.lean", "out/ArrayRef.lean"),
   ("tests/golden/ArrayAt.lean", "out/ArrayAt.lean"),
   ("tests/golden/ArraySum.lean", "out/ArraySum.lean"),
   ("tests/golden/ArrayRefU32.lean", "out/ArrayRefU32.lean"),
   ("tests/golden/ArrayAtU32.lean", "out/ArrayAtU32.lean"),
   ("tests/golden/InsertionSort.lean", "out/InsertionSort.lean"),
   ("tests/golden/ArraySortSum.lean", "out/ArraySortSum.lean"),
   ("tests/golden/ArrayRefU328.lean", "out/ArrayRefU328.lean"),
   ("tests/golden/ArrayAtU328.lean", "out/ArrayAtU328.lean"),
   ("tests/golden/InsertionSort8.lean", "out/InsertionSort8.lean"),
   ("tests/golden/ArraySortSum8.lean", "out/ArraySortSum8.lean"),
   ("tests/golden/OptHas.lean", "out/OptHas.lean"),
   ("tests/golden/OptHasValue.lean", "out/OptHasValue.lean"),
   ("tests/golden/OptGet.lean", "out/OptGet.lean"),
   ("tests/golden/OptImplGet.lean", "out/OptImplGet.lean"),
   ("tests/golden/OptDerefOp.lean", "out/OptDerefOp.lean"),
   ("tests/golden/OptDeref.lean", "out/OptDeref.lean"),
   ("tests/golden/SpanExtent.lean", "out/SpanExtent.lean"),
   ("tests/golden/SpanExtent_Spec.lean", "out/SpanExtent_Spec.lean"),
   ("tests/golden/SpanSize.lean", "out/SpanSize.lean"),
   ("tests/golden/SpanSize_Spec.lean", "out/SpanSize_Spec.lean"),
   ("tests/golden/SpanIndex.lean", "out/SpanIndex.lean"),
   ("tests/golden/SpanIndex_Spec.lean", "out/SpanIndex_Spec.lean"),
   ("tests/golden/SpanSum.lean", "out/SpanSum.lean"),
   ("tests/golden/SpanSum_Spec.lean", "out/SpanSum_Spec.lean"),
   ("tests/golden/ViewBegin.lean", "out/ViewBegin.lean"),
   ("tests/golden/ViewBegin_Spec.lean", "out/ViewBegin_Spec.lean"),
   ("tests/golden/ViewEnd.lean", "out/ViewEnd.lean"),
   ("tests/golden/ViewEnd_Spec.lean", "out/ViewEnd_Spec.lean"),
   ("tests/golden/ViewSum.lean", "out/ViewSum.lean"),
   ("tests/golden/ViewSum_Spec.lean", "out/ViewSum_Spec.lean"),
   ("tests/golden/VecSize.lean", "out/VecSize.lean"),
   ("tests/golden/VecSize_Spec.lean", "out/VecSize_Spec.lean"),
   ("tests/golden/VecIndex.lean", "out/VecIndex.lean"),
   ("tests/golden/VecIndex_Spec.lean", "out/VecIndex_Spec.lean"),
   ("tests/golden/VecReadSum.lean", "out/VecReadSum.lean"),
   ("tests/golden/VecReadSum_Spec.lean", "out/VecReadSum_Spec.lean"),
   ("tests/golden/VecGrowAlloc.lean", "out/VecGrowAlloc.lean"),
   ("tests/golden/VecGrowAlloc_Spec.lean", "out/VecGrowAlloc_Spec.lean"),
   ("tests/golden/VecGrowBack.lean", "out/VecGrowBack.lean"),
   ("tests/golden/VecGrowBack_Spec.lean", "out/VecGrowBack_Spec.lean"),
   ("tests/golden/VecGrowBegin.lean", "out/VecGrowBegin.lean"),
   ("tests/golden/VecGrowBegin_Spec.lean", "out/VecGrowBegin_Spec.lean"),
   ("tests/golden/VecGrowCheckLen.lean", "out/VecGrowCheckLen.lean"),
   ("tests/golden/VecGrowCheckLen_Spec.lean", "out/VecGrowCheckLen_Spec.lean"),
   ("tests/golden/VecGrowConstruct.lean", "out/VecGrowConstruct.lean"),
   ("tests/golden/VecGrowConstruct_Spec.lean", "out/VecGrowConstruct_Spec.lean"),
   ("tests/golden/VecGrowDealloc.lean", "out/VecGrowDealloc.lean"),
   ("tests/golden/VecGrowDealloc_Spec.lean", "out/VecGrowDealloc_Spec.lean"),
   ("tests/golden/VecGrowDeallocGuard.lean", "out/VecGrowDeallocGuard.lean"),
   ("tests/golden/VecGrowDeallocGuard_Spec.lean", "out/VecGrowDeallocGuard_Spec.lean"),
   ("tests/golden/VecGrowDestroyNoop.lean", "out/VecGrowDestroyNoop.lean"),
   ("tests/golden/VecGrowDestroyNoop_Spec.lean", "out/VecGrowDestroyNoop_Spec.lean"),
   ("tests/golden/VecGrowDestroyPtr.lean", "out/VecGrowDestroyPtr.lean"),
   ("tests/golden/VecGrowDestroyPtr_Spec.lean", "out/VecGrowDestroyPtr_Spec.lean"),
   ("tests/golden/VecGrowDiffMax.lean", "out/VecGrowDiffMax.lean"),
   ("tests/golden/VecGrowDiffMax_Spec.lean", "out/VecGrowDiffMax_Spec.lean"),
   ("tests/golden/VecGrowDtor.lean", "out/VecGrowDtor.lean"),
   ("tests/golden/VecGrowDtor_Spec.lean", "out/VecGrowDtor_Spec.lean"),
   ("tests/golden/VecGrowEmptyCtor.lean", "out/VecGrowEmptyCtor.lean"),
   ("tests/golden/VecGrowEmptyCtor_Spec.lean", "out/VecGrowEmptyCtor_Spec.lean"),
   ("tests/golden/VecGrowEnd.lean", "out/VecGrowEnd.lean"),
   ("tests/golden/VecGrowEnd_Spec.lean", "out/VecGrowEnd_Spec.lean"),
   ("tests/golden/VecGrowGetTp.lean", "out/VecGrowGetTp.lean"),
   ("tests/golden/VecGrowGetTp_Spec.lean", "out/VecGrowGetTp_Spec.lean"),
   ("tests/golden/VecGrowIterId.lean", "out/VecGrowIterId.lean"),
   ("tests/golden/VecGrowIterId_Spec.lean", "out/VecGrowIterId_Spec.lean"),
   ("tests/golden/VecGrowMax.lean", "out/VecGrowMax.lean"),
   ("tests/golden/VecGrowMax_Spec.lean", "out/VecGrowMax_Spec.lean"),
   ("tests/golden/VecGrowMin.lean", "out/VecGrowMin.lean"),
   ("tests/golden/VecGrowMin_Spec.lean", "out/VecGrowMin_Spec.lean"),
   ("tests/golden/VecGrowMinus.lean", "out/VecGrowMinus.lean"),
   ("tests/golden/VecGrowMinus_Spec.lean", "out/VecGrowMinus_Spec.lean"),
   ("tests/golden/VecGrowMinusEl.lean", "out/VecGrowMinusEl.lean"),
   ("tests/golden/VecGrowMinusEl_Spec.lean", "out/VecGrowMinusEl_Spec.lean"),
   ("tests/golden/VecGrowReloc.lean", "out/VecGrowReloc.lean"),
   ("tests/golden/VecGrowReloc_Spec.lean", "out/VecGrowReloc_Spec.lean"),
   ("tests/golden/VecGrowComposerRealloc.lean", "out/VecGrowComposerRealloc.lean"),
   ("tests/golden/VecGrowComposerRealloc_Spec.lean", "out/VecGrowComposerRealloc_Spec.lean"),
   ("tests/golden/VecGrowComposerEmplace.lean", "out/VecGrowComposerEmplace.lean"),
   ("tests/golden/VecGrowComposerEmplace_Spec.lean", "out/VecGrowComposerEmplace_Spec.lean"),
   ("tests/golden/VecGrowComposerPushBack.lean", "out/VecGrowComposerPushBack.lean"),
   ("tests/golden/VecGrowComposerPushBack_Spec.lean", "out/VecGrowComposerPushBack_Spec.lean"),
   ("tests/golden/VecGrowComposerEntry.lean", "out/VecGrowComposerEntry.lean"),
   ("tests/golden/VecGrowComposerEntry_Spec.lean", "out/VecGrowComposerEntry_Spec.lean"),
   ("tests/golden/VecGrowCapacity.lean", "out/VecGrowCapacity.lean"),
   ("tests/golden/VecGrowCapacity_Spec.lean", "out/VecGrowCapacity_Spec.lean"),
   ("tests/golden/VecGrowComposerReserve.lean", "out/VecGrowComposerReserve.lean"),
   ("tests/golden/VecGrowComposerReserve_Spec.lean", "out/VecGrowComposerReserve_Spec.lean"),
   ("tests/golden/VecGrowComposerReserveEntry.lean", "out/VecGrowComposerReserveEntry.lean"),
   ("tests/golden/VecGrowComposerReserveEntry_Spec.lean", "out/VecGrowComposerReserveEntry_Spec.lean"),
   ("tests/golden/VecGrowUnit.lean", "out/VecGrowUnit.lean"),
   ("tests/golden/VecGrowUnit_Spec.lean", "out/VecGrowUnit_Spec.lean"),]

/-- Emitted files `check.sh` typechecks individually (beyond the spec
    loop, which covers every `out/*_Spec.lean`). -/
def emittedTypechecks : List String :=
  ["out/Add.lean", "out/Incr.lean", "out/Choose.lean", "out/SumArray.lean",
   "out/AddCaller.lean", "out/SumCaller.lean", "out/StructByValue.lean",
   "out/NestedSum.lean", "out/SkipSum.lean", "out/FindEq.lean", "out/Cls.lean",
   "out/ClsFall.lean", "out/ClsDense.lean", "out/ClsBreak.lean",
   "out/ClsAdd.lean",
   "out/Add64.lean", "out/Addu64.lean",
   "out/Neg.lean", "out/Sdiv.lean",
   "out/XorU32.lean", "out/AndU32.lean", "out/OrU32.lean",
   "out/ShlU32.lean", "out/ShrU32.lean",
   "out/VecAlloc.lean",
   "out/VecCopySum.lean", "out/VecCopySum_Spec.lean",
   "out/VecAllocU64.lean", "out/VecAllocU64_Spec.lean",
   "out/VecRealloc.lean", "out/VecRealloc_Spec.lean",
   "out/MethodSum.lean", "out/PointSumRef.lean",
   "out/MethodSum_Spec.lean", "out/PointSumRef_Spec.lean",
   "out/AccCtor.lean", "out/AccAdd.lean", "out/AccGet.lean",
   "out/AccDtor.lean", "out/AccTwo.lean",
   "out/AccCtor_Spec.lean", "out/AccAdd_Spec.lean", "out/AccGet_Spec.lean",
   "out/AccDtor_Spec.lean", "out/AccTwo_Spec.lean",
   "out/BoxThrough.lean", "out/BoxThrough_Spec.lean",
   "out/SumNorestrict.lean", "out/SumNorestrict_Spec.lean",
   "out/OverloadAdd.lean", "out/OverloadAdd_Spec.lean",
   "out/Add3.lean", "out/Add3_Spec.lean",
   "out/UseAdd.lean", "out/UseAdd_Spec.lean",
   "out/NsAdd.lean", "out/NsAdd_Spec.lean",
   "out/UseNsAdd.lean", "out/UseNsAdd_Spec.lean",
   "out/MoveInt.lean", "out/MoveInt_Spec.lean",
   "out/MoveCtor.lean", "out/MoveCtor_Spec.lean",
   "out/MoveAcc.lean", "out/MoveAcc_Spec.lean",
   "out/ScopeEarly.lean", "out/ScopeEarly_Spec.lean",
   "out/Tadd32.lean", "out/Tadd32_Spec.lean",
   "out/Tadd64.lean", "out/Tadd64_Spec.lean",
   "out/UseTadd32.lean", "out/UseTadd32_Spec.lean",
   "out/UseTadd64.lean", "out/UseTadd64_Spec.lean",
   "out/ArrayRef.lean", "out/ArrayRef_Spec.lean",
   "out/ArrayAt.lean", "out/ArrayAt_Spec.lean",
   "out/ArraySum.lean", "out/ArraySum_Spec.lean",
   "out/ArrayRefU32.lean", "out/ArrayRefU32_Spec.lean",
   "out/ArrayAtU32.lean", "out/ArrayAtU32_Spec.lean",
   "out/InsertionSort.lean", "out/InsertionSort_Spec.lean",
   "out/ArraySortSum.lean", "out/ArraySortSum_Spec.lean",
   "out/ArrayRefU328.lean", "out/ArrayRefU328_Spec.lean",
   "out/ArrayAtU328.lean", "out/ArrayAtU328_Spec.lean",
   "out/InsertionSort8.lean", "out/InsertionSort8_Spec.lean",
   "out/ArraySortSum8.lean", "out/ArraySortSum8_Spec.lean",
   "out/OptHas.lean", "out/OptHas_Spec.lean",
   "out/OptHasValue.lean", "out/OptHasValue_Spec.lean",
   "out/OptGet.lean", "out/OptGet_Spec.lean",
   "out/OptImplGet.lean", "out/OptImplGet_Spec.lean",
   "out/OptDerefOp.lean", "out/OptDerefOp_Spec.lean",
   "out/OptDeref.lean", "out/OptDeref_Spec.lean",
   "out/SpanExtent.lean", "out/SpanExtent_Spec.lean",
   "out/SpanSize.lean", "out/SpanSize_Spec.lean",
   "out/SpanIndex.lean", "out/SpanIndex_Spec.lean",
   "out/SpanSum.lean", "out/SpanSum_Spec.lean",
   "out/ViewBegin.lean", "out/ViewBegin_Spec.lean",
   "out/ViewEnd.lean", "out/ViewEnd_Spec.lean",
   "out/ViewSum.lean", "out/ViewSum_Spec.lean",
   "out/VecSize.lean", "out/VecSize_Spec.lean",
   "out/VecIndex.lean", "out/VecIndex_Spec.lean",
   "out/VecReadSum.lean", "out/VecReadSum_Spec.lean",
   "out/VecGrowAlloc.lean", "out/VecGrowAlloc_Spec.lean",
   "out/VecGrowBack.lean", "out/VecGrowBack_Spec.lean",
   "out/VecGrowBegin.lean", "out/VecGrowBegin_Spec.lean",
   "out/VecGrowCheckLen.lean", "out/VecGrowCheckLen_Spec.lean",
   "out/VecGrowConstruct.lean", "out/VecGrowConstruct_Spec.lean",
   "out/VecGrowDealloc.lean", "out/VecGrowDealloc_Spec.lean",
   "out/VecGrowDeallocGuard.lean", "out/VecGrowDeallocGuard_Spec.lean",
   "out/VecGrowDestroyNoop.lean", "out/VecGrowDestroyNoop_Spec.lean",
   "out/VecGrowDestroyPtr.lean", "out/VecGrowDestroyPtr_Spec.lean",
   "out/VecGrowDiffMax.lean", "out/VecGrowDiffMax_Spec.lean",
   "out/VecGrowDtor.lean", "out/VecGrowDtor_Spec.lean",
   "out/VecGrowEmptyCtor.lean", "out/VecGrowEmptyCtor_Spec.lean",
   "out/VecGrowEnd.lean", "out/VecGrowEnd_Spec.lean",
   "out/VecGrowGetTp.lean", "out/VecGrowGetTp_Spec.lean",
   "out/VecGrowIterId.lean", "out/VecGrowIterId_Spec.lean",
   "out/VecGrowMax.lean", "out/VecGrowMax_Spec.lean",
   "out/VecGrowMin.lean", "out/VecGrowMin_Spec.lean",
   "out/VecGrowMinus.lean", "out/VecGrowMinus_Spec.lean",
   "out/VecGrowMinusEl.lean", "out/VecGrowMinusEl_Spec.lean",
   "out/VecGrowReloc.lean", "out/VecGrowReloc_Spec.lean",
   "out/VecGrowComposerRealloc.lean", "out/VecGrowComposerRealloc_Spec.lean",
   "out/VecGrowComposerEmplace.lean", "out/VecGrowComposerEmplace_Spec.lean",
   "out/VecGrowComposerPushBack.lean", "out/VecGrowComposerPushBack_Spec.lean",
   "out/VecGrowComposerEntry.lean", "out/VecGrowComposerEntry_Spec.lean",
   "out/VecGrowCapacity.lean", "out/VecGrowCapacity_Spec.lean",
   "out/VecGrowComposerReserve.lean", "out/VecGrowComposerReserve_Spec.lean",
   "out/VecGrowComposerReserveEntry.lean", "out/VecGrowComposerReserveEntry_Spec.lean",
   "out/VecGrowUnit.lean", "out/VecGrowUnit_Spec.lean",]

/-- Library modules `check.sh` typechecks (`lake build` covers
    elaboration; these pin the files individually like the harness). -/
def moduleTypechecks : List String :=
  ["Circe/Tactics.lean", "Circe/Specs.lean",
   "Circe/Mem.lean", "Circe/Transfer.lean",
   "Circe/Validator.lean", "Circe/Derived.lean",
   "Circe/ReadOnly.lean", "Circe/Scope.lean"]

/-- Content assertions `(file, fixed-string)`: every `grep -q[F]` in
    `check.sh` (all needles are regex-safe literals). Grouped to mirror
    the harness stages. -/
def contentAsserts : List (String × List (String × String)) :=
  [("phase5-bodies",
    [("out/Add.lean", "checkedAddI32 a b"),
     ("out/Incr.lean", "checkedIncrI32 p"),
     ("out/Choose.lean", ".ok (if b then x else y)"),
     ("out/Choose.lean", ".ok (if b then (ret, y) else (x, ret))"),
     ("out/SumArray.lean", "prefixSumU32 a.val a.val.length"),
     ("Circe/Specs.lean", "theorem incr_correct"),
     ("Circe/Specs.lean", "theorem choose_lens_laws"),
     ("Circe/Specs.lean", "theorem sum_correct"),
     ("Circe/Tactics.lean", "macro \"cir_simp\"")]),
   ("phase6-docs",
    [("docs/SUBSET.md", "vec_alloc"),
     -- NOTE: `tools/check-phase6.sh` is orphaned (nothing invokes it) and
     -- its `Stacked-Borrows` needle went stale when ROADMAP was reworded
     -- to `Stacked Borrows`. The live intent (docs pin the memory model)
     -- is preserved with the corrected needle. M3 (with its
     -- `Stacked Borrows` non-goal) moved to `DELIVERED.md` (2026-10-05).
     ("docs/DELIVERED.md", "Stacked Borrows"),
     ("docs/ROADMAP.md", "C++-lite"),
     ("docs/SUBSET.md", "cir.br")]),
   ("s1-bodies",
    [("out/AddCaller.lean", "checkedAddI32 x y"),
     ("out/AddCaller.lean", "checkedAddI32 t z"),
     ("out/SumCaller.lean", "prefixSumU32 a.val a.val.length")]),
   ("s2-body", [("out/StructByValue.lean", "pointTranslate p dx dy")]),
   ("s3a-bodies",
    [("out/NestedSum.lean", "nestedSumU32 n.toNat m.toNat"),
     ("out/SkipSum.lean", "skipSumU32 n.toNat"),
     ("out/FindEq.lean", "findEqOut a n.toNat k"),
     ("out/Cls.lean", "if x == 0 then .ok 10")]),
   ("s3b-bodies",
    [("out/Add64.lean", "checkedAddI64 a b"),
     ("out/Addu64.lean", ".ok (a + b)")]),
   ("n6a-arith",
    [("out/Neg.lean", "checkedNegI32 x"),
     ("out/Sdiv.lean", "checkedDivI32 a b"),
     ("tests/golden/Neg.lean", "neg_fwd"),
     ("tests/golden/Sdiv.lean", "sdiv_fwd"),
     ("tests/golden/Neg_Spec.lean", "neg_correct_ok"),
     ("tests/golden/Sdiv_Spec.lean", "sdiv_correct_zero"),
     ("Circe/CoreIR.lean", "| neg : CExpr"),
     ("Circe/CoreIR.lean", "| sdiv : CExpr"),
     ("Circe/Emit/Add.lean", "theorem emit_correct_neg"),
     ("Circe/Emit/Add.lean", "theorem emit_correct_sdiv"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_neg"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_sdiv"),
     ("Circe/Validator/Gate.lean", "def isNegShape"),
     ("Circe/Validator/Gate.lean", "def isSdivShape"),
     ("Circe/Validator/Gate.lean", "arithOpCount raw.text == 1"),
     ("Circe/Specs.lean", "theorem neg_correct_ok"),
     ("Circe/Specs.lean", "theorem neg_correct_err"),
     ("Circe/Specs.lean", "theorem sdiv_correct_ok"),
     ("Circe/Specs.lean", "theorem sdiv_correct_zero"),
     ("Circe/Specs.lean", "theorem sdiv_correct_overflow"),
     ("Circe/Tactics.lean", "checkedNegI32_ok, checkedNegI32_err"),
     ("Circe/Tactics.lean", "checkedDivI32_zero")]),
   ("k1-bitwise",
    [("out/XorU32.lean", ".ok (a ^^^ b)"),
     ("out/AndU32.lean", ".ok (a &&& b)"),
     ("out/OrU32.lean", ".ok (a ||| b)"),
     ("out/ShlU32.lean", "checkedShiftU32 a b"),
     ("out/ShrU32.lean", "checkedShiftU32 a b"),
     ("tests/golden/XorU32.lean", "xor_u32_fwd"),
     ("tests/golden/ShlU32.lean", "shl_u32_fwd"),
     ("tests/golden/XorU32_Spec.lean", "xorU32_correct"),
     ("tests/golden/ShlU32_Spec.lean", "shlU32_correct_ok"),
     ("tests/golden/ShrU32_Spec.lean", "shrU32_correct_err"),
     ("Circe/CoreIR.lean", "| bxor : CExpr"),
     ("Circe/CoreIR.lean", "| bshl : CExpr"),
     ("Circe/Emit/Bitwise.lean", "theorem emit_correct_xorU32"),
     ("Circe/Emit/Bitwise.lean", "theorem emit_correct_shlU32"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_xorU32"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_shrU32"),
     ("Circe/Validator/Gate.lean", "def isXorU32Shape"),
     ("Circe/Validator/Gate.lean", "def isShrU32Shape"),
     ("Circe/Validator/Gate.lean", "cir.shift(left"),
     ("Circe/Specs.lean", "theorem xorU32_correct"),
     ("Circe/Specs.lean", "theorem shlU32_correct_err"),
     ("Circe/Base.lean", "def checkedShiftU32")]),
   ("n6b-switch",
    [("out/ClsFall.lean", "else if x == 1 then .ok 10"),
     ("out/ClsDense.lean", "else if x == 7 then .ok 70"),
     ("tests/golden/ClsFall.lean", "cls_fall_fwd"),
     ("tests/golden/ClsDense.lean", "cls_dense_fwd"),
     ("tests/golden/ClsFall_Spec.lean", "cls_fall_spec_check"),
     ("tests/golden/ClsDense_Spec.lean", "cls_dense_spec_check"),
     ("Circe/Validator/Gate.lean", "def isClsFallShape"),
     ("Circe/Validator/Gate.lean", "def isClsDenseShape"),
     ("Circe/Validator/Gate.lean", "arithOpCount text == 0"),
     ("Circe/Emit/Flow.lean", "theorem evalFuncFuel_clsFall"),
     ("Circe/Emit/Flow.lean", "theorem evalFuncFuel_clsDense"),
     ("Circe/Emit/Match.lean", "theorem matchFrag_clsFall"),
     ("Circe/Emit/Match.lean", "theorem matchFrag_clsDense"),
     ("Circe/Specs.lean", "theorem clsFall_correct"),
     ("Circe/Specs.lean", "theorem clsDense_correct"),
     ("Circe/Tactics.lean", "clsFallFwd, clsDenseFwd,"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_clsFall"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_clsDense"),
     ("Circe/Derived.lean", "theorem oracleNoalias_clsFall"),
     ("Circe/Derived.lean", "theorem oracleNoalias_clsDense"),
     ("out/ClsBreak.lean", ".ok (if x == 0 then 10 else if x == 1 then 20 else 99)"),
     ("tests/golden/ClsBreak.lean", "cls_break_fwd"),
     ("tests/golden/ClsBreak_Spec.lean", "cls_break_spec_check"),
     ("Circe/Validator/Gate.lean", "def isClsBreakLowerableText"),
     ("Circe/Validator/Gate.lean", "def isClsBreakShape"),
     ("Circe/Emit/Flow.lean", "theorem evalFuncFuel_clsBreak"),
     ("Circe/Emit/Match.lean", "theorem matchFrag_clsBreak"),
     ("Circe/Specs.lean", "theorem clsBreak_correct"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_clsBreak"),
     ("Circe/Derived.lean", "theorem oracleNoalias_clsBreak"),
     ("out/ClsAdd.lean", ".ok (if x == 0 then y + 1 else if x == 1 then y + 2 else y)"),
     ("tests/golden/ClsAdd.lean", "cls_add_fwd"),
     ("tests/golden/ClsAdd_Spec.lean", "cls_add_spec_check"),
     ("Circe/Validator/Gate.lean", "def isClsAddLowerableText"),
     ("Circe/Validator/Gate.lean", "def isClsAddShape"),
     ("Circe/Emit/Flow.lean", "theorem evalFuncFuel_clsAdd"),
     ("Circe/Emit/Match.lean", "theorem matchFrag_clsAdd"),
     ("Circe/Specs.lean", "theorem clsAdd_correct"),
     ("Circe/Tactics.lean", "clsBreakFwd, clsAddFwd, add64Fwd"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_clsAdd"),
     ("Circe/Derived.lean", "theorem oracleNoalias_clsAdd")]),
   ("s4-cir-simp",
    [("Circe/Tactics.lean", "addCallerFwd_as_calls, sumCallerFwd_is_call"),
     ("Circe/Tactics.lean", "pointTranslate_ok, pointTranslate_err_x"),
     ("Circe/Tactics.lean", "checkedAddI64_ok, checkedAddI64_err"),
     ("Circe/Tactics.lean", "vecFillSumU32_correct"),
     ("Circe/Tactics.lean", "vecReallocFillSumU32_correct"),
     ("Circe/Tactics.lean", "vecFillSumU64_correct"),
     ("Circe/Tactics.lean", "result_bind_assoc, result_pure_bind"),
     ("Circe/Tactics.lean", "pointSum, pointSum_ok, pointSum_err, methodSumFwd_ok,"),
     ("Circe/Tactics.lean", "accTwo, accTwo_ok, accTwo_err_a, accTwo_err_b, accAddFwd_ok,"),
     ("Circe/Tactics.lean", "boxThrough, boxThrough_ok")]),
   ("s4-stub-contents",
    [("out/SumArray_Spec.lean", "_spec_fwd"),
     ("out/SumArray_Spec.lean", "_spec_edges"),
     ("out/SumArray_Spec.lean", "_spec_check"),
     ("out/SumArray_Spec.lean", "prefixSumU32")]),
   ("s5-helpers",
    [("Circe/Eval/Stmt.lean", "macro \"cir_fuel\""),
     ("Circe/Eval/Stmt.lean", "word32_lt_two32_of_fuel"),
     ("Circe/Emit/Choose.lean", "macro \"cir_choose\""),
     ("Circe/Emit/Sum.lean", "word32_lt_two32_of_fuel _ hfuel")]),
   ("m1a-body",
    [("out/VecCopySum.lean", "vecFillSumU32 n.toNat"),
     ("out/VecCopySum.lean", "vec_copy_sum_fwd")]),
   ("m1b-body",
    [("out/VecAllocU64.lean", "vecFillSumU64 n.toNat"),
     ("out/VecAllocU64.lean", "vec_alloc_u64_fwd")]),
   ("m1c-body",
    [("out/VecRealloc.lean", "vecReallocFillSumU32 n.toNat"),
     ("out/VecRealloc.lean", "vec_realloc_fwd")]),
   ("m2a-bodies",
    [("out/MethodSum.lean", "pointSum p"),
     ("out/PointSumRef.lean", "pointSum p")]),
   ("m2b-bodies",
    [("out/AccCtor.lean", ".ok accCtor"),
     ("out/AccAdd.lean", "accAdd s v"),
     ("out/AccGet.lean", "accGet s"),
     ("out/AccDtor.lean", "accDtor t"),
     ("out/AccTwo.lean", "accTwo a b")]),
   ("m2c-body", [("out/BoxThrough.lean", "boxThrough x")]),
   ("m3a-model",
    [("Circe/Mem/Agree.lean", "theorem memTransfer_add"),
     ("Circe/Mem/Agree.lean", "theorem memTransfer_incr"),
     ("Circe/Transfer/Core.lean", "theorem memTransfer_sum "),
     ("Circe/Transfer/Core.lean", "theorem memTransfer_sum_oob"),
     ("Circe/Transfer/VecLeaves.lean", "theorem memTransfer_vec "),
     ("Circe/Mem/Agree.lean", "def m3c_transfer_statement")]),
   ("m3b-derived",
    [("Circe/Validator/Gate.lean", "def derivedNoalias"),
     ("Circe/Validator/Gate.lean", "theorem derivedNoalias_all_noalias"),
     ("Circe/Validator/Gate.lean", "theorem derivedNoalias_admitted_c"),
     ("Circe/Derived.lean", "theorem oracleNoalias_choose"),
     ("Circe/Derived.lean", "theorem oracleNoalias_sumCaller"),
     ("Circe/Derived.lean", "theorem oracleNoalias_findEq"),
     ("Circe/Derived.lean", "theorem derived_bridge_noalias")]),
   ("m3c-loopfree",
    [("Circe/Transfer/Flow.lean", "theorem memTransfer_choose"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_add64"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_addu64"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_cls"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_clsFall"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_clsDense"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_clsBreak"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_clsAdd"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_translate"),
     ("Circe/Derived.lean", "theorem oracleNoalias_add64"),
     ("Circe/Derived.lean", "theorem oracleNoalias_addu64"),
     ("Circe/Derived.lean", "theorem oracleNoalias_cls"),
     ("Circe/Derived.lean", "theorem oracleNoalias_clsFall"),
     ("Circe/Derived.lean", "theorem oracleNoalias_clsDense"),
     ("Circe/Derived.lean", "theorem oracleNoalias_clsBreak"),
     ("Circe/Derived.lean", "theorem oracleNoalias_clsAdd"),
     ("Circe/Derived.lean", "theorem oracleNoalias_translate"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_add_fget_var")]),
   ("m3c-flow",
    [("Circe/Transfer/Flow.lean", "theorem memTransfer_nested"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_skip"),
     ("Circe/Transfer/Flow.lean", "theorem memTransfer_findEq"),
     ("Circe/Transfer/Flow.lean", "theorem memNestedOuter_correct"),
     ("Circe/Transfer/Flow.lean", "theorem memSkipWhile_correct"),
     ("Circe/Transfer/Flow.lean", "theorem memFindWhile_some"),
     ("Circe/Transfer/Flow.lean", "theorem memFindWhile_none"),
     ("Circe/Derived.lean", "theorem oracleNoalias_nested"),
     ("Circe/Derived.lean", "theorem oracleNoalias_skip")]),
   ("m3c-caller",
    [("Circe/Transfer/Flow.lean", "theorem memEvalProgFunc_addCaller"),
     ("Circe/Transfer/Flow.lean", "theorem memTransferProg_addCaller"),
     ("Circe/Transfer/Flow.lean", "theorem memEvalProgFunc_sumCaller"),
     ("Circe/Transfer/Flow.lean", "theorem memTransferProg_sumCaller"),
     ("Circe/Mem/Model.lean", "def memEvalProgStmt"),
     ("Circe/Mem/Model.lean", "def memEvalProgFunc"),
     ("Circe/Mem/Model.lean", "theorem memEvalProgStmt_callRet_ok"),
     ("Circe/Mem/Model.lean", "theorem memEvalProgStmt_callRet_err")]),
   ("m3c-vec2",
    [("Circe/Transfer/VecLeaves.lean", "theorem memVec2FillWhile_correct"),
     ("Circe/Transfer/VecLeaves.lean", "theorem memVec2CopyWhile_correct"),
     ("Circe/Transfer/VecLeaves.lean", "theorem memVec2SumWhile_correct"),
     ("Circe/Transfer/VecLeaves.lean", "theorem memEvalFuncFuel_vec2"),
     ("Circe/Transfer/VecLeaves.lean", "theorem memTransfer_vec2"),
     ("Circe/Derived.lean", "theorem oracleNoalias_vec2"),
     ("Circe/Mem/Agree.lean", "theorem memFind_memStore_other"),
     ("Circe/Mem/Agree.lean", "theorem memFind_memFree_other")]),
   ("m3c-vecrealloc",
    [("Circe/Mem/Model.lean", "def memRealloc"),
     ("Circe/Mem/Agree.lean", "theorem vrealloc_lockstep"),
     ("Circe/Mem/Agree.lean", "theorem memEvalStmtFuel_vrealloc"),
     ("Circe/Transfer/VecHeap.lean", "theorem memVecReallocFillWhile_correct"),
     ("Circe/Transfer/VecHeap.lean", "theorem memVecReallocExtWhile_correct"),
     ("Circe/Transfer/VecHeap.lean", "theorem memVecReallocSumWhile_correct"),
     ("Circe/Transfer/VecHeap.lean", "theorem memVecReallocStep_eval"),
     ("Circe/Transfer/VecHeap.lean", "theorem memEvalFuncFuel_vecRealloc"),
     ("Circe/Transfer/VecHeap.lean", "theorem memTransfer_vecRealloc"),
     ("Circe/Derived.lean", "theorem oracleNoalias_vecRealloc")]),
   ("m3c-vec64",
    [("Circe/Mem/Model.lean", "structure Block64"),
     ("Circe/Mem/Model.lean", "def memFind64"),
     ("Circe/Mem/Model.lean", "def memAllocData64"),
     ("Circe/Mem/Model.lean", "def memLoad64"),
     ("Circe/Mem/Model.lean", "def memStore64"),
     ("Circe/Mem/Model.lean", "def memFree64"),
     ("Circe/Mem/Agree.lean", "theorem vset64_lockstep"),
     ("Circe/Mem/Agree.lean", "theorem vfree64_lockstep"),
     ("Circe/Mem/Agree.lean", "theorem memEvalStmtFuel_let_vnew64"),
     ("Circe/Transfer/VecHeap.lean", "theorem memVec64FillWhile_correct"),
     ("Circe/Transfer/VecHeap.lean", "theorem memVec64SumWhile_correct"),
     ("Circe/Transfer/VecHeap.lean", "theorem memEvalFuncFuel_vec64"),
     ("Circe/Transfer/VecHeap.lean", "theorem memTransfer_vec64"),
     ("Circe/Derived.lean", "theorem oracleNoalias_vec64")]),
   ("m3d-cpp",
    [("Circe/Mem/Model.lean", "theorem memEvalProgStmt_cleanup"),
     ("Circe/Mem/Agree.lean", "theorem memEvalStmtFuel_let_boxNew"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_boxGet_hit"),
     ("Circe/Mem/Agree.lean", "theorem vboxFree_lockstep"),
     ("Circe/Mem/Agree.lean", "theorem memEvalStmtFuel_boxFree"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_methodSum"),
     ("Circe/Transfer/Slice.lean", "theorem memTransfer_methodSum"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalProgFunc_pointSumRef"),
     ("Circe/Transfer/Slice.lean", "theorem memTransferProg_pointSumRef"),
     ("Circe/Transfer/Acc.lean", "theorem memEvalFuncFuel_accCtor"),
     ("Circe/Transfer/Acc.lean", "theorem memTransfer_accAdd"),
     ("Circe/Transfer/Acc.lean", "theorem memTransfer_accGet"),
     ("Circe/Transfer/Acc.lean", "theorem memTransfer_accDtor"),
     ("Circe/Transfer/Acc.lean", "theorem memEvalProgFunc_accTwo"),
     ("Circe/Transfer/Acc.lean", "theorem memTransferProg_accTwo"),
     ("Circe/Transfer/Acc.lean", "theorem memEvalFuncFuel_boxThrough"),
     ("Circe/Transfer/Acc.lean", "theorem memTransfer_boxThrough"),
     ("Circe/Derived.lean", "theorem oracleNoalias_methodSum"),
     ("Circe/Derived.lean", "theorem oracleNoalias_pointSumRef"),
     ("Circe/Derived.lean", "theorem oracleNoalias_accTwo"),
     ("Circe/Derived.lean", "theorem oracleNoalias_boxThrough")]),
   ("n2a-discipline",
    [("Circe/ReadOnly.lean", "def IsReadOnlyParams"),
     ("Circe/ReadOnly.lean", "theorem hasWriter_not_readOnly"),
     ("Circe/ReadOnly.lean", "theorem writer_reader_excluded"),
     ("Circe/ReadOnly.lean", "theorem twoReaderParams_readOnly"),
     ("Circe/ReadOnly.lean", "theorem bindMemArgs_twoShared"),
     ("Circe/ReadOnly.lean", "theorem twoShared_noalias"),
     ("Circe/ReadOnly.lean", "theorem twoShared_consistent"),
     ("Circe/ReadOnly.lean", "theorem twoShared_alias_sound")]),
   ("n2b-catalog",
    [("Circe/Validator/Gate.lean", "writer+reader"),
     ("Circe/Validator/Gate.lean", "escaping-borrow"),
     ("Circe/Validator/Gate.lean", "borrow-after-free")]),
   ("n2c-recovery",
    [("Circe/Validator/Gate.lean", "def recoveredNoalias"),
     ("Circe/Validator/Gate.lean", "theorem recoveredNoalias_admitted_reader"),
     ("Circe/Validator/Gate.lean", "theorem recoveredNoalias_single_oracle"),
     ("Circe/Validator/Gate.lean", "def isRecoveredParam"),
     ("out/SumNorestrict.lean", "prefixSumU32 a.val a.val.length")]),
   ("l1-scope",
    [("Circe/Scope.lean", "def extractScopes"),
     ("Circe/Scope.lean", "theorem extractScopes_empty"),
     ("Circe/Scope.lean", "theorem extractScopes_bound")]),
   ("n4a-overload",
    [("Circe/Validator/Shapes.lean", "def isAdd3Shape"),
     ("Circe/Validator/Shapes.lean", "def isOverloadCallerShape"),
     ("Circe/Validator/Shapes.lean", "def overloadLeafCallees"),
     ("Circe/Validator/Gate.lean", "calls a known overload leaf"),
     ("Circe/Emit/Match.lean", "some .add3"),
     ("Circe/Emit/Match.lean", "some .useNsAdd"),
     ("Circe/Emit/Add.lean", "theorem evalFuncFuel_add3"),
     ("Circe/Emit/Calls.lean", "theorem evalProgFunc_useNsAdd"),
     ("Circe/Transfer/Flow.lean", "theorem memEvalFuncFuel_add3"),
     ("Circe/Transfer/Flow.lean", "theorem memTransferProg_useAdd"),
     ("Circe/Derived.lean", "theorem oracleNoalias_useNsAdd"),
     ("Circe/Mem/Agree.lean", "theorem memEvalStmtFuel_seq_fallthrough"),
     ("out/UseAdd.lean", "_Z7use_addii_fwd"),
     ("tests/golden/UseNsAdd.lean", "_Z10use_ns_addii_fwd")]),
   ("n4c-tadd",
    [("Circe/Validator/Shapes.lean", "def templateLeafCallees"),
     ("Circe/Validator/Shapes.lean", "def isOverloadCaller64Shape"),
     ("Circe/Validator/Gate.lean", "calls a known template-instantiation leaf"),
     ("Circe/Emit/Match.lean", "some .useTadd32"),
     ("Circe/Emit/Match.lean", "some .useTadd64"),
     ("Circe/Emit/Add.lean", "theorem evalFuncFuel_add64At"),
     ("Circe/Emit/Calls.lean", "theorem evalProgFunc_useTadd64"),
     ("Circe/Transfer/Flow.lean", "theorem memEvalFuncFuel_add64At"),
     ("Circe/Transfer/Flow.lean", "theorem memTransferProg_useTadd32"),
     ("Circe/Derived.lean", "theorem oracleNoalias_useTadd64"),
     ("out/UseTadd32.lean", "_Z10use_tadd32ii_fwd"),
     ("tests/golden/UseTadd64.lean", "_Z10use_tadd64ll_fwd")]),
   ("n4d-array",
    [("Circe/Validator/Shapes.lean", "def isArrayRefShape"),
     ("Circe/Validator/Shapes.lean", "def isArrayAtShape"),
     ("Circe/Validator/Shapes.lean", "def isArraySumShape"),
     ("Circe/Validator/Shapes.lean", "def arrayLeafCallees"),
     ("Circe/Validator/Gate.lean", "calls a known `std::array` leaf"),
     ("Circe/Emit/Match.lean", "some .arrayRef"),
     ("Circe/Emit/Match.lean", "some .arrayAt"),
     ("Circe/Emit/Match.lean", "some .arraySum"),
     ("Circe/Emit/Array.lean", "theorem evalFuncFuel_arrayRef"),
     ("Circe/Emit/Array.lean", "theorem evalFuncFuel_arrayAt"),
     ("Circe/Emit/Array.lean", "theorem evalProgFunc_arraySum"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_arrayRef"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_arrayAt"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalProgFunc_arraySum"),
     ("Circe/Transfer/Slice.lean", "theorem memTransferProg_arraySum"),
     ("Circe/Derived.lean", "theorem oracleNoalias_arrayRef"),
     ("Circe/Derived.lean", "theorem oracleNoalias_arraySum"),
     ("Circe/Specs.lean", "theorem arrayRef_correct_hit"),
     ("Circe/Specs.lean", "theorem arrayAt_correct"),
     ("Circe/Specs.lean", "theorem arraySum_correct_ok"),
     ("Circe/Specs.lean", "theorem arraySum_correct_err_c"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_idxi_hit"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_idxi_oob"),
     ("out/ArraySum.lean", "_Z9array_sumRKSt5arrayIiLm4EE_fwd"),
     ("tests/golden/ArrayRef.lean", "_S_refERA4_Kim_fwd")]),
   ("n9-arraysort",
    [("Circe/Validator/Shapes.lean", "def isArrayRefU32Shape"),
     ("Circe/Validator/Shapes.lean", "def isArrayAtU32Shape"),
     ("Circe/Validator/Shapes.lean", "def isInsertionSortShape"),
     ("Circe/Validator/Shapes.lean", "def isArraySortSumShape"),
     ("Circe/Emit/Match.lean", "some .arrayRefU32"),
     ("Circe/Emit/Match.lean", "some .arrayAtU32"),
     ("Circe/Emit/Match.lean", "some .insertionSort"),
     ("Circe/Emit/Match.lean", "some .arraySortSum"),
     ("Circe/Emit/Match.lean", "theorem matchFrag_arrayRefU32"),
     ("Circe/Emit/Match.lean", "theorem matchFrag_arrayAtU32"),
     ("Circe/Emit/Match.lean", "theorem matchFrag_insertionSort"),
     ("Circe/Emit/Match.lean", "theorem matchFrag_arraySortSum"),
     ("Circe/Emit/ArraySort.lean", "def arrayRefU32Fwd"),
     ("Circe/Emit/ArraySort.lean", "def insertionSortFwd"),
     ("Circe/Emit/ArraySort.lean", "def arraySortSumEntryFwd"),
     ("out/ArraySortSum.lean", "_Z14array_sort_sumv_fwd"),
     ("out/InsertionSort.lean", "_Z14insertion_sortRSt5arrayIjLm4EE_fwd"),
     ("tests/golden/ArraySortSum.lean", "_Z14array_sort_sumv_fwd"),
     ("tests/golden/InsertionSort.lean", "_Z14insertion_sortRSt5arrayIjLm4EE_fwd")]),
  ("n9b-arraysort",
   [("Circe/Validator/Shapes.lean", "def isArrayRefU32Shape"),
    ("Circe/Validator/Shapes.lean", "def isArrayAtU32_8Shape"),
    ("Circe/Validator/Shapes.lean", "def isInsertionSort8Shape"),
    ("Circe/Validator/Shapes.lean", "def isArraySortSum8Shape"),
    ("Circe/Emit/Match.lean", "some .arraySortSum"),
    ("Circe/Emit/Match.lean", "theorem matchFrag_insertionSort8"),
    ("Circe/Emit/Match.lean", "theorem matchFrag_arraySortSum8"),
    ("Circe/Emit/ArraySort.lean", "def arrayRefU32Fwd"),
    ("Circe/Emit/ArraySort.lean", "def insertionSortFwd"),
    ("Circe/Emit/ArraySort8.lean", "def arraySortSum8EntryFunc"),
    ("Circe/Emit/ArraySort8.lean", "theorem evalProgFunc_arraySortSum8Entry"),
    ("out/ArraySortSum8.lean", "_Z15array_sort_sum8v_fwd"),
    ("out/InsertionSort8.lean", "_Z15insertion_sort8RSt5arrayIjLm8EE_fwd"),
    ("tests/golden/ArraySortSum8.lean", "_Z15array_sort_sum8v_fwd"),
    ("tests/golden/InsertionSort8.lean", "_Z15insertion_sort8RSt5arrayIjLm8EE_fwd")]),
   ("n4d-optional",
    [("Circe/Validator/Shapes.lean", "def isOptHasShape"),
     ("Circe/Validator/Shapes.lean", "def isOptGetShape"),
     ("Circe/Validator/Shapes.lean", "def isOptHasValueShape"),
     ("Circe/Validator/Shapes.lean", "def isOptImplGetShape"),
     ("Circe/Validator/Shapes.lean", "def isOptDerefOpShape"),
     ("Circe/Validator/Shapes.lean", "def isOptDerefShape"),
     ("Circe/Validator/Shapes.lean", "def optLeafCallees"),
     ("Circe/Validator/Gate.lean", "calls a known `std::optional` leaf"),
     ("Circe/Emit/Match.lean", "some .optHas"),
     ("Circe/Emit/Match.lean", "some .optHasValue"),
     ("Circe/Emit/Match.lean", "some .optGet"),
     ("Circe/Emit/Match.lean", "some .optImplGet"),
     ("Circe/Emit/Match.lean", "some .optDerefOp"),
     ("Circe/Emit/Match.lean", "some .optDeref"),
     ("Circe/Emit/Optional.lean", "theorem evalFuncFuel_optHas"),
     ("Circe/Emit/Optional.lean", "theorem evalFuncFuel_optHasValue"),
     ("Circe/Emit/Optional.lean", "theorem evalFuncFuel_optGet"),
     ("Circe/Emit/Optional.lean", "theorem evalFuncFuel_optDerefOp"),
     ("Circe/Emit/Optional.lean", "theorem evalProgFunc_optImplGet"),
     ("Circe/Emit/Optional.lean", "theorem evalProgFunc_optDeref"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_optHas_some"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_optHas_none"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_optGet_some"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_optGet_none"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalProgFunc_optImplGet"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalProgFunc_optDeref"),
     ("Circe/Transfer/Slice.lean", "theorem memTransferProg_optImplGet"),
     ("Circe/Transfer/Slice.lean", "theorem memTransferProg_optDeref"),
     ("Circe/Derived.lean", "theorem bindMemArgs_optVal"),
     ("Circe/Derived.lean", "theorem oracleNoalias_optHas"),
     ("Circe/Derived.lean", "theorem oracleNoalias_optDeref"),
     ("Circe/Specs.lean", "theorem optHas_correct"),
     ("Circe/Specs.lean", "theorem optHasValue_correct"),
     ("Circe/Specs.lean", "theorem optGet_correct_some"),
     ("Circe/Specs.lean", "theorem optGet_correct_none"),
     ("Circe/Specs.lean", "theorem optDerefOp_correct"),
     ("Circe/Specs.lean", "theorem optDeref_correct_some"),
     ("Circe/Specs.lean", "theorem optDeref_correct_none"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_optHas_hit"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_optGet_hit"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_optGet_oob"),
     ("Circe/Eval/Core.lean", "theorem evalExpr_optHas_some"),
     ("Circe/Eval/Core.lean", "theorem evalExpr_optGet_none"),
     ("out/OptDeref.lean", "_Z9opt_derefRKSt8optionalIiE_fwd"),
     ("tests/golden/OptHas.lean", "_M_is_engagedEv_fwd")]),
   ("n4d-span",
    [("Circe/Validator/Shapes.lean", "def isSpanExtentShape"),
     ("Circe/Validator/Shapes.lean", "def isSpanSizeShape"),
     ("Circe/Validator/Shapes.lean", "def isSpanIndexShape"),
     ("Circe/Validator/Shapes.lean", "def isSpanSumShape"),
     ("Circe/Validator/Shapes.lean", "def spanLeafCallees"),
     ("Circe/Validator/Gate.lean", "calls a known `std::span` leaf"),
     ("Circe/Emit/Match.lean", "some .spanExtent"),
     ("Circe/Emit/Match.lean", "some .spanSize"),
     ("Circe/Emit/Match.lean", "some .spanIndex"),
     ("Circe/Emit/Match.lean", "some .spanSum"),
     ("Circe/Emit/Span.lean", "theorem evalFuncFuel_spanSum"),
     ("Circe/Emit/Span.lean", "theorem spanWhile_correct"),
     ("Circe/Emit/Span.lean", "theorem evalFuncFuel_spanIndex"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_spanSum"),
     ("Circe/Transfer/Slice.lean", "theorem memSpanWhile_correct"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_spanIndex_hit"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_spanIndex_oob"),
     ("Circe/Derived.lean", "theorem bindMemArgs_spanVal"),
     ("Circe/Derived.lean", "theorem oracleNoalias_spanSum"),
     ("Circe/Specs.lean", "theorem spanSum_correct_cons"),
     ("Circe/Specs.lean", "theorem spanSum_correct_cons_err"),
     ("Circe/Specs.lean", "theorem spanIndex_correct_oob"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_spanAt_oob"),
     ("Circe/Eval/Core.lean", "theorem evalExpr_spanAt_oob"),
     ("out/SpanSum.lean", "_Z8span_sumSt4spanIKiLm18446744073709551615EE_fwd"),
     ("tests/golden/SpanExtent.lean", "_M_extentEv_fwd")]),
   ("n7a-view",
    [("Circe/Validator/Shapes.lean", "def isViewBeginShape"),
     ("Circe/Validator/Shapes.lean", "def isViewEndShape"),
     ("Circe/Validator/Shapes.lean", "def isViewSumShape"),
     ("Circe/Validator/Shapes.lean", "def viewLeafCallees"),
     ("Circe/Validator/Gate.lean", "calls a known `std::string_view` leaf"),
     ("Circe/Emit/Match.lean", "some .viewBegin"),
     ("Circe/Emit/Match.lean", "some .viewEnd"),
     ("Circe/Emit/Match.lean", "some .viewSum"),
     ("Circe/Emit/View.lean", "theorem evalFuncFuel_viewSum"),
     ("Circe/Emit/View.lean", "theorem viewWhile_correct"),
     ("Circe/Emit/View.lean", "theorem evalFuncFuel_viewEnd"),
     ("Circe/Emit/View.lean", "theorem evalFuncFuel_viewBegin"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_viewSum"),
     ("Circe/Transfer/Slice.lean", "theorem memViewWhile_correct"),
     ("Circe/Transfer/Slice.lean", "theorem memTransfer_viewSum"),
     ("Circe/Derived.lean", "theorem bindMemArgs_viewVal"),
     ("Circe/Derived.lean", "theorem oracleNoalias_viewSum"),
     ("Circe/Specs.lean", "theorem viewSum_correct_cons"),
     ("Circe/Specs.lean", "theorem viewSum_correct_cons_err"),
     ("Circe/Specs.lean", "theorem viewEnd_correct"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_viewAt_oob"),
     ("Circe/Eval/Core.lean", "theorem evalExpr_viewAt_oob"),
     ("Circe/Eval/Core.lean", "theorem evalExpr_viewAt_some"),
     ("out/ViewSum.lean", "_Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE_fwd"),
     ("tests/golden/ViewBegin.lean", "_ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv_fwd")]),
   ("n7b-reserve",
    [("Circe/Validator/Shapes.lean", "def isStdVecGrowCapacityShape"),
     ("Circe/Validator/GrowLeaves.lean", "def isStdVecReserveShape"),
     ("Circe/Validator/GrowLeaves.lean", "def isVecReserveSumEntryShape"),
     ("Circe/Validator/Gate.lean", "calls a known `std::vector` leaf"),
     ("Circe/Emit/Match.lean", "some .vecCapacity"),
     ("Circe/Emit/Match.lean", "some .vecReserve"),
     ("Circe/Emit/Match.lean", "some .vecReserveSumEntry"),
     ("Circe/Emit/Match.lean", "theorem matchFrag_stdVecReserve"),
     ("Circe/Emit/VecCompose/Reserve.lean", "theorem evalProgFunc_stdVecReserve"),
     ("Circe/Emit/VecCompose/Reserve.lean", "theorem evalProgFunc_vecReserveSumEntry"),
     ("Circe/Transfer/GrowReserve.lean", "theorem memEvalProgFunc_stdVecReserve"),
     ("Circe/Transfer/GrowReserve.lean", "theorem memTransfer_stdVecReserve"),
     ("Circe/Transfer/GrowReserve.lean", "theorem memEvalProgFunc_vecReserveSumEntry"),
     ("Circe/Transfer/GrowReserve.lean", "theorem memTransfer_vecReserveSumEntry"),
     ("Circe/Transfer/GrowLeaves.lean", "theorem memTransfer_stdVecGrowCapacity"),
     ("Circe/Derived.lean", "theorem bindMemArgs_stdVecReserve"),
     ("Circe/Derived.lean", "theorem oracleNoalias_vecReserveSumEntry"),
     ("Circe/Specs.lean", "theorem stdVecReserve_correct_realloc"),
     ("Circe/Specs.lean", "theorem vecReserveSumEntry_correct"),
     ("Circe/Specs.lean", "theorem stdVecGrowCapacity_correct"),
     ("out/VecGrowComposerReserve.lean", "_ZNSt6vectorIiSaIiEE7reserveEm_fwd"),
     ("tests/golden/VecGrowCapacity.lean", "_ZNKSt6vectorIiSaIiEE8capacityEv_fwd")]),
   ("n4d-vecread",
    [("Circe/Validator/Shapes.lean", "def isStdVecSizeShape"),
     ("Circe/Validator/Shapes.lean", "def isStdVecIndexShape"),
     ("Circe/Validator/Shapes.lean", "def isStdVecReadSumShape"),
     ("Circe/Validator/GrowLeaves.lean", "def stdVecLeafCallees"),
     ("Circe/Validator/Gate.lean", "calls a known `std::vector` leaf"),
     ("Circe/Emit/Match.lean", "some .vecSize"),
     ("Circe/Emit/Match.lean", "some .vecIndex"),
     ("Circe/Emit/Match.lean", "some .vecReadSum"),
     ("Circe/Emit/VecRead.lean", "theorem evalFuncFuel_stdVecReadSum"),
     ("Circe/Emit/VecRead.lean", "theorem stdVecWhile_correct"),
     ("Circe/Emit/VecRead.lean", "theorem evalFuncFuel_stdVecIndex"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_stdVecReadSum"),
     ("Circe/Transfer/Slice.lean", "theorem memStdVecWhile_correct"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_stdVecIndex_hit"),
     ("Circe/Transfer/Slice.lean", "theorem memEvalFuncFuel_stdVecIndex_oob"),
     ("Circe/Derived.lean", "theorem bindMemArgs_stdVecVal"),
     ("Circe/Derived.lean", "theorem oracleNoalias_stdVecReadSum"),
     ("Circe/Specs.lean", "theorem stdVecReadSum_correct_cons"),
     ("Circe/Specs.lean", "theorem stdVecReadSum_correct_cons_err"),
     ("Circe/Specs.lean", "theorem stdVecIndex_correct_oob"),
     ("Circe/Mem/Model.lean", "theorem memEvalExpr_stdVecAt_oob"),
     ("Circe/Eval/Core.lean", "theorem evalExpr_stdVecAt_oob"),
     ("out/VecReadSum.lean", "_Z12vec_read_sumRKSt6vectorIiSaIiEE_fwd"),
     ("tests/golden/VecSize.lean", "_ZNKSt6vectorIiSaIiEE4sizeEv_fwd")]),
   ("n4d-vecgrow",
    [("Circe/Validator/GrowLeaves.lean", "def isVecGrowComposerText"),
     ("Circe/Validator/Gate.lean", "N4d-iv-b2 growth composer"),
     ("Circe/Emit/VecGrow/B.lean", "theorem evalFuncFuel_stdVecReloc"),
     ("Circe/Emit/VecGrow/B.lean", "theorem stdVecRelocWhile_correct"),
     ("Circe/Transfer/GrowReloc.lean", "theorem memStdVecRelocWhile_correct"),
     ("Circe/Transfer/GrowReloc.lean", "theorem memTransfer_stdVecReloc"),
     ("Circe/Derived.lean", "theorem bindMemArgs_stdVecReloc"),
     ("Circe/Derived.lean", "theorem oracleNoalias_stdVecReloc"),
     ("Circe/Specs.lean", "theorem stdVecReloc_correct_nil"),
     ("Circe/Specs.lean", "theorem stdVecGrowRealloc_correct_ok"),
     ("Circe/Specs.lean", "theorem stdVecGrowRealloc_correct_err_checklen"),
     ("Circe/Emit/VecCompose/Realloc.lean", "theorem evalProgFunc_stdVecGrowRealloc"),
     ("Circe/Transfer/GrowRealloc.lean", "theorem memEvalProgFunc_stdVecGrowRealloc"),
     ("Circe/Transfer/GrowRealloc.lean", "theorem memTransfer_stdVecGrowRealloc"),
     ("Circe/Derived.lean", "theorem bindMemArgs_stdVecGrowRealloc"),
     ("Circe/Derived.lean", "theorem oracleNoalias_stdVecGrowRealloc"),
     ("Circe/Validator/GrowLeaves.lean", "def isStdVecReallocInsertShape"),
     ("out/VecGrowComposerRealloc.lean", "_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT__fwd"),
     ("Circe/Specs.lean", "theorem stdVecEmplaceBack_correct_slow"),
     ("Circe/Specs.lean", "theorem stdVecEmplaceBack_correct_fast"),
     ("Circe/Specs.lean", "theorem stdVecEmplaceBack_correct_err_checklen"),
     ("Circe/Specs.lean", "theorem stdVecEmplaceBack_correct_ok_slow"),
     ("Circe/Specs.lean", "theorem stdVecEmplaceBack_correct_err_construct"),
     ("Circe/Specs.lean", "theorem stdVecEmplaceBack_correct_ok_fast"),
     ("Circe/Emit/VecCompose/Emplace.lean", "theorem evalProgFunc_stdVecEmplaceBack"),
     ("Circe/Transfer/GrowEmplace.lean", "theorem memEvalProgFunc_stdVecEmplaceBack"),
     ("Circe/Transfer/GrowEmplace.lean", "theorem memTransfer_stdVecEmplaceBack"),
     ("Circe/Derived.lean", "theorem bindMemArgs_stdVecEmplaceBack"),
     ("Circe/Derived.lean", "theorem oracleNoalias_stdVecEmplaceBack"),
     ("Circe/Validator/GrowLeaves.lean", "def isStdVecEmplaceBackShape"),
     ("out/VecGrowComposerEmplace.lean", "_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT__fwd"),
     ("Circe/Specs.lean", "theorem stdVecPushBack_correct_slow"),
     ("Circe/Specs.lean", "theorem stdVecPushBack_correct_fast"),
     ("Circe/Specs.lean", "theorem stdVecPushBack_correct_err_checklen"),
     ("Circe/Specs.lean", "theorem stdVecPushBack_correct_ok_slow"),
     ("Circe/Specs.lean", "theorem stdVecPushBack_correct_err_construct"),
     ("Circe/Specs.lean", "theorem stdVecPushBack_correct_ok_fast"),
     ("Circe/Emit/VecCompose/Emplace.lean", "theorem evalProgFunc_stdVecPushBack"),
     ("Circe/Emit/VecCompose/Emplace.lean", "theorem findFunc_stdVecEmplaceBack"),
     ("Circe/Transfer/GrowEmplace.lean", "theorem memEvalProgFunc_stdVecPushBack"),
     ("Circe/Transfer/GrowEmplace.lean", "theorem memTransfer_stdVecPushBack"),
     ("Circe/Derived.lean", "theorem bindMemArgs_stdVecPushBack"),
     ("Circe/Derived.lean", "theorem oracleNoalias_stdVecPushBack"),
     ("Circe/Validator/GrowLeaves.lean", "def isStdVecPushBackShape"),
     ("out/VecGrowComposerPushBack.lean", "_ZNSt6vectorIiSaIiEE9push_backEOi_fwd"),
     ("Circe/Specs.lean", "theorem vecPushSumEntry_correct"),
     ("Circe/Emit/VecCompose/Entry.lean", "theorem evalProgFunc_vecPushSumEntry"),
     ("Circe/Transfer/GrowEntry.lean", "theorem memEvalProgFunc_vecPushSumEntry"),
     ("Circe/Transfer/GrowEntry.lean", "theorem memTransfer_vecPushSumEntry"),
     ("Circe/Derived.lean", "theorem bindMemArgs_vecPushSumEntry"),
     ("Circe/Derived.lean", "theorem oracleNoalias_vecPushSumEntry"),
     ("Circe/Validator/GrowLeaves.lean", "def isVecPushSumEntryShape"),
     ("out/VecGrowComposerEntry.lean", "_Z12vec_push_sumv_fwd"),
     ("Circe/Specs.lean", "theorem stdVecCheckLen_correct_fail"),
     ("Circe/Mem/Agree.lean", "theorem vgrowSet_lockstep"),
     ("out/VecGrowReloc.lean", "_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0__fwd"),
     ("tests/golden/VecGrowCheckLen.lean", "_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc_fwd")]),
   ("n5-ergonomics",
    [("Circe/Eval/Stmt.lean", "theorem fuel_step_down"),
     ("Circe/Eval/Stmt.lean", "elab \"cir_step \""),
     ("Circe/Emit/VecCompose/Emplace.lean", "fuel_step_down"),
     ("Circe/Transfer/GrowEmplace.lean", "fuel_step_down"),
     ("Circe/Emit/Span.lean", "cir_step evalExpr"),
     ("Circe/Emit/VecRead.lean", "cir_step evalExpr"),
     ("tests/golden/VecGrowComposerRealloc_Spec.lean", "TODO (user)"),
     ("tests/golden/VecGrowComposerEmplace_Spec.lean", "TODO (user)"),
     ("tests/golden/VecGrowComposerPushBack_Spec.lean", "TODO (user)"),
     ("tests/golden/VecGrowComposerEntry_Spec.lean", "TODO (user)")])]

/-! ## Custom jobs (logic `check.sh` expresses in shell) -/

/-- `Circe/Emit` files: the S5 `by cir_fuel` adoption check
    (`grep -qr "by cir_fuel" Circe/Emit/`). -/
def emitFiles : List String :=
  ["Circe/Emit/Acc.lean", "Circe/Emit/Add.lean", "Circe/Emit/Array.lean",
   "Circe/Emit/Box.lean",
   "Circe/Emit/Calls.lean", "Circe/Emit/Choose.lean", "Circe/Emit/Flow.lean",
   "Circe/Emit/Fragment.lean", "Circe/Emit/Match.lean",
   "Circe/Emit/Method.lean", "Circe/Emit/Render.lean",
   "Circe/Emit/SpecStubs.lean", "Circe/Emit/Struct.lean",
   "Circe/Emit/Sum.lean", "Circe/Emit/Vec.lean", "Circe/Emit/Vec2.lean",
   "Circe/Emit/Vec64.lean", "Circe/Emit/VecRealloc.lean"]

def checkCirFuelAdoption : IO Unit := do
  let mut found := false
  for f in emitFiles do
    let text ← IO.FS.readFile f
    if containsSubstr text "by cir_fuel" then found := true
  if !found then throw (IO.userError "no `by cir_fuel` adoption in Circe/Emit")

/-- N5a negative gate: the manual composer fuel split
    (`Nat.exists_eq_succ_of_ne_zero` at call sites) is gone — the only
    remaining occurrence is the `fuel_step_down` proof itself. -/
def checkNoManualFuelSplit : IO Unit := do
  let out ← shOut "grep" #["-rl", "exists_eq_succ_of_ne_zero", "Circe/"]
  let hits := (out.splitOn "\n").filter (· != "")
  if hits != ["Circe/Eval/Stmt.lean"] then
    throw (IO.userError s!"manual fuel split outside fuel_step_down: {hits}")

/-- M1-homes gate: the heap-family program translations live in
    `Circe.Emit.VecFwd` (next to their proofs), never in `Circe.Base`
    (evaluator vocabulary only). -/
def checkVecFwdHomes : IO Unit := do
  for d in ["def vecFillSumU32 ", "def vecFillSumU64 ",
      "def vecReallocFillSumU32 ", "def vecFillLoopAux ",
      "def vecSumLoopAux ", "def vecCopyLoopAux "] do
    needHas "Circe/Emit/VecFwd.lean" d
  let base ← IO.FS.readFile "Circe/Base.lean"
  for d in ["vecFillSumU32", "vecFillSumU64", "vecReallocFillSumU32",
      "vecFillLoop", "vecSumLoop", "vecCopyLoop"] do
    if containsSubstr base d then
      throw (IO.userError s!"M1 translation still in Circe/Base.lean: {d}")

/-- S3-homes gate: the control-flow translations live in
    `Circe.Emit.FlowFwd` (next to their proofs), never in `Circe.Base`. -/
def checkFlowFwdHomes : IO Unit := do
  for d in ["def nestedSumU32 ", "def skipSumU32 ", "def findEqOut ",
      "def rowU32 ", "def findIdxU32 "] do
    needHas "Circe/Emit/FlowFwd.lean" d
  let base ← IO.FS.readFile "Circe/Base.lean"
  for d in ["nestedSumU32", "skipSumU32", "findEqOut",
      "rowU32", "findIdxU32"] do
    if containsSubstr base d then
      throw (IO.userError s!"S3 translation still in Circe/Base.lean: {d}")

/-- M2-homes gate: the C++-lite translations live in
    `Circe.Emit.M2Fwd` (next to their proofs), never in `Circe.Base`. -/
def checkM2FwdHomes : IO Unit := do
  for d in ["def pointTranslate ", "def pointSum ", "def accTwo ",
      "def moveAcc ", "def scopeEarly ", "def boxThrough ",
      "structure Point "] do
    needHas "Circe/Emit/M2Fwd.lean" d
  let base ← IO.FS.readFile "Circe/Base.lean"
  for d in ["pointTranslate", "pointSum", "accTwo",
      "moveAcc", "scopeEarly", "boxThrough", "structure Point"] do
    if containsSubstr base d then
      throw (IO.userError s!"M2 translation still in Circe/Base.lean: {d}")

/-- Sum-homes gate: the prefix-sum translations live in
    `Circe.Emit.SumFwd` (next to their proofs), never in `Circe.Base`. -/
def checkSumFwdHomes : IO Unit := do
  for d in ["def prefixSumU32 ", "def prefixSumU64 "] do
    needHas "Circe/Emit/SumFwd.lean" d
  let base ← IO.FS.readFile "Circe/Base.lean"
  for d in ["prefixSumU32", "prefixSumU64"] do
    if containsSubstr base d then
      throw (IO.userError s!"sum translation still in Circe/Base.lean: {d}")

/-- Grow-homes gate: the bulk word-copy folds live in
    `Circe.Emit.GrowFwd` (next to their proofs), never in `Circe.Base`. -/
def checkGrowFwdHomes : IO Unit := do
  for d in ["def stdVecBlitFold ", "def stdVecBlitBackFold ",
      "def stdVecBlitFwdFold "] do
    needHas "Circe/Emit/GrowFwd.lean" d
  let base ← IO.FS.readFile "Circe/Base.lean"
  for d in ["stdVecBlitFold", "stdVecBlitBackFold", "stdVecBlitFwdFold"] do
    if containsSubstr base d then
      throw (IO.userError s!"growth blit still in Circe/Base.lean: {d}")

/-- N8c adoption gate: every collapsed closed-entry proof goes through
    the `cir_eval_closed` macro (single adoption point over
    `native_decide`; new entries must use it too). -/
def closedEntryFiles : List String :=
  ["Circe/Emit/VecCompose/Erase.lean",
   "Circe/Emit/VecCompose/InsertRouter.lean",
   "Circe/Emit/VecCompose/Entry.lean",
   "Circe/Emit/VecCompose/Reserve.lean",
   "Circe/Transfer/GrowErase.lean",
   "Circe/Transfer/GrowInsert.lean",
   "Circe/Transfer/GrowEntry.lean",
   "Circe/Transfer/GrowReserve.lean"]

def checkClosedEvalAdoption : IO Unit := do
  for f in closedEntryFiles do
    let text ← IO.FS.readFile f
    if !containsSubstr text "cir_eval_closed" then
      throw (IO.userError s!"no `cir_eval_closed` adoption in {f}")

/-- M2 setup gate: no `cir.cleanup`/`cir.trap` in C corpus `.cir` files
    (C++ files excluded by construction). -/
def checkM2SetupGate : IO Unit := do
  let cpp ← lsDir "tests/cpp"
  let excluded := cpp.filter (endsWith · ".cpp") |>.map (fun f =>
    (f.toList.take (f.length - 4) |> String.ofList) ++ ".cir")
  let cir ← lsDir "tests/cir"
  for f in cir do
    if endsWith f ".cir" && !(excluded.contains f) then
      let text ← IO.FS.readFile ("tests/cir/" ++ f)
      if containsSubstr text "cir.cleanup" || containsSubstr text "cir.trap" then
        throw (IO.userError s!"newly-gated ops present in C corpus: {f}")

/-- `_spec_check` entry name: the `grep -oE` equivalent (ident chars
    immediately preceding the first `_spec_check`). -/
def specCheckOf (text : String) : Option String := do
  let k ← findSubstr? text "_spec_check" 0
  let pre := (text.toList.take k).reverse.takeWhile
    (fun c => c.isAlphanum || c == '_')
  if pre.isEmpty then none else some (String.ofList pre.reverse)

/-- S4 spec loop: every `out/*_Spec.lean` typechecks and its `_check`
    entry evaluates to `true`. Per-stub temporaries: the single shared
    name `check.sh` used would race under parallel tasks. -/
def checkSpecStubs : IO Unit := do
  let entries ← lsDir "out"
  let stubs := entries.filter (endsWith · "_Spec.lean")
  if stubs.length != 105 then
    throw (IO.userError s!"expected 105 spec stubs, found {stubs.length}")
  for s in stubs do
    typecheck ("out/" ++ s)
  for s in stubs do
    let text ← IO.FS.readFile ("out/" ++ s)
    let chk ← match specCheckOf text with
      | none => throw (IO.userError s!"no _spec_check entry in {s}")
      | some c => pure c
    let tmp := s!"{workdir}/spec_eval_{s}"
    IO.FS.writeFile tmp (text ++ s!"\n#eval {chk}_spec_check\n")
    let out ← shOut "lake" #["env", "lean", tmp]
    if !(out.splitOn "\n").contains "true" then
      throw (IO.userError s!"spec check false: {s}: {out}")

/-! ## Suite roster (every `tests/lean` runner, run as parallel tasks) -/

def diffSuites (trials : String) : List Job :=
  [("diff-phase3", DiffPhase3.main [bin "circe_add_native", bin "circe_incr_native", trials]),
   ("diff-phase4", DiffPhase4.main [bin "circe_choose_native", bin "circe_sum_native", trials]),
   ("diff-calls", DiffCalls.main [bin "circe_add_caller_native", bin "circe_sum_caller_native", trials]),
   ("diff-struct", DiffStruct.main [bin "circe_struct_native", trials]),
   ("diff-flow", DiffFlow.main [bin "circe_nested_native", bin "circe_skip_native", bin "circe_find_native", bin "circe_cls_native", bin "circe_cls_fall_native", bin "circe_cls_dense_native", bin "circe_cls_break_native", bin "circe_cls_add_native", trials]),
   ("diff-width", DiffWidth.main [bin "circe_add64_native", bin "circe_addu64_native", trials]),
   ("diff-arith", DiffArith.main [bin "circe_neg_native", bin "circe_sdiv_native", bin "circe_xor_u32_native", bin "circe_and_u32_native", bin "circe_or_u32_native", bin "circe_shl_u32_native", bin "circe_shr_u32_native", trials]),
   ("diff-vec", DiffVec.main [bin "circe_vec_native", trials]),
   ("diff-vec2", DiffVec2.main [bin "circe_vec2_native", trials]),
   ("diff-vec64", DiffVec64.main [bin "circe_vec64_native", trials]),
   ("diff-vecleak", DiffVecLeak.main [bin "circe_vecleak_native", trials]),
   ("diff-vecrealloc", DiffVecRealloc.main [bin "circe_vecrealloc_native", trials]),
   ("diff-acc", DiffAcc.main [bin "circe_acc_native", trials]),
   ("diff-method", DiffMethod.main [bin "circe_method_native", trials]),
   ("diff-box", DiffBox.main [bin "circe_box_native", trials]),
   ("diff-overload", DiffOverload.main [bin "circe_overload_native", bin "circe_ns_add_native", trials]),
   ("diff-move", DiffMove.main [bin "circe_move_int_native", bin "circe_move_acc_native", bin "circe_scope_early_native", trials]),
   ("diff-tadd", DiffTadd.main [bin "circe_tadd_native", trials]),
   ("diff-array", DiffArray.main [bin "circe_array_sum_native", trials]),
   ("diff-optional", DiffOptional.main [bin "circe_opt_deref_native", trials]),
   ("diff-norestrict", DiffNorestrict.main [bin "circe_sum_norestrict_native", trials]),
   ("diff-span", DiffSpan.main [bin "circe_span_sum_native", trials]),
   ("diff-view", DiffView.main [bin "circe_view_sum_native", trials]),
   ("diff-vecread", DiffVecRead.main [bin "circe_vec_read_native", trials]),
   ("diff-reserve", DiffReserve.main [bin "circe_vec_reserve_native", trials]),
   ("diff-insert", DiffInsert.main [bin "circe_vec_insert_native", trials]),
   ("diff-erase", DiffErase.main [bin "circe_vec_erase_native", trials]),
   ("diff-sort", DiffSort.main [trials])]

def checkSuites : List Job :=
  [("golden-phase4", GoldenPhase4.main),
   ("golden-phase6", GoldenPhase6.main),
   ("golden-phase7", GoldenPhase7.main),
   ("golden-calls", GoldenCalls.main),
   ("golden-struct", GoldenStruct.main),
   ("golden-flow", GoldenFlow.main),
   ("golden-width", GoldenWidth.main),
   ("golden-vec2", GoldenVec2.main),
   ("golden-vec64", GoldenVec64.main),
   ("golden-vecrealloc", GoldenVecRealloc.main),
   ("golden-freediscipline", GoldenFreeDiscipline.main),
   ("golden-m2setup", GoldenM2Setup.main),
   ("golden-method", GoldenMethod.main),
   ("golden-acc", GoldenAcc.main),
   ("golden-box", GoldenBox.main),
   ("golden-overload", GoldenOverload.main),
   ("golden-move", GoldenMove.main),
   ("golden-tadd", GoldenTadd.main),
   ("golden-array", GoldenArray.main),
   ("golden-arraysort", GoldenArraySort.main),
   ("golden-arraysort8", GoldenArraySort8.main),
   ("golden-aliasprobe", GoldenAliasProbe.main),
   ("golden-optional", GoldenOptional.main),
   ("golden-span", GoldenSpan.main),
   ("golden-view", GoldenView.main),
   ("golden-vecread", GoldenVecRead.main),
   ("golden-vecgrow", GoldenVecGrow.main),
   ("golden-readonly", GoldenReadOnly.main),
   ("golden-rejectcatalog", GoldenRejectCatalog.main),
   ("derived-noalias", DerivedNoalias.main),
   ("scope-report", ScopeReport.main)]

/-- Registered suite module names (mirrors the `Suites` roots: a new
    `tests/lean` runner without registration fails loudly here). -/
def suiteModules : List String :=
  ["DerivedNoalias", "DiffAcc", "DiffArith", "DiffBox", "DiffCalls", "DiffFlow",
   "DiffMethod", "DiffMove", "DiffNorestrict", "DiffOptional", "DiffOverload", "DiffPhase3", "DiffPhase4", "DiffSpan", "DiffStruct",
   "DiffTadd",
   "DiffVec", "DiffVec2", "DiffVec64", "DiffVecLeak", "DiffVecRealloc", "DiffVecRead",
   "DiffView", "DiffReserve", "DiffInsert", "DiffErase", "DiffSort", "DiffWidth", "DiffOverload", "DiffArray",
   "GoldenAcc", "GoldenBox", "GoldenCalls", "GoldenFlow",
   "GoldenFreeDiscipline", "GoldenM2Setup", "GoldenMethod", "GoldenMove", "GoldenOptional", "GoldenOverload", "GoldenPhase4",
   "GoldenPhase6", "GoldenPhase7", "GoldenReadOnly", "GoldenRejectCatalog",
   "GoldenSpan", "GoldenStruct", "GoldenTadd", "GoldenArray", "GoldenArraySort", "GoldenArraySort8", "GoldenAliasProbe", "GoldenVec2", "GoldenVec64", "GoldenVecRealloc", "GoldenVecRead", "GoldenVecGrow", "GoldenView",
   "GoldenWidth", "ScopeReport"]

def stem (f : String) : String :=
  String.ofList (f.toList.take (f.length - 5))

/-- Anti-deletion tripwire: the roster must match `tests/lean/*.lean`
    exactly (both directions). -/
def checkSuiteRoster : IO Unit := do
  let files ← lsDir "tests/lean"
  let mods := (files.filter (endsWith · ".lean")).map stem
  for m in mods do
    if !suiteModules.contains m then
      throw (IO.userError s!"unregistered suite (add it to the driver roster): {m}")
  for m in suiteModules do
    if !mods.contains m then
      throw (IO.userError s!"rostered suite missing from tests/lean: {m}")

/-- Anti-deletion tripwire: golden pairs must match `tests/golden/*.lean`
    exactly (both directions). -/
def checkGoldenRoster : IO Unit := do
  let files ← lsDir "tests/golden"
  let goldens := files.filter (endsWith · ".lean")
  for g in goldens do
    if !(goldenPairs.map (·.1)).contains ("tests/golden/" ++ g) then
      throw (IO.userError s!"unpinned golden (add its diff pair): {g}")
  for (w, _) in goldenPairs do
    let base := w.toList.drop ("tests/golden/".length) |> String.ofList
    if !goldens.contains base then
      throw (IO.userError s!"golden pair without a checked-in file: {w}")

def main (args : List String) : IO Unit := do
  let trials := ((args.filter (· != "--")).getD 0 "1000")
  IO.FS.createDirAll workdir
  IO.println "== regenerate out/ =="
  sh "lake" #["env", "lean", "--run", "tools/GenOut.lean"]
  IO.println s!"== native builds ({nativeBuilds.length}) =="
  let _ ← runJobs (nativeBuilds.map fun (cc, srcs, out) =>
    (s!"build {out}", ccBuild cc srcs out))
  IO.println "== gate (parallel tasks) =="
  let jobs : List Job :=
    goldenPairs.map (fun (w, g) => (s!"diff {g}", needSameBytes w g))
    ++ (emittedTypechecks ++ moduleTypechecks).map
        (fun f => (s!"typecheck {f}", typecheck f))
    ++ diffSuites trials ++ checkSuites
    ++ contentAsserts.map (fun (n, ps) => (s!"assert {n}", do
        for (f, needle) in ps do needHas f needle))
    ++ [("spec-stubs", checkSpecStubs),
        ("m2-setup-gate", checkM2SetupGate),
        ("cir-fuel-adoption", checkCirFuelAdoption),
        ("n5-no-manual-fuel-split", checkNoManualFuelSplit),
        ("n8-closed-eval-adoption", checkClosedEvalAdoption),
        ("m1-vecfwd-homes", checkVecFwdHomes),
        ("s3-flowfwd-homes", checkFlowFwdHomes),
        ("m2-m2fwd-homes", checkM2FwdHomes),
        ("s0-sumfwd-homes", checkSumFwdHomes),
        ("n7-growfwd-homes", checkGrowFwdHomes),
        ("roster-suites", checkSuiteRoster),
        ("roster-goldens", checkGoldenRoster)]
  let res ← runJobs jobs
  let bad := res.filter (fun (_, r) => !r.isOk)
  IO.println s!"== {res.length} jobs, {res.length - bad.length} ok, {bad.length} failed =="
  match bad with
  | [] => IO.println "TEST-OK"
  | (_, .error e) :: _ =>
    for (n, _) in bad do IO.println s!"FAILED {n}"
    throw e
  | (_, .ok _) :: _ => throw (IO.userError "unreachable")

