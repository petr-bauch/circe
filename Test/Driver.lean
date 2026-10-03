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
import DiffBox
import DiffCalls
import DiffFlow
import DiffMethod
import DiffNorestrict
import DiffPhase3
import DiffPhase4
import DiffStruct
import DiffVec
import DiffVec2
import DiffVec64
import DiffVecLeak
import DiffVecRealloc
import DiffWidth
import GoldenAcc
import GoldenBox
import GoldenCalls
import GoldenFlow
import GoldenFreeDiscipline
import GoldenM2Setup
import GoldenMethod
import GoldenPhase4
import GoldenPhase6
import GoldenPhase7
import GoldenReadOnly
import GoldenRejectCatalog
import GoldenStruct
import GoldenVec2
import GoldenVec64
import GoldenVecRealloc
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
   ("cc", ["tests/c/add64.c", "tests/diff/driver_add64.c"], bin "circe_add64_native"),
   ("cc", ["tests/c/addu64.c", "tests/diff/driver_addu64.c"], bin "circe_addu64_native"),
   ("cc", ["tests/c/vec_alloc.c", "tests/diff/driver_vec.c"], bin "circe_vec_native"),
   ("cc", ["tests/c/vec_copy_sum.c", "tests/diff/driver_veccopy.c"], bin "circe_vec2_native"),
   ("cc", ["tests/c/vec_alloc_u64.c", "tests/diff/driver_vec64.c"], bin "circe_vec64_native"),
   ("cc", ["tests/c/vec_realloc.c", "tests/diff/driver_vecrealloc.c"], bin "circe_vecrealloc_native"),
   ("cc", ["tests/c/vec_alloc_leak.c", "tests/diff/driver_vecleak.c"], bin "circe_vecleak_native"),
   ("c++", ["tests/cpp/point_sum_ref.cpp", "tests/diff/driver_method.cpp"], bin "circe_method_native"),
   ("c++", ["tests/cpp/acc_two.cpp", "tests/diff/driver_acc.cpp"], bin "circe_acc_native"),
   ("c++", ["tests/cpp/box_through.cpp", "tests/diff/driver_box.cpp"], bin "circe_box_native"),
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
   ("tests/golden/Add64.lean", "out/Add64.lean"),
   ("tests/golden/Addu64.lean", "out/Addu64.lean"),
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
   ("tests/golden/SumNorestrict.lean", "out/SumNorestrict.lean")]

/-- Emitted files `check.sh` typechecks individually (beyond the spec
    loop, which covers every `out/*_Spec.lean`). -/
def emittedTypechecks : List String :=
  ["out/Add.lean", "out/Incr.lean", "out/Choose.lean", "out/SumArray.lean",
   "out/AddCaller.lean", "out/SumCaller.lean", "out/StructByValue.lean",
   "out/NestedSum.lean", "out/SkipSum.lean", "out/FindEq.lean", "out/Cls.lean",
   "out/Add64.lean", "out/Addu64.lean",
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
   "out/SumNorestrict.lean", "out/SumNorestrict_Spec.lean"]

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
     -- is preserved with the corrected needle.
     ("docs/ROADMAP.md", "Stacked Borrows"),
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
    [("Circe/Eval.lean", "macro \"cir_fuel\""),
     ("Circe/Eval.lean", "word32_lt_two32_of_fuel"),
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
    [("Circe/Mem.lean", "theorem memTransfer_add"),
     ("Circe/Mem.lean", "theorem memTransfer_incr"),
     ("Circe/Transfer.lean", "theorem memTransfer_sum "),
     ("Circe/Transfer.lean", "theorem memTransfer_sum_oob"),
     ("Circe/Transfer.lean", "theorem memTransfer_vec "),
     ("Circe/Mem.lean", "def m3c_transfer_statement")]),
   ("m3b-derived",
    [("Circe/Validator.lean", "def derivedNoalias"),
     ("Circe/Validator.lean", "theorem derivedNoalias_all_noalias"),
     ("Circe/Validator.lean", "theorem derivedNoalias_admitted_c"),
     ("Circe/Derived.lean", "theorem oracleNoalias_choose"),
     ("Circe/Derived.lean", "theorem oracleNoalias_sumCaller"),
     ("Circe/Derived.lean", "theorem oracleNoalias_findEq"),
     ("Circe/Derived.lean", "theorem derived_bridge_noalias")]),
   ("m3c-loopfree",
    [("Circe/Transfer.lean", "theorem memTransfer_choose"),
     ("Circe/Transfer.lean", "theorem memTransfer_add64"),
     ("Circe/Transfer.lean", "theorem memTransfer_addu64"),
     ("Circe/Transfer.lean", "theorem memTransfer_cls"),
     ("Circe/Transfer.lean", "theorem memTransfer_translate"),
     ("Circe/Derived.lean", "theorem oracleNoalias_add64"),
     ("Circe/Derived.lean", "theorem oracleNoalias_addu64"),
     ("Circe/Derived.lean", "theorem oracleNoalias_cls"),
     ("Circe/Derived.lean", "theorem oracleNoalias_translate"),
     ("Circe/Mem.lean", "theorem memEvalExpr_add_fget_var")]),
   ("m3c-flow",
    [("Circe/Transfer.lean", "theorem memTransfer_nested"),
     ("Circe/Transfer.lean", "theorem memTransfer_skip"),
     ("Circe/Transfer.lean", "theorem memTransfer_findEq"),
     ("Circe/Transfer.lean", "theorem memNestedOuter_correct"),
     ("Circe/Transfer.lean", "theorem memSkipWhile_correct"),
     ("Circe/Transfer.lean", "theorem memFindWhile_some"),
     ("Circe/Transfer.lean", "theorem memFindWhile_none"),
     ("Circe/Derived.lean", "theorem oracleNoalias_nested"),
     ("Circe/Derived.lean", "theorem oracleNoalias_skip")]),
   ("m3c-caller",
    [("Circe/Transfer.lean", "theorem memEvalProgFunc_addCaller"),
     ("Circe/Transfer.lean", "theorem memTransferProg_addCaller"),
     ("Circe/Transfer.lean", "theorem memEvalProgFunc_sumCaller"),
     ("Circe/Transfer.lean", "theorem memTransferProg_sumCaller"),
     ("Circe/Mem.lean", "def memEvalProgStmt"),
     ("Circe/Mem.lean", "def memEvalProgFunc"),
     ("Circe/Mem.lean", "theorem memEvalProgStmt_callRet_ok"),
     ("Circe/Mem.lean", "theorem memEvalProgStmt_callRet_err")]),
   ("m3c-vec2",
    [("Circe/Transfer.lean", "theorem memVec2FillWhile_correct"),
     ("Circe/Transfer.lean", "theorem memVec2CopyWhile_correct"),
     ("Circe/Transfer.lean", "theorem memVec2SumWhile_correct"),
     ("Circe/Transfer.lean", "theorem memEvalFuncFuel_vec2"),
     ("Circe/Transfer.lean", "theorem memTransfer_vec2"),
     ("Circe/Derived.lean", "theorem oracleNoalias_vec2"),
     ("Circe/Mem.lean", "theorem memFind_memStore_other"),
     ("Circe/Mem.lean", "theorem memFind_memFree_other")]),
   ("m3c-vecrealloc",
    [("Circe/Mem.lean", "def memRealloc"),
     ("Circe/Mem.lean", "theorem vrealloc_lockstep"),
     ("Circe/Mem.lean", "theorem memEvalStmtFuel_vrealloc"),
     ("Circe/Transfer.lean", "theorem memVecReallocFillWhile_correct"),
     ("Circe/Transfer.lean", "theorem memVecReallocExtWhile_correct"),
     ("Circe/Transfer.lean", "theorem memVecReallocSumWhile_correct"),
     ("Circe/Transfer.lean", "theorem memVecReallocStep_eval"),
     ("Circe/Transfer.lean", "theorem memEvalFuncFuel_vecRealloc"),
     ("Circe/Transfer.lean", "theorem memTransfer_vecRealloc"),
     ("Circe/Derived.lean", "theorem oracleNoalias_vecRealloc")]),
   ("m3c-vec64",
    [("Circe/Mem.lean", "structure Block64"),
     ("Circe/Mem.lean", "def memFind64"),
     ("Circe/Mem.lean", "def memAllocData64"),
     ("Circe/Mem.lean", "def memLoad64"),
     ("Circe/Mem.lean", "def memStore64"),
     ("Circe/Mem.lean", "def memFree64"),
     ("Circe/Mem.lean", "theorem vset64_lockstep"),
     ("Circe/Mem.lean", "theorem vfree64_lockstep"),
     ("Circe/Mem.lean", "theorem memEvalStmtFuel_let_vnew64"),
     ("Circe/Transfer.lean", "theorem memVec64FillWhile_correct"),
     ("Circe/Transfer.lean", "theorem memVec64SumWhile_correct"),
     ("Circe/Transfer.lean", "theorem memEvalFuncFuel_vec64"),
     ("Circe/Transfer.lean", "theorem memTransfer_vec64"),
     ("Circe/Derived.lean", "theorem oracleNoalias_vec64")]),
   ("m3d-cpp",
    [("Circe/Mem.lean", "theorem memEvalProgStmt_cleanup"),
     ("Circe/Mem.lean", "theorem memEvalStmtFuel_let_boxNew"),
     ("Circe/Mem.lean", "theorem memEvalExpr_boxGet_hit"),
     ("Circe/Mem.lean", "theorem vboxFree_lockstep"),
     ("Circe/Mem.lean", "theorem memEvalStmtFuel_boxFree"),
     ("Circe/Transfer.lean", "theorem memEvalFuncFuel_methodSum"),
     ("Circe/Transfer.lean", "theorem memTransfer_methodSum"),
     ("Circe/Transfer.lean", "theorem memEvalProgFunc_pointSumRef"),
     ("Circe/Transfer.lean", "theorem memTransferProg_pointSumRef"),
     ("Circe/Transfer.lean", "theorem memEvalFuncFuel_accCtor"),
     ("Circe/Transfer.lean", "theorem memTransfer_accAdd"),
     ("Circe/Transfer.lean", "theorem memTransfer_accGet"),
     ("Circe/Transfer.lean", "theorem memTransfer_accDtor"),
     ("Circe/Transfer.lean", "theorem memEvalProgFunc_accTwo"),
     ("Circe/Transfer.lean", "theorem memTransferProg_accTwo"),
     ("Circe/Transfer.lean", "theorem memEvalFuncFuel_boxThrough"),
     ("Circe/Transfer.lean", "theorem memTransfer_boxThrough"),
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
    [("Circe/Validator.lean", "writer+reader"),
     ("Circe/Validator.lean", "escaping-borrow"),
     ("Circe/Validator.lean", "borrow-after-free")]),
   ("n2c-recovery",
    [("Circe/Validator.lean", "def recoveredNoalias"),
     ("Circe/Validator.lean", "theorem recoveredNoalias_admitted_reader"),
     ("Circe/Validator.lean", "theorem recoveredNoalias_single_oracle"),
     ("Circe/Validator.lean", "def isRecoveredParam"),
     ("out/SumNorestrict.lean", "prefixSumU32 a.val a.val.length")]),
   ("l1-scope",
    [("Circe/Scope.lean", "def extractScopes"),
     ("Circe/Scope.lean", "theorem extractScopes_empty"),
     ("Circe/Scope.lean", "theorem extractScopes_bound")])]

/-! ## Custom jobs (logic `check.sh` expresses in shell) -/

/-- `Circe/Emit` files: the S5 `by cir_fuel` adoption check
    (`grep -qr "by cir_fuel" Circe/Emit/`). -/
def emitFiles : List String :=
  ["Circe/Emit/Acc.lean", "Circe/Emit/Add.lean", "Circe/Emit/Box.lean",
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
  if stubs.length != 26 then
    throw (IO.userError s!"expected 26 spec stubs, found {stubs.length}")
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
   ("diff-flow", DiffFlow.main [bin "circe_nested_native", bin "circe_skip_native", bin "circe_find_native", bin "circe_cls_native", trials]),
   ("diff-width", DiffWidth.main [bin "circe_add64_native", bin "circe_addu64_native", trials]),
   ("diff-vec", DiffVec.main [bin "circe_vec_native", trials]),
   ("diff-vec2", DiffVec2.main [bin "circe_vec2_native", trials]),
   ("diff-vec64", DiffVec64.main [bin "circe_vec64_native", trials]),
   ("diff-vecleak", DiffVecLeak.main [bin "circe_vecleak_native", trials]),
   ("diff-vecrealloc", DiffVecRealloc.main [bin "circe_vecrealloc_native", trials]),
   ("diff-acc", DiffAcc.main [bin "circe_acc_native", trials]),
   ("diff-method", DiffMethod.main [bin "circe_method_native", trials]),
   ("diff-box", DiffBox.main [bin "circe_box_native", trials]),
   ("diff-norestrict", DiffNorestrict.main [bin "circe_sum_norestrict_native", trials])]

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
   ("golden-readonly", GoldenReadOnly.main),
   ("golden-rejectcatalog", GoldenRejectCatalog.main),
   ("derived-noalias", DerivedNoalias.main),
   ("scope-report", ScopeReport.main)]

/-- Registered suite module names (mirrors the `Suites` roots: a new
    `tests/lean` runner without registration fails loudly here). -/
def suiteModules : List String :=
  ["DerivedNoalias", "DiffAcc", "DiffBox", "DiffCalls", "DiffFlow",
   "DiffMethod", "DiffNorestrict", "DiffPhase3", "DiffPhase4", "DiffStruct",
   "DiffVec", "DiffVec2", "DiffVec64", "DiffVecLeak", "DiffVecRealloc",
   "DiffWidth", "GoldenAcc", "GoldenBox", "GoldenCalls", "GoldenFlow",
   "GoldenFreeDiscipline", "GoldenM2Setup", "GoldenMethod", "GoldenPhase4",
   "GoldenPhase6", "GoldenPhase7", "GoldenReadOnly", "GoldenRejectCatalog",
   "GoldenStruct", "GoldenVec2", "GoldenVec64", "GoldenVecRealloc",
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

