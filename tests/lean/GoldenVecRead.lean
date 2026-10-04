-- Golden test for N4d-iv-a: `std::vector<int32_t>` reads pipeline
-- + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenVecRead.lean`
-- 1. Corpus pipeline: `tests/cir/vec_read_sum.cir` (real CIRGen
--    output: the `const&` `vec_read_sum` index-loop entry + the
--    `size` projection leaf + the call-free fused `operator[]`
--    leaf; no ctor/dtor/push/realloc defs) validates via
--    `runModulePipeline` with NO oracle facts (uniqueness comes
--    from the `nonnull + dereferenceable + noundef` attr triple,
--    the M2a single-reference precedent) and emits byte-identical
--    text to `tests/golden/{VecReadSum,VecSize,VecIndex}.lean`
--    (file order: entry, size, index).
-- 2. Rejection suite: call to an unknown vector callee (generic),
--    double call into `size` (site-count pin), entry with two
--    `operator[]` calls and no `size` (call-multiset pin), `size`
--    called at the wrong arity, bare vector pointer without the
--    attr triple (alias discipline) — the first is generic, the
--    middle three hit the dedicated vector wrong-shape rejection,
--    the last `alias-reject`.
-- 3. Deferral pin (N4d-iv-b): `push_back` (growth — reallocation
--    moves values) rejects with the generic out-of-subset code.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

namespace GoldenVecRead

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecReadSumEv : String :=
  "_Z12vec_read_sumRKSt6vectorIiSaIiEE"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexEv : String :=
  "_ZNKSt6vectorIiSaIiEEixEm"

def checkVecReadPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_read_sum.cir"
  let wantSum ← IO.FS.readFile "tests/golden/VecReadSum.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_read_sum: {msg}")
  | .ok [("_Z12vec_read_sumRKSt6vectorIiSaIiEE", gotSum),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotSum != wantSum then
      throw (IO.userError "golden mismatch for vec_read_sum entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for operator[] leaf")
    IO.println "PASS pipeline vec_read_sum (entry + size + index, no oracle facts)"
    pure 3
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecRead (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecread: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecread: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecread: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecread {name} [{code}]"
    pure 1

/-- Call to an unknown vector callee: generic call-shape rejection. -/
def advUnknownVecCallee : String :=
  "module {\n  cir.func @vcall(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZNSt6vectorIiSaIiEEixEmX(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %r : !cir.ptr<!s32i>, !s32i\n    cir.return %v : !s32i\n  }\n}"

/-- Two call sites into `size`: the call-free pin rejects. -/
def advDoubleSize : String :=
  "module {\n  cir.func @vsize2(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %b = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %s = cir.add %a, %b : !u64i\n    cir.return %s : !u64i\n  }\n}"

/-- Two `operator[]` calls and no `size`: the (name, arity,
    site-count) multiset pin rejects. -/
def advDoubleIndex : String :=
  "module {\n  cir.func @vread2(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @" ++ vecIndexEv ++ "(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %b = cir.call @" ++ vecIndexEv ++ "(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!s32i>, !s32i\n    %w = cir.load %b : !cir.ptr<!s32i>, !s32i\n    %s = cir.add nsw %v, %w : !s32i\n    cir.return %s : !s32i\n  }\n}"

/-- `size` called at the wrong arity: no admitted shape takes three
    `i32`s into the vector `size` leaf. -/
def advVecSizeWrongArity : String :=
  "module {\n  cir.func @varod(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}, %arg2: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!s32i) -> !u64i\n"
  ++ "    %b = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.return %b : !s32i\n  }\n}"

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    cir.return %r : !u64i\n  }\n}"

/-- N4d-iv-b deferral pin (`push_back`): growth (reallocation moves
    values) is outside the reads subset. -/
def advPushBack : String :=
  "module {\n  cir.func @vpush(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<!s32i> {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.call @_ZNSt6vectorIiSaIiEE9push_backEOi(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !cir.ptr<!s32i>) -> ()\n"
  ++ "    cir.return\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecReadPipeline
  passed := passed + c0
  let r1 ← checkRejectVecRead "vcall" advUnknownVecCallee .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r1
  let r2 ← checkRejectVecRead "vsize2" advDoubleSize .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r2
  let r3 ← checkRejectVecRead "vread2" advDoubleIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r3
  let r4 ← checkRejectVecRead "varod" advVecSizeWrongArity .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r4
  let r5 ← checkRejectVecRead "vbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  let d1 ← checkRejectVecRead "vpush" advPushBack .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + d1
  IO.println s!"GOLDENVECREAD-OK passed={passed}"

end GoldenVecRead
