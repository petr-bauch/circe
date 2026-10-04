-- Golden test for N4d-i: `std::array<int, 4>` read pipeline +
-- rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenArray.lean`
-- 1. Corpus pipeline: `tests/cir/array_sum.cir` (real CIRGen output
--    with `-fno-exceptions`: the 4-call entry + `operator[]` +
--    `_S_ref`) validates via `runModulePipeline` with NO oracle facts
--    (uniqueness comes from the `nonnull + dereferenceable + noundef`
--    attr triple, the M2a single-reference precedent) and emits
--    byte-identical text to
--    `tests/golden/{ArraySum,ArrayAt,ArrayRef}.lean`.
-- 2. Rejection suite: call to an unknown array callee (generic),
--    double call into `_S_ref` (single-site pin), call plus extra
--    indexing ops, `operator[]` called at the wrong arity, 3-site entry
--    (not 4), bare array pointer without the attr triple (alias
--    discipline) — the first is generic, the rest hit the dedicated
--    array wrong-shape rejection (or `alias-reject`).
-- 3. Deferral pins (N4d-iii/iv, still out of subset; N4d-ii
--    graduated: guarded `operator*` is admitted — see
--    `GoldenOptional` — while `optional::value` stays out): the
--    `value` throw lowers to `cir.trap`, `string_view::begin`/`end` return raw
--    pointers, `vector` needs operator-`new` — each rejects with its
--    dedicated code, documenting exactly what a future slice must gate.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

namespace GoldenArray

def arrayTriple : String :=
  "{llvm.align = 4 : i64, llvm.dereferenceable = 16 : i64, llvm.nonnull, llvm.noundef}"

def checkArrayPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/array_sum.cir"
  let wantSum ← IO.FS.readFile "tests/golden/ArraySum.lean"
  let wantAt ← IO.FS.readFile "tests/golden/ArrayAt.lean"
  let wantRef ← IO.FS.readFile "tests/golden/ArrayRef.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected array_sum: {msg}")
  | .ok [("_Z9array_sumRKSt5arrayIiLm4EE", gotSum),
         ("_ZNKSt5arrayIiLm4EEixEm", gotAt),
         ("_ZNSt14__array_traitsIiLm4EE6_S_refERA4_Kim", gotRef)] =>
    if gotSum != wantSum then
      throw (IO.userError "golden mismatch for array_sum entry")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for operator[] entry")
    if gotRef != wantRef then
      throw (IO.userError "golden mismatch for _S_ref leaf")
    IO.println "PASS pipeline array_sum (entry + at + ref, no oracle facts)"
    pure 3
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectArray (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-array: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-array: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-array: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-array {name} [{code}]"
    pure 1

/-- Call to an unknown array callee: generic call-shape rejection. -/
def advUnknownArrayCallee : String :=
  "module {\n  cir.func @acall(%arg0: !cir.ptr<!rec_std3A3Aarray3Cint2C_4UL3E> " ++ arrayTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZNKSt5arrayIiLm4EEixEmX(%arg0) : (!cir.ptr<!rec_std3A3Aarray3Cint2C_4UL3E>) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

/-- Two call sites into `_S_ref`: the single-site pin rejects. -/
def advDoubleRef : String :=
  "module {\n  cir.func @adouble(%arg0: !cir.ptr<!cir.array<!s32i x 4>> " ++ arrayTriple ++ ", %arg1: !u64i {llvm.noundef}) -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @_ZNSt14__array_traitsIiLm4EE6_S_refERA4_Kim(%arg0, %arg1) : (!cir.ptr<!cir.array<!s32i x 4>>, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %b = cir.call @_ZNSt14__array_traitsIiLm4EE6_S_refERA4_Kim(%arg0, %arg1) : (!cir.ptr<!cir.array<!s32i x 4>>, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!s32i>, !s32i\n    %w = cir.load %b : !cir.ptr<!s32i>, !s32i\n    %s = cir.add nsw %v, %w : !s32i\n    %r = cir.alloca \"__retval\" : !cir.ptr<!cir.ptr<!s32i>>\n    cir.store %a, %r : !cir.ptr<!s32i>, !cir.ptr<!cir.ptr<!s32i>>\n    %q = cir.load %r : !cir.ptr<!cir.ptr<!s32i>>, !cir.ptr<!s32i>\n    cir.return %q : !cir.ptr<!s32i>\n  }\n}"

/-- Call plus extra indexing ops: the leaf admits `get_element` alone
    (any projection or arithmetic of its own rejects). -/
def advRefLocalArith : String :=
  "module {\n  cir.func @aarith(%arg0: !cir.ptr<!cir.array<!s32i x 4>> " ++ arrayTriple ++ ", %arg1: !u64i {llvm.noundef}) -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @_ZNSt14__array_traitsIiLm4EE6_S_refERA4_Kim(%arg0, %arg1) : (!cir.ptr<!cir.array<!s32i x 4>>, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %m = cir.get_member %arg0[0] {name = \"_M_elems\"} : !cir.ptr<!cir.array<!s32i x 4>> -> !cir.ptr<!cir.array<!s32i x 4>>\n"
  ++ "    %e = cir.get_element %m[%arg1 : !u64i] : !cir.ptr<!cir.array<!s32i x 4>> -> !cir.ptr<!s32i>\n    cir.return %e : !cir.ptr<!s32i>\n  }\n}"

/-- `operator[]` called at the wrong arity: no admitted caller
    targets it with three params. -/
def advAtWrongArity : String :=
  "module {\n  cir.func @aarod(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}, %arg2: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @_ZNKSt5arrayIiLm4EEixEm(%arg0) : (!s32i) -> !cir.ptr<!s32i>\n    %v = cir.load %a : !cir.ptr<!s32i>, !s32i\n    cir.return %v : !s32i\n  }\n}"

/-- Three call sites into `operator[]` (not four): the site-count pin
    rejects. -/
def advThreeSites : String :=
  "module {\n  cir.func @asites(%arg0: !cir.ptr<!rec_std3A3Aarray3Cint2C_4UL3E> " ++ arrayTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %c0 = cir.const #cir.int<0> : !u64i\n"
  ++ "    %c1 = cir.const #cir.int<1> : !u64i\n"
  ++ "    %c2 = cir.const #cir.int<2> : !u64i\n"
  ++ "    %a = cir.call @_ZNKSt5arrayIiLm4EEixEm(%arg0, %c0) : (!cir.ptr<!rec_std3A3Aarray3Cint2C_4UL3E>, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %b = cir.call @_ZNKSt5arrayIiLm4EEixEm(%arg0, %c1) : (!cir.ptr<!rec_std3A3Aarray3Cint2C_4UL3E>, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %c = cir.call @_ZNKSt5arrayIiLm4EEixEm(%arg0, %c2) : (!cir.ptr<!rec_std3A3Aarray3Cint2C_4UL3E>, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!s32i>, !s32i\n    %w = cir.load %b : !cir.ptr<!s32i>, !s32i\n    %x = cir.load %c : !cir.ptr<!s32i>, !s32i\n    %s = cir.add nsw %v, %w : !s32i\n    %t = cir.add nsw %s, %x : !s32i\n    cir.return %t : !s32i\n  }\n}"

/-- Bare array pointer without the attr triple: the alias discipline
    rejects before shapes are even consulted. -/
def advBareArrayPtr : String :=
  "module {\n  cir.func @abare(%arg0: !cir.ptr<!cir.array<!s32i x 4>> {llvm.noundef}, %arg1: !u64i {llvm.noundef}) -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n"
  ++ "    %e = cir.get_element %arg0[%arg1 : !u64i] : !cir.ptr<!cir.array<!s32i x 4>> -> !cir.ptr<!s32i>\n    cir.return %e : !cir.ptr<!s32i>\n  }\n}"

/-- N4d-ii deferral pin (`optional::value`): the throw path lowers to
    `cir.trap`, which is `outOfSubset` outside the M2b/N4b shapes. -/
def advOptTrap : String :=
  "module {\n  cir.func @otrap(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    cir.trap\n    cir.return %arg0 : !s32i\n  }\n}"

/-- N4d-iii deferral pin (`string_view::begin`/`end`): raw pointer
    return with no pointer inputs is `escape-reject`
    (escaping-borrow). -/
def advViewPtrRet : String :=
  "module {\n  cir.func @vptrret(%arg0: !s32i {llvm.noundef}) -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.alloca \"r\" : !cir.ptr<!s32i>\n    cir.return %r : !cir.ptr<!s32i>\n  }\n}"

/-- N4d-iv deferral pin (`vector` allocator): operator-`new` outside
    the `box_through` shape is `outOfSubset` (the 2188-line CIR /
    60-def allocator bloat never reaches a shape). -/
def advVecNew : String :=
  "module {\n  cir.func @vnew(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %m = cir.call @_Znwm(%arg0) : (!s32i) -> !cir.ptr<!s32i>\n    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n    cir.return %v : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkArrayPipeline
  passed := passed + c0
  let r1 ← checkRejectArray "acall" advUnknownArrayCallee .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r1
  let r2 ← checkRejectArray "adouble" advDoubleRef .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r2
  let r3 ← checkRejectArray "aarith" advRefLocalArith .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r3
  let r4 ← checkRejectArray "aarod" advAtWrongArity .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r4
  let r5 ← checkRejectArray "asites" advThreeSites .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r5
  let r6 ← checkRejectArray "abare" advBareArrayPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r6
  let d1 ← checkRejectArray "otrap" advOptTrap .unknown
    "out-of-subset" "trap (`cir.trap`"
  passed := passed + d1
  let d2 ← checkRejectArray "vptrret" advViewPtrRet .unknown
    "escape-reject" "with no pointer inputs"
  passed := passed + d2
  let d3 ← checkRejectArray "vnew" advVecNew .unknown
    "out-of-subset" "outside the admitted `box_through` shape"
  passed := passed + d3
  IO.println s!"GOLDENARRAY-OK passed={passed}"

end GoldenArray
