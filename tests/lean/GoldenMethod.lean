-- Golden test for M2a: POD const-method pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenMethod.lean`
-- 1. Corpus pipeline: `tests/cir/point_sum_ref.cir` (real CIRGen output
--    with `-fno-exceptions`: entry + method leaf) validates via
--    `validateModule` with NO oracle facts (uniqueness comes from the
--    `nonnull + dereferenceable + noundef` attr triple) and emits
--    byte-identical text to `tests/golden/PointSumRef.lean` +
--    `tests/golden/MethodSum.lean`.
-- 2. Rejection suite: by-value `coerce` lowering (deferral pin), unknown
--    method callee, call inside the method leaf, method returning
--    `Point`, bare `Point*` without the attr triple, double method call
--    — all loud with exact codes + message substrings.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

def tripleAttrs : String :=
  "{llvm.align = 4 : i64, llvm.dereferenceable = 8 : i64, llvm.nonnull, llvm.noundef}"

def checkMethodPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/point_sum_ref.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/PointSumRef.lean"
  let wantLeaf ← IO.FS.readFile "tests/golden/MethodSum.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected point_sum_ref: {msg}")
  | .ok [("_Z13point_sum_refRK5Point", gotEntry),
         ("_ZNK5Point3sumEv", gotLeaf)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for point_sum_ref entry")
    if gotLeaf != wantLeaf then
      throw (IO.userError "golden mismatch for method leaf")
    IO.println "PASS pipeline point_sum_ref (entry + leaf, no oracle facts)"
    pure 2
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectMethod (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-method: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-method: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-method: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-method {name} [{code}]"
    pure 1

/-- By-value struct param: the `coerce` alloca + `bitcast` lowering is
    deferred (pass by `const&` instead). -/
def advCoerce : String :=
  "module {\n  cir.func @_Z9point_sum5Point(%arg0: !u64i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %0 = cir.alloca \"coerce\" align(8) : !cir.ptr<!u64i>\n    %1 = cir.cast bitcast %0 : !cir.ptr<!u64i> -> !cir.ptr<!rec_Point>\n    %2 = cir.load %1 : !cir.ptr<!rec_Point>, !rec_Point\n    %3 = cir.alloca \"p\" align(4) : !cir.ptr<!rec_Point>\n    cir.store %2, %3 : !rec_Point, !cir.ptr<!rec_Point>\n    %4 = cir.call @_ZNK5Point3sumEv(%3) : (!cir.ptr<!rec_Point>) -> !s32i\n    cir.return %4 : !s32i\n  }\n}"

def advUnknownMethod : String :=
  "module {\n  cir.func @uref(%arg0: !cir.ptr<!rec_Point> " ++ tripleAttrs ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZNK5Point3fooEv(%arg0) : (!cir.ptr<!rec_Point>) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

def advMethodCall : String :=
  "module {\n  cir.func @mcall(%arg0: !cir.ptr<!rec_Point> " ++ tripleAttrs ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %m = cir.get_member %arg0[0] {name = \"x\"} : !cir.ptr<!rec_Point> -> !cir.ptr<!s32i>\n    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %r = cir.call @_ZNK5Point3sumEv(%arg0) : (!cir.ptr<!rec_Point>) -> !s32i\n    %s = cir.add nsw %v, %r : !s32i\n    cir.return %s : !s32i\n  }\n}"

def advMethodPointRet : String :=
  "module {\n  cir.func @mpret(%arg0: !cir.ptr<!rec_Point> " ++ tripleAttrs ++ ") -> !rec_Point attributes {\"nothrow\"} {\n"
  ++ "    %m = cir.get_member %arg0[0] {name = \"x\"} : !cir.ptr<!rec_Point> -> !cir.ptr<!s32i>\n    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %n = cir.get_member %arg0[1] {name = \"y\"} : !cir.ptr<!rec_Point> -> !cir.ptr<!s32i>\n    %w = cir.load %n : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %s = cir.add nsw %v, %w : !s32i\n    %q = cir.alloca \"q\" align(4) : !cir.ptr<!rec_Point>\n    cir.store %v, %q : !s32i, !cir.ptr<!s32i>\n    %r = cir.load %q : !cir.ptr<!rec_Point>, !rec_Point\n    cir.return %r : !rec_Point\n  }\n}"

def advBarePtr : String :=
  "module {\n  cir.func @bptr(%arg0: !cir.ptr<!rec_Point> {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %m = cir.get_member %arg0[0] {name = \"x\"} : !cir.ptr<!rec_Point> -> !cir.ptr<!s32i>\n    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %n = cir.get_member %arg0[1] {name = \"y\"} : !cir.ptr<!rec_Point> -> !cir.ptr<!s32i>\n    %w = cir.load %n : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %s = cir.add nsw %v, %w : !s32i\n    cir.return %s : !s32i\n  }\n}"

def advDoubleCall : String :=
  "module {\n  cir.func @dref(%arg0: !cir.ptr<!rec_Point> " ++ tripleAttrs ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @_ZNK5Point3sumEv(%arg0) : (!cir.ptr<!rec_Point>) -> !s32i\n"
  ++ "    %b = cir.call @_ZNK5Point3sumEv(%arg0) : (!cir.ptr<!rec_Point>) -> !s32i\n"
  ++ "    %s = cir.add nsw %a, %b : !s32i\n    cir.return %s : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkMethodPipeline
  passed := passed + c0
  let c1 ← checkRejectMethod "coerce" advCoerce .unknown
    "out-of-subset" "coerce"
  passed := passed + c1
  let c2 ← checkRejectMethod "uref" advUnknownMethod .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + c2
  let c3 ← checkRejectMethod "mcall" advMethodCall .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + c3
  let c4 ← checkRejectMethod "mpret" advMethodPointRet .unknown
    "out-of-subset" "outside the admitted `translate` shape"
  passed := passed + c4
  let c5 ← checkRejectMethod "bptr" advBarePtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + c5
  let c6 ← checkRejectMethod "dref" advDoubleCall .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + c6
  IO.println s!"GOLDENMETHOD-OK passed={passed}"
