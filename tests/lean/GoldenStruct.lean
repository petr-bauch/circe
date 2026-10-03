-- Golden test for S2: struct-by-value pipeline + misshapen-struct
-- rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenStruct.lean`
-- 1. Corpus pipeline: `tests/cir/struct_by_value.cir` parses, validates
--    under its `tests/oracle/verdicts.txt` verdict (`unknown`: no pointer
--    params), and emits byte-identical text to
--    `tests/golden/StructByValue.lean`.
-- 2. Rejection suite: misshapen struct uses (wrong arity, struct + call,
--    struct passthrough without field ops, `get_member` on non-struct
--    types) hit exact codes + message substrings, so the new `validate`
--    branches are exercised. Mismatch policy: any in-subset divergence
--    is P0; out-of-subset must reject loudly.
import Circe.Validator

namespace GoldenStruct

def checkStructPipeline (verdicts : List OracleFact) : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/struct_by_value.cir"
  let want ← IO.FS.readFile "tests/golden/StructByValue.lean"
  let oracle ← match lookupOracle verdicts "translate" with
    | none => throw (IO.userError "no oracle fact for translate")
    | some o => pure o
  match runPipeline text oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError "golden mismatch for translate")
    IO.println "PASS pipeline translate"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected translate: {msg}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectStruct (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-struct: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-struct: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-struct: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-struct {name} [{code}]"
    pure 1

/-- Wrong arity: `Point` + one delta (two params) with field reads —
    outside the three-param `translate` shape. -/
def advStructArity : String :=
  "module {\n  cir.func @tr2(%arg0: !rec_Point {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !rec_Point attributes {\"nothrow\"} {\n    %m = cir.get_member %arg0[0] {name = \"x\"} : !cir.ptr<!rec_Point> -> !cir.ptr<!s32i>\n    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n    %s = cir.add nsw %v, %arg1 : !s32i\n    cir.return %arg0 : !rec_Point\n  }\n}"

/-- Struct + call: field read plus a non-heap call — the call-shape
    gate fires first (calls outside admitted shapes). -/
def advStructCall : String :=
  "module {\n  cir.func @trs(%arg0: !rec_Point {llvm.noundef}, %arg1: !s32i {llvm.noundef}, %arg2: !s32i {llvm.noundef}) -> !rec_Point attributes {\"nothrow\"} {\n    %m = cir.get_member %arg0[0] {name = \"x\"} : !cir.ptr<!rec_Point> -> !cir.ptr<!s32i>\n    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n    %r = cir.call @add(%v, %arg1) : (!s32i, !s32i) -> !s32i\n    cir.return %arg0 : !rec_Point\n  }\n}"

/-- Struct passthrough: `Point` in, `Point` out, no field ops at all —
    outside every shape (generic fallback message). -/
def advStructPassthrough : String :=
  "module {\n  cir.func @tp(%arg0: !rec_Point {llvm.noundef}) -> !rec_Point attributes {\"nothrow\"} {\n    cir.return %arg0 : !rec_Point\n  }\n}"

/-- `get_member` on non-struct types: two `i32`s with a field read —
    misshapen struct access, not the `translate` shape. -/
def advGetMemberNonStruct : String :=
  "module {\n  cir.func @gm(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %m = cir.get_member %arg0[0] {name = \"x\"} : !cir.ptr<!s32i> -> !cir.ptr<!s32i>\n    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n    %s = cir.add nsw %v, %arg1 : !s32i\n    cir.return %s : !s32i\n  }\n}"

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkStructPipeline verdicts
  passed := passed + c1
  let c2 ← checkRejectStruct "tr2" advStructArity .unknown
    "out-of-subset" "outside the admitted `translate` shape"
  passed := passed + c2
  let c3 ← checkRejectStruct "trs" advStructCall .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + c3
  let c4 ← checkRejectStruct "tp" advStructPassthrough .unknown
    "out-of-subset" "admitted"
  passed := passed + c4
  let c5 ← checkRejectStruct "gm" advGetMemberNonStruct .unknown
    "out-of-subset" "outside the admitted `translate` shape"
  passed := passed + c5
  IO.println s!"GOLDENSTRUCT-OK passed={passed}"

end GoldenStruct
