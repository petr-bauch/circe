-- Golden test for S3a: control-flow pipeline + misshapen-flow
-- rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenFlow.lean`
-- 1. Corpus pipeline: `tests/cir/{nested_sum,skip_sum,find_eq,cls,
--    cls_fall,cls_dense}.cir` parse, validate under their
--    `tests/oracle/verdicts.txt` verdicts, and emit byte-identical text
--    to `tests/golden/{NestedSum,SkipSum,FindEq,Cls,ClsFall,ClsDense}.lean`.
-- 2. Rejection suite: misshapen control flow (break outside a loop,
--    non-lowerable switch, lowerable switch with wrong signature,
--    break inside nested loops, single-return search loop, range-case
--    switch, unsigned arithmetic in a case body, permuted const mapping,
--    double-`10` mapping matching neither `cls` nor `cls_fall` pins)
--    hits exact codes + message substrings, so the new `validate`
--    branches are exercised. Mismatch policy: any in-subset
--    divergence is P0; out-of-subset must reject loudly.
import Circe.Validator

namespace GoldenFlow

def checkFlowPipeline (verdicts : List OracleFact) (cir golden func : String) :
    IO Nat := do
  let text ← IO.FS.readFile cir
  let want ← IO.FS.readFile golden
  let oracle ← match lookupOracle verdicts func with
    | none => throw (IO.userError s!"no oracle fact for {func}")
    | some o => pure o
  match runPipeline text oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for {func}")
    IO.println s!"PASS pipeline {func}"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected {func}: {msg}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectFlow (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-flow: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-flow: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-flow: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-flow {name} [{code}]"
    pure 1

/-- `break` outside any loop: no `cir.for`, so neither the skip shape
    (needs the loop) nor any older shape matches. -/
def advBreakNoLoop : String :=
  "module {\n  cir.func @bn(%arg0: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    cir.break loc(#loc1)\n    cir.return %arg0 : !u32i\n  }\n}"

/-- `switch` with unadmitted fallthrough (first case returns the
    scrutinee, second case is an empty scope on const `2`): neither the
    `cls` shape (non-const returns) nor the N6b-i `cls_fall` shape
    (which needs an empty `case 0` falling into a const `case 1`) nor
    `cls_dense` matches, so the `forbiddenOp` switch branch fires. -/
def advSwitchFallthrough : String :=
  "module {\n  cir.func @sf(%arg0: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    cir.switch(%arg0 : !u32i) {\n      cir.case(equal, [#cir.int<0> : !u32i]) {\n        cir.return %arg0 : !u32i\n      }\n      cir.case(equal, [#cir.int<2> : !u32i]) {\n        cir.scope {\n        }\n      }\n      cir.case(default, []) {\n        cir.return %arg0 : !u32i\n      }\n    }\n    cir.return %arg0 : !u32i\n  }\n}"

/-- Lowerable switch text but wrong signature (two params): passes the
    `forbiddenOp` exemption, then fails shape admission with the
    switch-specific message. -/
def advSwitchArity : String :=
  "module {\n  cir.func @sa(%arg0: !u32i {llvm.noundef}, %arg1: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    cir.switch(%arg0 : !u32i) {\n      cir.case(equal, [#cir.int<0> : !u32i]) {\n        %a = cir.const #cir.int<10> : !u32i\n        cir.return %a : !u32i\n      }\n      cir.case(equal, [#cir.int<1> : !u32i]) {\n        %b = cir.const #cir.int<20> : !u32i\n        cir.return %b : !u32i\n      }\n      cir.case(default, []) {\n        %c = cir.const #cir.int<30> : !u32i\n        cir.return %c : !u32i\n      }\n    }\n    cir.return %arg0 : !u32i\n  }\n}"

/-- `break` inside nested loops: excluded from the nested shape (no
    loop-exits there) and from the skip shape (two bounds + `cir.mul`),
    so the break/continue-specific message fires. -/
def advBreakNested : String :=
  "module {\n  cir.func @bnn(%arg0: !u32i {llvm.noundef}, %arg1: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    cir.for : cond {\n      cir.condition(%arg0)\n    } body {\n      cir.for : cond {\n        cir.condition(%arg1)\n      } body {\n        cir.break loc(#loc1)\n        cir.yield loc(#loc2)\n      } step {\n        cir.yield loc(#loc3)\n      }\n      cir.yield loc(#loc4)\n    } step {\n      cir.yield loc(#loc5)\n    }\n    %m = cir.mul %arg0, %arg1 : !u32i\n    cir.return %m : !u32i\n  }\n}"

/-- Single-return search loop (no early return): three params defeat
    the `sum` shape, the missing second return defeats `find_eq`;
    `cir.ptr_stride` without the admitted bound form is `oob-possible`. -/
def advSearchNoReturn : String :=
  "module {\n  cir.func @snr(%arg0: !cir.ptr<!u32i> {llvm.noalias} {llvm.noundef}, %arg1: !u64i {llvm.noundef}, %arg2: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    cir.for : cond {\n      cir.condition(%arg1)\n    } body {\n      %p = cir.ptr_stride %arg0 : !cir.ptr<!u32i>\n      cir.yield loc(#loc1)\n    } step {\n      cir.yield loc(#loc2)\n    }\n    cir.return %arg2 : !u32i\n  }\n}"

/-- `switch` on a range case: not equality-lowerable. -/
def advSwitchRange : String :=
  "module {\n  cir.func @sr(%arg0: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    cir.switch(%arg0 : !u32i) {\n      cir.case(range, [#cir.int<0> : !u32i, #cir.int<5> : !u32i]) {\n        cir.return %arg0 : !u32i\n      }\n      cir.case(default, []) {\n        cir.return %arg0 : !u32i\n      }\n    }\n    cir.return %arg0 : !u32i\n  }\n}"

/-- `cls`-shaped `switch` with unsigned arithmetic in a case body: the
    region pins pass but `arithOpCount == 0` fails (N6b-i closes the
    unsigned-arith hole — plain `cir.add` used to slip past the
    `nsw`/`cir.mul` exclusions and validate to `clsFunc`). -/
def advSwitchArith : String :=
  "module {\n  cir.func @sx(%arg0: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    cir.switch(%arg0 : !u32i) {\n      cir.case(equal, [#cir.int<0> : !u32i]) {\n        %t = cir.add %arg0, %arg0 : !u32i\n        %a = cir.const #cir.int<10> : !u32i\n        cir.return %a : !u32i\n      }\n      cir.case(equal, [#cir.int<1> : !u32i]) {\n        %b = cir.const #cir.int<20> : !u32i\n        cir.return %b : !u32i\n      }\n      cir.case(default, []) {\n        %c = cir.const #cir.int<30> : !u32i\n        cir.return %c : !u32i\n      }\n    }\n    cir.return %arg0 : !u32i\n  }\n}"

/-- Permuted const mapping: every pinned const is present, but `case 0`
    returns `30` and `default` returns `10` — the N6b-i per-region pins
    (not the old whole-text pins) reject it, so no canonical body can
    miscompile it. -/
def advSwitchPermuted : String :=
  "module {\n  cir.func @sp(%arg0: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    cir.switch(%arg0 : !u32i) {\n      cir.case(equal, [#cir.int<0> : !u32i]) {\n        %a = cir.const #cir.int<30> : !u32i\n        cir.return %a : !u32i\n      }\n      cir.case(equal, [#cir.int<1> : !u32i]) {\n        %b = cir.const #cir.int<20> : !u32i\n        cir.return %b : !u32i\n      }\n      cir.case(default, []) {\n        %c = cir.const #cir.int<10> : !u32i\n        cir.return %c : !u32i\n      }\n    }\n    cir.return %arg0 : !u32i\n  }\n}"

/-- Double-`10` mapping: `case 0` and `case 1` both return `10`, so the
    text matches neither the `cls` region pins (`case 1` needs `20`)
    nor the `cls_fall` emptiness pin (`case 0` is non-empty) — the
    shared-structure overlap validates to no canonical body. -/
def advSwitchDoubleTen : String :=
  "module {\n  cir.func @sd(%arg0: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    cir.switch(%arg0 : !u32i) {\n      cir.case(equal, [#cir.int<0> : !u32i]) {\n        %a = cir.const #cir.int<10> : !u32i\n        cir.return %a : !u32i\n      }\n      cir.case(equal, [#cir.int<1> : !u32i]) {\n        %b = cir.const #cir.int<10> : !u32i\n        cir.return %b : !u32i\n      }\n      cir.case(default, []) {\n        %c = cir.const #cir.int<30> : !u32i\n        cir.return %c : !u32i\n      }\n    }\n    cir.return %arg0 : !u32i\n  }\n}"

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkFlowPipeline verdicts "tests/cir/nested_sum.cir"
    "tests/golden/NestedSum.lean" "nested_sum"
  passed := passed + c1
  let c2 ← checkFlowPipeline verdicts "tests/cir/skip_sum.cir"
    "tests/golden/SkipSum.lean" "skip_sum"
  passed := passed + c2
  let c3 ← checkFlowPipeline verdicts "tests/cir/find_eq.cir"
    "tests/golden/FindEq.lean" "find_eq"
  passed := passed + c3
  let c4 ← checkFlowPipeline verdicts "tests/cir/cls.cir"
    "tests/golden/Cls.lean" "cls"
  passed := passed + c4
  let c5 ← checkFlowPipeline verdicts "tests/cir/cls_fall.cir"
    "tests/golden/ClsFall.lean" "cls_fall"
  passed := passed + c5
  let c6 ← checkFlowPipeline verdicts "tests/cir/cls_dense.cir"
    "tests/golden/ClsDense.lean" "cls_dense"
  passed := passed + c6
  let r1 ← checkRejectFlow "bn" advBreakNoLoop .unknown
    "out-of-subset" "`break`/`continue`"
  passed := passed + r1
  let r2 ← checkRejectFlow "sf" advSwitchFallthrough .unknown
    "out-of-subset" "`cir.switch`"
  passed := passed + r2
  let r3 ← checkRejectFlow "sa" advSwitchArity .unknown
    "out-of-subset" "admitted `cls` shape"
  passed := passed + r3
  let r4 ← checkRejectFlow "bnn" advBreakNested .unknown
    "out-of-subset" "`break`/`continue`"
  passed := passed + r4
  let r5 ← checkRejectFlow "snr" advSearchNoReturn .noalias
    "oob-possible" "ptr_stride"
  passed := passed + r5
  let r6 ← checkRejectFlow "sr" advSwitchRange .unknown
    "out-of-subset" "`cir.switch`"
  passed := passed + r6
  let r7 ← checkRejectFlow "sx" advSwitchArith .unknown
    "out-of-subset" "`cir.switch`"
  passed := passed + r7
  let r8 ← checkRejectFlow "sp" advSwitchPermuted .unknown
    "out-of-subset" "`cir.switch`"
  passed := passed + r8
  let r9 ← checkRejectFlow "sd" advSwitchDoubleTen .unknown
    "out-of-subset" "`cir.switch`"
  passed := passed + r9
  IO.println s!"GOLDENFLOW-OK passed={passed}"

end GoldenFlow
