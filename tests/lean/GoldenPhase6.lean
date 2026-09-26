-- Golden test for Phase 6: extended rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenPhase6.lean`
-- Covers every `forbiddenOp` branch that Phase 4's suite (`GoldenPhase4`)
-- left untested — volatile/atomics/inline-asm, `double`, `int_to_ptr`,
-- `landingpad`, `void*` returns — plus the Phase 6 additions: heap
-- (`malloc`/`free`), `setjmp`/`longjmp`, globals, function pointers, VLAs,
-- variadics, `switch`, `goto` (`cir.br`), bitfields, and signed wrapping
-- arithmetic without `nsw`. Every case asserts rejection with the exact
-- code plus a message substring, so each `validate` branch is exercised.
-- Mismatch policy: any in-subset C → Lean divergence is P0; everything
-- here must reject loudly (never silently model memory).
import Circe.Validator

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkReject6 (name text : String) (verdict : Verdict) (code substr : String) :
    IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-suite6: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-suite6: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-suite6: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject6 {name} [{code}]"
    pure 1

def advVolatile : String :=
  "module {\n  cir.func @vol(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %v = cir.load volatile %arg0 : !s32i, !s32i\n    cir.return %v : !s32i\n  }\n}"

def advAtomic : String :=
  "module {\n  cir.func @atm(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %v = cir.load atomic %arg0 : !s32i, !s32i\n    cir.return %v : !s32i\n  }\n}"

def advInlineAsm : String :=
  "module {\n  cir.func @iasm(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %v = inline_asm \"nop\" : -> !s32i\n    cir.return %v : !s32i\n  }\n}"

def advDouble : String :=
  "module {\n  cir.func @dbl(%arg0: !cir.double {llvm.noundef}) -> !cir.double attributes {\"nothrow\"} {\n    cir.return %arg0 : !cir.double\n  }\n}"

def advIntToPtr : String :=
  "module {\n  cir.func @itp(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %p = cir.cast int_to_ptr %arg0 : !s32i -> !cir.ptr<!s32i>\n    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n    cir.return %v : !s32i\n  }\n}"

def advLandingPad : String :=
  "module {\n  cir.func @lpad(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %e = landingpad { i8*, i32 } cleanup\n    cir.return %arg0 : !s32i\n  }\n}"

def advVoidStarRet : String :=
  "module {\n  cir.func @vr(%arg0: !s32i {llvm.noundef}) -> !cir.ptr<!cir.void> attributes {\"nothrow\"} {\n    cir.return %arg0 : !cir.ptr<!cir.void>\n  }\n}"

def advMalloc : String :=
  "module {\n  cir.func @mk(%arg0: !u64i {llvm.noundef}) -> !u64i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.return %arg0 : !u64i\n  }\n}"

def advFree : String :=
  "module {\n  cir.func @hf(%arg0: !cir.ptr<!s32i> {llvm.noalias, llvm.noundef}) attributes {\"nothrow\"} {\n    cir.call @free(%arg0) : (!cir.ptr<!s32i>) -> ()\n    cir.return\n  }\n}"

def advGlobal : String :=
  "module {\n  cir.global @g : !s32i\n  cir.func @gr() -> !s32i attributes {\"nothrow\"} {\n    %p = cir.get_global @g : !cir.ptr<!s32i>\n    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n    cir.return %v : !s32i\n  }\n}"

def advFuncPtr : String :=
  "module {\n  cir.func @fp(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %r = cir.call_indirect %arg0(%arg0) : (!s32i) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

def advVla : String :=
  "module {\n  cir.func @vla(%arg0: !u64i {llvm.noundef}) -> !u64i attributes {\"nothrow\"} {\n    %tok = cir.stack_save\n    %a = cir.alloca \"v\" : !cir.ptr<!s32i>\n    cir.stack_restore %tok : !u64i\n    cir.return %arg0 : !u64i\n  }\n}"

def advVariadic : String :=
  "module {\n  cir.func @var(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %a = cir.va_arg %arg0 : !s32i -> !s32i\n    cir.return %a : !s32i\n  }\n}"

def advSwitch : String :=
  "module {\n  cir.func @sw(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %r = cir.switch %arg0 : !s32i\n    cir.return %r : !s32i\n  }\n}"

def advGoto : String :=
  "module {\n  cir.func @gt(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    cir.br ^bb1\n  ^bb1:\n    %s = cir.add nsw %arg0, %arg1 : !s32i\n    cir.return %s : !s32i\n  }\n}"

def advBitfield : String :=
  "module {\n  cir.func @bf(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %v = cir.extract_bitfield %arg0[0:3] : !s32i -> !s32i\n    cir.return %v : !s32i\n  }\n}"

def advWrappingAdd : String :=
  "module {\n  cir.func @wadd(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %s = cir.add %arg0, %arg1 : !s32i\n    cir.return %s : !s32i\n  }\n}"

def advSetjmp : String :=
  "module {\n  cir.func @sj(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %r = cir.call @setjmp(%arg0) : (!s32i) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c1 ← checkReject6 "vol" advVolatile .unknown
    "out-of-subset" "volatile"
  passed := passed + c1
  let c2 ← checkReject6 "atm" advAtomic .unknown
    "out-of-subset" "atomic"
  passed := passed + c2
  let c3 ← checkReject6 "iasm" advInlineAsm .unknown
    "out-of-subset" "inline assembly"
  passed := passed + c3
  let c4 ← checkReject6 "dbl" advDouble .unknown
    "out-of-subset" "double"
  passed := passed + c4
  let c5 ← checkReject6 "itp" advIntToPtr .unknown
    "out-of-subset" "cast"
  passed := passed + c5
  let c6 ← checkReject6 "lpad" advLandingPad .unknown
    "out-of-subset" "exception"
  passed := passed + c6
  let c7 ← checkReject6 "vr" advVoidStarRet .unknown
    "out-of-subset" "void*"
  passed := passed + c7
  let c8 ← checkReject6 "mk" advMalloc .unknown
    "out-of-subset" "malloc"
  passed := passed + c8
  let c9 ← checkReject6 "hf" advFree .noalias
    "out-of-subset" "free"
  passed := passed + c9
  let c10 ← checkReject6 "gr" advGlobal .unknown
    "out-of-subset" "global"
  passed := passed + c10
  let c11 ← checkReject6 "fp" advFuncPtr .unknown
    "out-of-subset" "function pointer"
  passed := passed + c11
  let c12 ← checkReject6 "vla" advVla .unknown
    "out-of-subset" "VLA"
  passed := passed + c12
  let c13 ← checkReject6 "var" advVariadic .unknown
    "out-of-subset" "variadic"
  passed := passed + c13
  let c14 ← checkReject6 "sw" advSwitch .unknown
    "out-of-subset" "switch"
  passed := passed + c14
  let c15 ← checkReject6 "gt" advGoto .unknown
    "out-of-subset" "goto"
  passed := passed + c15
  let c16 ← checkReject6 "bf" advBitfield .unknown
    "out-of-subset" "bitfield"
  passed := passed + c16
  let c17 ← checkReject6 "wadd" advWrappingAdd .unknown
    "out-of-subset" "nsw"
  passed := passed + c17
  let c18 ← checkReject6 "sj" advSetjmp .unknown
    "out-of-subset" "setjmp"
  passed := passed + c18
  IO.println s!"GOLDEN6-OK passed={passed}"
