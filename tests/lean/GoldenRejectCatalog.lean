-- Golden test for N2b: interior rejection catalog.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenRejectCatalog.lean`
-- Today's catch-all `alias-reject` becomes per-cause messages so users can
-- tell *amenable* apart from *out of scope*:
-- 1. writer+reader: two or more live pointer params outside the
--    borrow-return (`choose`) shape (code `alias-reject`);
-- 2. escaping borrow: pointer return with no pointer inputs — a fresh or
--    stack address that cannot be one of the inputs (code
--    `escape-reject`; the ambiguous-inputs case keeps the existing
--    borrow-return message, pinned in `GoldenPhase4`);
-- 3. borrow-after-free: a heap `free` on some path plus a pointer return
--    — the borrow may dangle (code `escape-reject`).
-- N2c recovery-overreach negatives: a writer without attr text still hits
-- the rule-1 gate (recovery never covers writers), and two attr-less
-- pointers hit rule-1 before cause analysis.
-- N6a-iii arithmetic catalog: leaf-shaped but unadmitted arithmetic —
-- multi-op bodies (the P0 exactness fix), unsigned div/rem, signed
-- sub/mul, shifts, bitwise, nsw-less minus — rejects with per-cause
-- messages under the `outOfSubset` code.
-- Mismatch policy: any in-subset divergence is P0; out-of-subset must
-- reject loudly.
import Circe.Validator

namespace GoldenRejectCatalog

def checkRejectCatalog (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-catalog: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-catalog: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-catalog: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-catalog {name} [{code}]"
    pure 1

/-- Writer + reader: two `noalias` pointers plus a length, `u32` return,
    loop-free — clean oracle evidence, but no admitted two-reader `Func`
    (N2a admits none yet), so the pair cannot be discharged. -/
def advWriterReader : String :=
  "module {\n  cir.func @wr(%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}, %arg1: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}, %arg2: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %c = cir.const 0 : !u32i\n    cir.return %c : !u32i\n  }\n}"

/-- Escaping borrow, fresh address: pointer return with no pointer inputs
    at all — the address cannot be one of the inputs. -/
def advEscapeFresh : String :=
  "module {\n  cir.func @ef(%arg0: !u32i {llvm.noundef}) -> !cir.ptr<!u32i> attributes {\"nothrow\"} {\n    %c = cir.const 0 : !u32i\n    cir.return %c : !u32i\n  }\n}"

/-- Borrow after free: frees a block, then returns a pointer — the borrow
    may dangle. (One `free`, no `malloc`: the double-`free` gate does not
    fire first, so this reaches the borrow-after-free cause.) -/
def advBorrowAfterFree : String :=
  "module {\n  cir.func @baf(%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}) -> !cir.ptr<!u32i> attributes {\"nothrow\"} {\n    cir.call @free(%arg0) : (!cir.ptr<!u32i>) -> ()\n    cir.return %arg0 : !cir.ptr<!u32i>\n  }\n}"

/-- Writer without attr text: recovery never covers writers, even with a
    clean oracle verdict — the rule-1 gate still fires. -/
def advWriterNoAttr : String :=
  "module {\n  cir.func @inr(%arg0: !cir.ptr<!s32i> {llvm.noundef}) attributes {\"nothrow\"} {\n    %x = cir.load %arg0 : !cir.ptr<!s32i>, !s32i\n    %s = cir.add nsw %x, %x : !s32i\n    cir.store %s, %arg0 : !s32i, !cir.ptr<!s32i>\n    cir.return\n  }\n}"

/-- Two attr-less pointers: the rule-1 evidence gate precedes cause
    analysis (writer+reader presumes text evidence for both). -/
def advTwoBarePtrs : String :=
  "module {\n  cir.func @tb(%arg0: !cir.ptr<!u32i> {llvm.noundef}, %arg1: !cir.ptr<!u32i> {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %c = cir.const 0 : !u32i\n    cir.return %c : !u32i\n  }\n}"

/-- Multi-op arithmetic leaf: `add` + `mul` on two `i32`s — matches no
    single-op gate, so the arithmetic catalog fires (previously this
    shape silently validated to a single-op body: P0). -/
def advMultiOp : String :=
  "module {\n  cir.func @mop(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %m = cir.mul nsw %arg0, %arg1 : !s32i\n    %s = cir.add nsw %m, %arg0 : !s32i\n    cir.return %s : !s32i\n  }\n}"

/-- Unsigned division: `cir.div` on `!u32i` — only signed `sdiv` exists. -/
def advUdiv : String :=
  "module {\n  cir.func @udv(%arg0: !u32i {llvm.noundef}, %arg1: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %q = cir.div %arg0, %arg1 : !u32i\n    cir.return %q : !u32i\n  }\n}"

/-- Signed remainder: `cir.rem` on `!s32i` — only `sdiv` exists. -/
def advSrem : String :=
  "module {\n  cir.func @srm(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %r = cir.rem %arg0, %arg1 : !s32i\n    cir.return %r : !s32i\n  }\n}"

/-- Signed subtraction: `cir.sub nsw` on `!s32i` — no leaf. -/
def advSub : String :=
  "module {\n  cir.func @sbb(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %d = cir.sub nsw %arg0, %arg1 : !s32i\n    cir.return %d : !s32i\n  }\n}"

/-- Signed multiplication: `cir.mul nsw` on `!s32i` — no standalone leaf
    (unsigned wrapping `cir.mul` lives only inside fused loop shapes). -/
def advMul : String :=
  "module {\n  cir.func @mll(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %p = cir.mul nsw %arg0, %arg1 : !s32i\n    cir.return %p : !s32i\n  }\n}"

/-- Shift: `cir.shift` on `!u32i` — no leaf. -/
def advShift : String :=
  "module {\n  cir.func @shf(%arg0: !u32i {llvm.noundef}, %arg1: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %s = cir.shift(left, %arg0 : !u32i, %arg1 : !u32i) -> !u32i\n    cir.return %s : !u32i\n  }\n}"

/-- Bitwise: `cir.and` on `!u32i` — no leaf. -/
def advBitwise : String :=
  "module {\n  cir.func @bwa(%arg0: !u32i {llvm.noundef}, %arg1: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %b = cir.and %arg0, %arg1 : !u32i\n    cir.return %b : !u32i\n  }\n}"

/-- Unary minus without `nsw`: wrapping negation overflow is UB, and the
    `neg` leaf requires the marker. -/
def advMinusBare : String :=
  "module {\n  cir.func @mnb(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %n = cir.minus %arg0 : !s32i\n    cir.return %n : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c1 ← checkRejectCatalog "wr" advWriterReader .noalias
    "alias-reject" "writer+reader"
  passed := passed + c1
  let c2 ← checkRejectCatalog "ef" advEscapeFresh .unknown
    "escape-reject" "escaping-borrow"
  passed := passed + c2
  let c3 ← checkRejectCatalog "baf" advBorrowAfterFree .noalias
    "escape-reject" "borrow-after-free"
  passed := passed + c3
  let c4 ← checkRejectCatalog "inr" advWriterNoAttr .noalias
    "alias-reject" "without `__restrict__`"
  passed := passed + c4
  let c5 ← checkRejectCatalog "tb" advTwoBarePtrs .noalias
    "alias-reject" "without `__restrict__`"
  passed := passed + c5
  let c6 ← checkRejectCatalog "mop" advMultiOp .unknown
    "outOfSubset" "combines 2 arithmetic ops"
  passed := passed + c6
  let c7 ← checkRejectCatalog "udv" advUdiv .unknown
    "outOfSubset" "unsigned division"
  passed := passed + c7
  let c8 ← checkRejectCatalog "srm" advSrem .unknown
    "outOfSubset" "signed remainder"
  passed := passed + c8
  let c9 ← checkRejectCatalog "sbb" advSub .unknown
    "outOfSubset" "subtraction (`cir.sub`)"
  passed := passed + c9
  let c10 ← checkRejectCatalog "mll" advMul .unknown
    "outOfSubset" "multiplication (`cir.mul`)"
  passed := passed + c10
  let c11 ← checkRejectCatalog "shf" advShift .unknown
    "outOfSubset" "shifts (`cir.shift`)"
  passed := passed + c11
  let c12 ← checkRejectCatalog "bwa" advBitwise .unknown
    "outOfSubset" "bitwise ops"
  passed := passed + c12
  let c13 ← checkRejectCatalog "mnb" advMinusBare .unknown
    "outOfSubset" "without `nsw`"
  passed := passed + c13
  IO.println s!"GOLDENREJECTCATALOG-OK passed={passed}"

end GoldenRejectCatalog
