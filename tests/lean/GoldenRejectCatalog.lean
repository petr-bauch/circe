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
  IO.println s!"GOLDENREJECTCATALOG-OK passed={passed}"

end GoldenRejectCatalog
