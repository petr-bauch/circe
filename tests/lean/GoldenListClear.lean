-- Golden test for whole-chain free (`list_clear` over caller-owned
-- `Node {val, next}`): pillar-1 proposed goal #1, free leg (every
-- node freed exactly once, link saved before the free, payload
-- never read; returns null).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListClear.main`).
-- 1. Corpus pipeline: `tests/cir/list_clear.cir` (real CIRGen
--    output: `Node* head` in, `Node*` out = null; 4 allocas,
--    7 loads, 5 stores, one `while`, no `cir.if`, 1 `cir.cmp`
--    (guard `ne`), 1 `cir.get_member` (`[1]` link only), 2
--    `cir.const`, 1 bitcast, 1 call (`@free`), no `@malloc`)
--    validates via `runModulePipeline` with an `unknown`
--    oracle fact and emits byte-identical text to
--    `tests/golden/ListClear.lean`.
-- 2. Rejection suite: three-pointer variant (one more live
--    pointer — the offender gate fires: `alias-reject`);
--    return-the-freed-head variant (the escape gate fires:
--    `escape-reject`); double-free variant (the subset gate
--    fires: `out-of-subset`); sibling texts are not clear-shaped
--    and `list_clear` text is not sibling-shaped
--    (shape-exactness both directions).
import Circe.Validator

namespace GoldenListClear

def clearFact : OracleFact := ⟨"_Z10list_clearP4Node", .unknown⟩

def checkListClearPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_clear.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListClear.lean"
  match runModulePipeline text [clearFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_clear: {msg}")
  | .ok [("_Z10list_clearP4Node", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_clear entry")
    IO.println "PASS pipeline list_clear (entry, unknown oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListClear (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-clear: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-clear: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-clear: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-clear {name} [{code}]"
    pure 1

/-- Three-pointer variant: the corpus signature plus a second bare
    `Node*` param. Same body, one more live pointer — the offender
    gate fires first (a bare pointer among two live ones cannot be
    discharged): `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"
    "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4]), %arg1: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_clear.cir"
  checkRejectListClear "_Z10list_clearP4Node" (advThreePtr text) .unknown
    "alias-reject" "__restrict__"

/-- Return-the-freed-head variant: reload the head slot at the
    exit and return it. The escape gate fires: a freed heap
    block's address cannot be returned. -/
def advReturnFreedHead (text : String) : String :=
  text.replace "cir.return %5 : !cir.ptr<!rec_Node> loc(#loc36)"
    "%99 = cir.load %0 : !cir.ptr<!cir.ptr<!rec_Node>>, !cir.ptr<!rec_Node> loc(#loc36)\n    cir.return %99 : !cir.ptr<!rec_Node> loc(#loc36)"

def checkReturnFreedHeadRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_clear.cir"
  checkRejectListClear "_Z10list_clearP4Node" (advReturnFreedHead text) .unknown
    "escape-reject" "frees a heap block"

/-- Double-free variant: the free call issued twice on the same
    cursor. The subset gate fires: heap blocks are freed at most
    once. -/
def advDoubleFree (text : String) : String :=
  text.replace "cir.call @free(%12) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc34)"
    "cir.call @free(%12) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc34)\n          cir.call @free(%12) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc34)"

def checkDoubleFreeRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_clear.cir"
  checkRejectListClear "_Z10list_clearP4Node" (advDoubleFree text) .unknown
    "out-of-subset" "calls `free` more times"

/-- Sibling texts are not clear-shaped (no whole-chain `free`:
    read-only traversals, the allocating cons, the unlink +
    free with a value compare, the copy with `@malloc`). -/
def checkSibsNotListClear : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/list_copy.cir", "list_copy"),
      ("tests/cir/list_find.cir", "list_find"),
      ("tests/cir/list_erase.cir", "list_erase"),
      ("tests/cir/list_append.cir", "list_append"),
      ("tests/cir/list_length.cir", "list_length"),
      ("tests/cir/linked_reverse.cir", "linked_reverse"),
      ("tests/cir/list_rev.cir", "list_rev"),
      ("tests/cir/push_front.cir", "push_front")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-clear: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isListClearShape then
        throw (IO.userError s!"reject-clear: {nm} text wrongly clear-shaped")
      IO.println s!"PASS reject-clear {nm}-not-clear [shape-exact]"
      n := n + 1
  pure n

/-- `list_clear` text is not sibling-shaped (a whole-chain free
    with no read of the payload, no value compare, no store, no
    allocation). -/
def checkListClearNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_clear.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-clear: list_clear corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10list_clearP4Node") with
    | none =>
      throw (IO.userError "reject-clear: list_clear not found")
    | some raw =>
      if isListCopyShape raw then
        throw (IO.userError "reject-clear: list_clear text wrongly copy-shaped")
      if isListFindShape raw then
        throw (IO.userError "reject-clear: list_clear text wrongly find-shaped")
      if isListEraseShape raw then
        throw (IO.userError "reject-clear: list_clear text wrongly erase-shaped")
      if isListAppendShape raw then
        throw (IO.userError "reject-clear: list_clear text wrongly listappend-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-clear: list_clear text wrongly listlength-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-clear: list_clear text wrongly linkedreverse-shaped")
      if isPushFrontShape raw then
        throw (IO.userError "reject-clear: list_clear text wrongly pushfront-shaped")
      IO.println "PASS reject-clear clear-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListClearPipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkReturnFreedHeadRejects
  passed := passed + r2
  let r3 ← checkDoubleFreeRejects
  passed := passed + r3
  let r4 ← checkSibsNotListClear
  passed := passed + r4
  let r5 ← checkListClearNotSibs
  passed := passed + r5
  IO.println s!"GOLDENLISTCLEAR-OK passed={passed}"

end GoldenListClear
