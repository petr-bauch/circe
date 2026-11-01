-- Golden test for first-match erase (`list_erase` over caller-owned
-- `Node {val, next}` with `free`): pillar-1 goal #2, first
-- deallocating shape (dangling-loud discipline: the victim is freed
-- and the (possibly new) head returned; a miss returns the head
-- untouched).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListErase.main`).
-- 1. Corpus pipeline: `tests/cir/list_erase.cir` (real CIRGen output:
--    `Node* head` + `i32 val` in, `Node*` out; 5 allocas, 19 loads,
--    10 stores, one `while`, two `cir.if`, 5 `get_member`, one
--    `cir.call @free` + `get_global`, 3 `cir.const` (loop/unlink
--    guards), 3 `cir.cmp`, one `cast`, no `cir.return` in the miss
--    arm beyond the shared tail) validates via `runModulePipeline`
--    with an `unknown` oracle fact and emits byte-identical text to
--    `tests/golden/ListErase.lean`.
-- 2. Rejection suite: three-pointer variant (one more live pointer
--    — the offender gate fires: `alias-reject`); double-free
--    variant (the victim is freed twice — the count gate fires:
--    `out-of-subset`); sibling texts are not erase-shaped and
--    `list_erase` text is not sibling-shaped (shape-exactness both
--    directions).
import Circe.Validator

namespace GoldenListErase

def eraseFact : OracleFact := ⟨"_Z10list_eraseP4Nodei", .unknown⟩

def checkListErasePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_erase.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListErase.lean"
  match runModulePipeline text [eraseFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_erase: {msg}")
  | .ok [("_Z10list_eraseP4Nodei", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_erase entry")
    IO.println "PASS pipeline list_erase (entry, unknown oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListErase (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-erase: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-erase: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-erase: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-erase {name} [{code}]"
    pure 1

/-- Three-pointer variant: the corpus signature plus a third bare
    `Node*` param. Same body, one more live pointer — the offender
    gate fires first (a bare pointer among two live ones cannot be
    discharged): `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6])"
    "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6]), %arg2: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc5, #loc6])"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_erase.cir"
  checkRejectListErase "_Z10list_eraseP4Nodei" (advThreePtr text) .unknown
    "alias-reject" "__restrict__"

/-- Double-free variant: the victim is freed twice. The count
    gate fires (`out-of-subset`): heap blocks are freed at most
    once — the dangling-loud discipline for the first deallocating
    shape. -/
def advDoubleFree (text : String) : String :=
  text.replace "cir.call @free(%20) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc68)"
    "cir.call @free(%20) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc68)\n              cir.call @free(%20) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc68)"

def checkDoubleFreeRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_erase.cir"
  checkRejectListErase "_Z10list_eraseP4Nodei" (advDoubleFree text) .unknown
    "out-of-subset" "more times than"

/-- Sibling texts are not erase-shaped (writer legs with
    caller-provided nodes / read-only chases / the allocating cons,
    not the chase-unlink-free-return). -/
def checkSibsNotListErase : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/list_append.cir", "list_append"),
      ("tests/cir/list_length.cir", "list_length"),
      ("tests/cir/linked_reverse.cir", "linked_reverse"),
      ("tests/cir/list_rev.cir", "list_rev"),
      ("tests/cir/push_front.cir", "push_front")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-erase: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isListEraseShape then
        throw (IO.userError s!"reject-erase: {nm} text wrongly eraseshaped")
      IO.println s!"PASS reject-erase {nm}-not-erase [shape-exact]"
      n := n + 1
  pure n

/-- `list_erase` text is not sibling-shaped (first-match unlink +
    free, not a caller-node swing, a read-only count, an in-place
    chase, or an allocating cons). -/
def checkListEraseNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_erase.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-erase: list_erase corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10list_eraseP4Nodei") with
    | none =>
      throw (IO.userError "reject-erase: list_erase not found")
    | some raw =>
      if isListAppendShape raw then
        throw (IO.userError "reject-erase: list_erase text wrongly listappend-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-erase: list_erase text wrongly listlength-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-erase: list_erase text wrongly linkedreverse-shaped")
      if isPushFrontShape raw then
        throw (IO.userError "reject-erase: list_erase text wrongly pushfront-shaped")
      IO.println "PASS reject-erase erase-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListErasePipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkDoubleFreeRejects
  passed := passed + r2
  let r3 ← checkSibsNotListErase
  passed := passed + r3
  let r4 ← checkListEraseNotSibs
  passed := passed + r4
  IO.println s!"GOLDENLISTERASE-OK passed={passed}"

end GoldenListErase
