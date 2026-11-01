-- Golden test for caller-allocated node construction (`push_front`
-- over caller-owned `Node {val, next}`): pillar-1 goal #1, admitted
-- via the single-pointer exemption (one bare `Node*` cannot alias
-- itself; the honest `unknown` oracle verdict suffices and the
-- shape arm decides admission — no blessed-listing change, unlike
-- the two-pointer `list_append` writer leg).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenPushFront.main`).
-- 1. Corpus pipeline: `tests/cir/push_front.cir` (real CIRGen
--    output: `Node* head` + `i32 val` in, `Node*` out; one
--    `cir.call @malloc` + `get_global`, one `u64` const (16), one
--    `bitcast`, two `cir.get_member` (`[0]` payload, `[1]` link),
--    4 allocas / 6 loads / 6 stores, no `cmp` — no null-check arm
--    by design) validates via `runModulePipeline` with an
--    `unknown` oracle fact and emits byte-identical text to
--    `tests/golden/PushFront.lean`.
-- 2. Rejection suite: three-pointer variant (one more live
--    pointer — the offender gate fires: `alias-reject`);
--    free-after-alloc variant (the fresh cell is freed then
--    returned — the escape gate fires: `escape-reject`
--    borrow-after-free); sibling texts are not pushfront-shaped
--    and `push_front` text is not sibling-shaped (shape-exactness
--    both directions).
import Circe.Validator

namespace GoldenPushFront

def pushFact : OracleFact := ⟨"_Z10push_frontP4Nodei", .unknown⟩

def checkPushFrontPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/push_front.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/PushFront.lean"
  match runModulePipeline text [pushFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected push_front: {msg}")
  | .ok [("_Z10push_frontP4Nodei", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for push_front entry")
    IO.println "PASS pipeline push_front (entry, unknown oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectPushFront (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-pushfr: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-pushfr: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-pushfr: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-pushfr {name} [{code}]"
    pure 1

/-- Three-pointer variant: the corpus signature plus a third bare
    `Node*` param. Same body, one more live pointer — the offender
    gate fires first (a bare pointer among two live ones cannot be
    discharged): `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6])"
    "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6]), %arg2: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc5, #loc6])"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/push_front.cir"
  checkRejectPushFront "_Z10push_frontP4Nodei" (advThreePtr text) .unknown
    "alias-reject" "__restrict__"

/-- Free-after-alloc variant: the fresh cell is freed, then the
    (dangling) cell is returned. The escape gate fires
    (`borrow-after-free`): a freed heap block's address cannot be
    returned. -/
def advFreeRet (text : String) : String :=
  text.replace "    cir.return %15 : !cir.ptr<!rec_Node> loc(#loc33)"
    "    cir.call @free(%6) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc33)\n    cir.return %15 : !cir.ptr<!rec_Node> loc(#loc33)"

def checkFreeRetRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/push_front.cir"
  checkRejectPushFront "_Z10push_frontP4Nodei" (advFreeRet text) .unknown
    "escape-reject" "borrow-after-free"

/-- Sibling texts are not pushfront-shaped (writer legs with
    caller-provided nodes / read-only chase, not the allocating
    cons). -/
def checkSibsNotPushFront : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/list_append.cir", "list_append"),
      ("tests/cir/list_length.cir", "list_length"),
      ("tests/cir/linked_reverse.cir", "linked_reverse"),
      ("tests/cir/list_rev.cir", "list_rev")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-pushfr: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isPushFrontShape then
        throw (IO.userError s!"reject-pushfr: {nm} text wrongly pushfront-shaped")
      IO.println s!"PASS reject-pushfr {nm}-not-pushfront [shape-exact]"
      n := n + 1
  pure n

/-- `push_front` text is not sibling-shaped (allocating cons, not a
    caller-node swing, a read-only count, or an in-place chase). -/
def checkPushFrontNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/push_front.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-pushfr: push_front corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10push_frontP4Nodei") with
    | none =>
      throw (IO.userError "reject-pushfr: push_front not found")
    | some raw =>
      if isListAppendShape raw then
        throw (IO.userError "reject-pushfr: push_front text wrongly listappend-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-pushfr: push_front text wrongly listlength-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-pushfr: push_front text wrongly linkedreverse-shaped")
      IO.println "PASS reject-pushfr pushfront-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkPushFrontPipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkFreeRetRejects
  passed := passed + r2
  let r3 ← checkSibsNotPushFront
  passed := passed + r3
  let r4 ← checkPushFrontNotSibs
  passed := passed + r4
  IO.println s!"GOLDENPUSHFRONT-OK passed={passed}"

end GoldenPushFront
