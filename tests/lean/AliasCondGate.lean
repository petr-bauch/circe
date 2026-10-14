-- Unknown-verdict branch-writer gate (G3/S3 admission predicate):
-- `isAliasCondShape` accepts exactly one corpus function and rejects
-- the near-miss shapes with identical op counts.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `AliasCondGate.main`).
-- The predicate `isAliasCondShape` accepts `alias_cond` (two
-- single-reference-triple params plus `bool`, one scope-wrapped
-- `cir.if` firing the first writer run with the in-order dataflow
-- pin, the second run at top level — five loads, since C++ refs fuse
-- the deref chain) and rejects the `noalias` `cond_pair` (seven
-- loads, triple absent), the unbranched `wr_pair`, the single-writer
-- `incr`, the borrow-return `choose`, the two-reader `sum_two`, and
-- the C++ `alias_reborrow` corpus shapes. The adversarial rows pin
-- the branch half: fully-conditional pair (the re-read would observe
-- the wrong store), run 1 outside (the masked `p + 1` would lie),
-- condition on the wrong cell, and same-cell writers. Admission
-- under `unknown` and `mayAlias` plus the near-miss message routing
-- are pinned too.
import Circe.Validator

namespace AliasCondGate

def checkPred (cir name : String) (want : Bool) : IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"aliascond-gate: parse failed for {cir}")
    | some r => pure r
  match raw.funcs.find? (fun f => f.name == name) with
  | none =>
    throw (IO.userError s!"aliascond-gate: {cir}: no definition {name}")
  | some func =>
    let got := isAliasCondShape func
    if got != want then
      throw (IO.userError s!"aliascond-gate: {cir}:{name}: pred {got} != {want}")
    IO.println s!"PASS aliascond-pred {name} ({got})"
    pure 1

/-- Adversarial predicate row: transformed corpus text must reject. -/
def checkAdvPred (tag : String) (text : String) : IO Nat := do
  match parseModule text with
  | none => throw (IO.userError s!"aliascond-gate: {tag}: parse failed")
  | some raw =>
    match raw.funcs.find? (fun f => f.name == "_Z10alias_condRiS_b") with
    | none => throw (IO.userError s!"aliascond-gate: {tag}: no definition")
    | some func =>
      if isAliasCondShape func then
        throw (IO.userError s!"aliascond-gate: {tag}: unsound accept")
      IO.println s!"PASS aliascond-adv {tag} (false)"
      pure 1

def run1 : String :=
  "        %8 = cir.const #cir.int<1> : !s32i loc(#loc14)\n" ++
  "        %9 = cir.load %0 : !cir.ptr<!cir.ptr<!s32i>>, !cir.ptr<!s32i> loc(#loc15)\n" ++
  "        %10 = cir.load align(4) %9 : !cir.ptr<!s32i>, !s32i loc(#loc16)\n" ++
  "        %11 = cir.add nsw %10, %8 : !s32i loc(#loc26)\n" ++
  "        cir.store align(4) %11, %9 : !s32i, !cir.ptr<!s32i> loc(#loc26)\n"

def run2 : String :=
  "    %3 = cir.const #cir.int<2> : !s32i loc(#loc17)\n" ++
  "    %4 = cir.load %1 : !cir.ptr<!cir.ptr<!s32i>>, !cir.ptr<!s32i> loc(#loc18)\n" ++
  "    %5 = cir.load align(4) %4 : !cir.ptr<!s32i>, !s32i loc(#loc19)\n" ++
  "    %6 = cir.add nsw %5, %3 : !s32i loc(#loc27)\n" ++
  "    cir.store align(4) %6, %4 : !s32i, !cir.ptr<!s32i> loc(#loc27)\n"

def checkAdmitV (cir name : String) (verdict : Verdict) : IO Nat := do
  let text ← IO.FS.readFile cir
  match validateModule text [⟨name, verdict⟩] with
  | [(n, .ok _)] =>
    if n != name then
      throw (IO.userError s!"aliascond-gate: {cir}: admitted {n} != {name}")
    IO.println s!"PASS aliascond-admit {n}"
    pure 1
  | rows =>
    throw (IO.userError s!"aliascond-gate: {cir}: expected single admission, got {rows.length} rows")

def checkMsg (tag text needle : String) : IO Nat := do
  match parseModule text with
  | none => throw (IO.userError s!"aliascond-gate: {tag}: parse failed")
  | some _ =>
    match validateModule text [⟨"_Z10alias_condRiS_b", .unknown⟩] with
    | [(_, .error rej)] =>
      if !containsSubstr rej.message needle then
        throw (IO.userError s!"aliascond-gate: {tag}: message missing {needle}")
      IO.println s!"PASS aliascond-msg {tag}"
      pure 1
    | rows =>
      throw (IO.userError s!"aliascond-gate: {tag}: expected single rejection, got {rows.length} rows")

def main : IO Unit := do
  let mut passed := 0
  let c ← checkPred "tests/cir/alias_cond.cir" "_Z10alias_condRiS_b" true
  passed := passed + c
  let c ← checkPred "tests/cir/cond_pair.cir" "cond_pair" false
  passed := passed + c
  let c ← checkPred "tests/cir/wr_pair.cir" "wr_pair" false
  passed := passed + c
  let c ← checkPred "tests/cir/incr_ptr.cir" "incr" false
  passed := passed + c
  let c ← checkPred "tests/cir/choose_ptr.cir" "choose" false
  passed := passed + c
  let c ← checkPred "tests/cir/sum_two.cir" "sum_two" false
  passed := passed + c
  let c ← checkPred "tests/cir/alias_reborrow.cir" "_Z14alias_reborrowRi" false
  passed := passed + c
  let base ← IO.FS.readFile "tests/cir/alias_cond.cir"
  -- Fully conditional: run 2 moved inside the `if` region (the
  -- unconditional `q + 2` re-read would observe the wrong store).
  let c ← checkAdvPred "both-inside"
    ((base.replace run2 "").replace "      } loc(#loc25)" (run2 ++ "      } loc(#loc25)"))
  passed := passed + c
  -- Run 1 unconditional: moved after the scope close (the masked
  -- `p + 1` would lie when `c = false`).
  let c ← checkAdvPred "run1-outside"
    ((base.replace run1 "").replace "    } loc(#loc24)" ("    } loc(#loc24)\n" ++ run1))
  passed := passed + c
  -- Condition reads `p`'s cell instead of `c`.
  let c ← checkAdvPred "cond-on-p"
    (base.replace "%7 = cir.load align(1) %2" "%7 = cir.load align(1) %0")
  passed := passed + c
  -- Same-cell writers (both runs into `p`'s cell).
  let c ← checkAdvPred "same-cell"
    (base.replace "%4 = cir.load %1" "%4 = cir.load %0")
  passed := passed + c
  let c ← checkAdmitV "tests/cir/alias_cond.cir" "_Z10alias_condRiS_b" .unknown
  passed := passed + c
  let c ← checkAdmitV "tests/cir/alias_cond.cir" "_Z10alias_condRiS_b" .mayAlias
  passed := passed + c
  -- The near-miss keeps a rejection (never admission): the triple
  -- params never reach the verdict gate, so the generic fragment
  -- tail fires.
  let c ← checkMsg "both-inside"
    ((base.replace run2 "").replace "      } loc(#loc25)" (run2 ++ "      } loc(#loc25)"))
    "admitted Phase-4 fragment"
  passed := passed + c
  IO.println s!"ALIASCONDGATE-OK passed={passed}"

end AliasCondGate
