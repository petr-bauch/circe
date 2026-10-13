-- Branch-writer gate (G2b admission predicate): `isCondPairShape`
-- accepts exactly one corpus function and rejects the near-miss
-- shapes with identical op counts.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `CondPairGate.main`).
-- The predicate `isCondPairShape` accepts `cond_pair` (two
-- `__restrict__` params plus `bool`, one scope-wrapped `cir.if`
-- firing the first writer run with the in-order dataflow pin, the
-- second run at top level) and rejects the unbranched `wr_pair`,
-- the single-writer `incr`, the borrow-return `choose`, the
-- two-reader `sum_two`, and the C++ `alias_reborrow`/`alias_cond`
-- corpus shapes. The adversarial rows pin the branch half:
-- fully-conditional pair (both runs inside — the functionalized
-- `q + 2` would lie), run 1 outside (unconditional first write),
-- condition on the wrong cell, and same-cell writers (the G2
-- near-miss under a branch). Admission and the near-miss message
-- routing are pinned too.
import Circe.Validator

namespace CondPairGate

def checkPred (cir name : String) (want : Bool) : IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"condpair-gate: parse failed for {cir}")
    | some r => pure r
  match raw.funcs.find? (fun f => f.name == name) with
  | none =>
    throw (IO.userError s!"condpair-gate: {cir}: no definition {name}")
  | some func =>
    let got := isCondPairShape func
    if got != want then
      throw (IO.userError s!"condpair-gate: {cir}:{name}: pred {got} != {want}")
    IO.println s!"PASS condpair-pred {name} ({got})"
    pure 1

/-- Adversarial predicate row: transformed corpus text must reject. -/
def checkAdvPred (tag : String) (text : String) : IO Nat := do
  match parseModule text with
  | none => throw (IO.userError s!"condpair-gate: {tag}: parse failed")
  | some raw =>
    match raw.funcs.find? (fun f => f.name == "cond_pair") with
    | none => throw (IO.userError s!"condpair-gate: {tag}: no definition")
    | some func =>
      if isCondPairShape func then
        throw (IO.userError s!"condpair-gate: {tag}: unsound accept")
      IO.println s!"PASS condpair-adv {tag} (false)"
      pure 1

def run1 : String :=
  "        %9 = cir.load deref align(8) %0 : !cir.ptr<!cir.ptr<!s32i>>, !cir.ptr<!s32i> loc(#loc14)\n" ++
  "        %10 = cir.load align(4) %9 : !cir.ptr<!s32i>, !s32i loc(#loc15)\n" ++
  "        %11 = cir.const #cir.int<1> : !s32i loc(#loc16)\n" ++
  "        %12 = cir.add nsw %10, %11 : !s32i loc(#loc30)\n" ++
  "        %13 = cir.load deref align(8) %0 : !cir.ptr<!cir.ptr<!s32i>>, !cir.ptr<!s32i> loc(#loc17)\n" ++
  "        cir.store align(4) %12, %13 : !s32i, !cir.ptr<!s32i> loc(#loc31)\n"

def run2 : String :=
  "    %3 = cir.load deref align(8) %1 : !cir.ptr<!cir.ptr<!s32i>>, !cir.ptr<!s32i> loc(#loc19)\n" ++
  "    %4 = cir.load align(4) %3 : !cir.ptr<!s32i>, !s32i loc(#loc20)\n" ++
  "    %5 = cir.const #cir.int<2> : !s32i loc(#loc21)\n" ++
  "    %6 = cir.add nsw %4, %5 : !s32i loc(#loc32)\n" ++
  "    %7 = cir.load deref align(8) %1 : !cir.ptr<!cir.ptr<!s32i>>, !cir.ptr<!s32i> loc(#loc22)\n" ++
  "    cir.store align(4) %6, %7 : !s32i, !cir.ptr<!s32i> loc(#loc33)\n"

def checkAdmit (cir name : String) : IO Nat := do
  let text ← IO.FS.readFile cir
  match validateModule text [⟨name, .noalias⟩] with
  | [(n, .ok _)] =>
    if n != name then
      throw (IO.userError s!"condpair-gate: {cir}: admitted {n} != {name}")
    IO.println s!"PASS condpair-admit {n}"
    pure 1
  | rows =>
    throw (IO.userError s!"condpair-gate: {cir}: expected single admission, got {rows.length} rows")

def checkMsg (tag text needle : String) : IO Nat := do
  let mut n := 0
  for (name, res) in validateModule text [⟨"cond_pair", .noalias⟩] do
    match res with
    | .ok _ =>
      throw (IO.userError s!"condpair-gate: {tag}:{name}: unexpectedly admitted")
    | .error rej =>
      if !containsSubstr rej.message needle then
        throw (IO.userError s!"condpair-gate: {tag}:{name}: message missing {needle}")
      IO.println s!"PASS condpair-msg {name}"
      n := n + 1
  pure n

def main : IO Unit := do
  let mut passed := 0
  let c ← checkPred "tests/cir/cond_pair.cir" "cond_pair" true
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
  let c ← checkPred "tests/cir/alias_cond.cir" "_Z10alias_condRiS_b" false
  passed := passed + c
  let base ← IO.FS.readFile "tests/cir/cond_pair.cir"
  -- Fully conditional: run 2 moved inside the `if` region (the
  -- functionalized unconditional `q + 2` would lie).
  let c ← checkAdvPred "both-inside"
    ((base.replace run2 "").replace "      } loc(#loc29)" (run2 ++ "      } loc(#loc29)"))
  passed := passed + c
  -- Run 1 unconditional: moved after the scope close (the masked
  -- `c ? p + 1 : p` would lie when `c = false`).
  let c ← checkAdvPred "run1-outside"
    ((base.replace run1 "").replace "    } loc(#loc28)" ("    } loc(#loc28)\n" ++ run1))
  passed := passed + c
  -- Condition reads `p`'s cell instead of `c`.
  let c ← checkAdvPred "cond-on-p"
    (base.replace "%8 = cir.load align(1) %2" "%8 = cir.load align(1) %0")
  passed := passed + c
  -- Same-cell writers (the G2 near-miss under a branch).
  let c ← checkAdvPred "same-cell"
    ((base.replace "%3 = cir.load deref align(8) %1" "%3 = cir.load deref align(8) %0").replace "%7 = cir.load deref align(8) %1" "%7 = cir.load deref align(8) %0")
  passed := passed + c
  let c ← checkAdmit "tests/cir/cond_pair.cir" "cond_pair"
  passed := passed + c
  -- The near-miss keeps the pair-check rejection (never admission).
  let c ← checkMsg "both-inside"
    ((base.replace run2 "").replace "      } loc(#loc29)" (run2 ++ "      } loc(#loc29)"))
    "live pointer parameters"
  passed := passed + c
  IO.println s!"CONDPAIRGATE-OK passed={passed}"

end CondPairGate
