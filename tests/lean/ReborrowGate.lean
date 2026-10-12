-- Sequential-writer-pair gate (L2-admission predicate, deferred).
--
-- Run from the repo root: `lake env lean --run tests/lean/ReborrowGate.lean`
-- The predicate `isSequentialReborrowShape` accepts exactly one corpus
-- function (`alias_reborrow`: one single-reference root, three writer
-- allocas, L2-disjoint writer ranges) and rejects the overlapping
-- `alias_cond` pair (L2 comparison fails), the two-reader `sum_two`
-- (two params), the `vec_at_sum` entry (loop), and the admitted
-- `scope_early` leaf (no disjoint writer triple). Recognition routes
-- to the deferred "sequential writers" message — still a rejection
-- (mutable writers need Iris framing over `Mem`; there is no writer
-- `Func` yet) — while `alias_cond` keeps the generic fragment message.
-- The disjointness soundness lemmas
-- (`hasSequentialWriterRanges_disjoint`,
-- `isSequentialReborrowShape_disjoint`) are compile-time proofs, not
-- runtime checks.
import Circe.Validator

namespace ReborrowGate

def checkPred (cir name : String) (want : Bool) : IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"reborrow-gate: parse failed for {cir}")
    | some r => pure r
  match raw.funcs.find? (fun f => f.name == name) with
  | none =>
    throw (IO.userError s!"reborrow-gate: {cir}: no definition {name}")
  | some func =>
    let got := isSequentialReborrowShape func
    if got != want then
      throw (IO.userError s!"reborrow-gate: {cir}:{name}: pred {got} != {want}")
    IO.println s!"PASS reborrow-pred {name} ({got})"
    pure 1

def checkMsg (cir needle : String) : IO Nat := do
  let text ← IO.FS.readFile cir
  let mut n := 0
  for (name, res) in validateModule text [] do
    match res with
    | .ok _ =>
      throw (IO.userError s!"reborrow-gate: {cir}:{name}: unexpectedly admitted")
    | .error rej =>
      if !containsSubstr rej.message needle then
        throw (IO.userError s!"reborrow-gate: {cir}:{name}: message missing {needle}")
      IO.println s!"PASS reborrow-msg {name}"
      n := n + 1
  pure n

def main : IO Unit := do
  let mut passed := 0
  let c ← checkPred "tests/cir/alias_reborrow.cir" "_Z14alias_reborrowRi" true
  passed := passed + c
  let c ← checkPred "tests/cir/alias_cond.cir" "_Z10alias_condRiS_b" false
  passed := passed + c
  let c ← checkPred "tests/cir/sum_two.cir" "sum_two" false
  passed := passed + c
  let c ← checkPred "tests/cir/vec_at_sum.cir"
    "_Z10vec_at_sumRKSt6vectorIiSaIiEE" false
  passed := passed + c
  let c ← checkPred "tests/cir/scope_early.cir" "_Z11scope_earlyii" false
  passed := passed + c
  let c ← checkMsg "tests/cir/alias_reborrow.cir" "sequential writers"
  passed := passed + c
  let c ← checkMsg "tests/cir/alias_cond.cir"
    "not in the admitted Phase-4 fragment"
  passed := passed + c
  IO.println s!"REBORROWGATE-OK passed={passed}"

end ReborrowGate
