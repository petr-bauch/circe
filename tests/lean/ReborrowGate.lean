-- Sequential-writer-pair gate (L2-admission predicate; F1 admits the
-- exact shape).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `ReborrowGate.main`).
-- The predicate `isSequentialReborrowShape` accepts exactly one corpus
-- function (`alias_reborrow`: one single-reference root, three writer
-- allocas, L2-disjoint writer ranges) and rejects the overlapping
-- `alias_cond` pair (L2 comparison fails), the two-reader `sum_two`
-- (two params), the `vec_at_sum` entry (loop), and the admitted
-- `scope_early` leaf (no disjoint writer triple). Since F1, the exact
-- `isReborrowShape` admits `alias_reborrow` (single check below);
-- non-exact sequential writers keep the deferred "sequential writers"
-- message. The overlapping `alias_cond` pair admits since G3/S3 via
-- the open contract (admit row below), never via reborrow. The disjointness soundness lemmas
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

def checkAdmit (cir name : String) : IO Nat := do
  let text ← IO.FS.readFile cir
  match validateModule text [] with
  | [(n, .ok _)] =>
    if n != name then
      throw (IO.userError s!"reborrow-gate: {cir}: admitted {n} != {name}")
    IO.println s!"PASS reborrow-admit {n}"
    pure 1
  | rows =>
    throw (IO.userError s!"reborrow-gate: {cir}: expected single admission, got {rows.length} rows")

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
  let c ← checkAdmit "tests/cir/alias_reborrow.cir" "_Z14alias_reborrowRi"
  passed := passed + c
  -- Overlapping writers are not reborrow-shaped (pred row above
  -- still pins `false`), but since G3/S3 they admit via the open
  -- contract — even with no oracle facts (triple params default to
  -- `unknown`, which the address case-split covers).
  let c ← checkAdmit "tests/cir/alias_cond.cir" "_Z10alias_condRiS_b"
  passed := passed + c
  IO.println s!"REBORROWGATE-OK passed={passed}"

end ReborrowGate
