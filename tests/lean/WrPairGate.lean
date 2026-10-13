-- Writer-pair gate (G2 admission predicate): `isWrPairShape`
-- accepts exactly one corpus function and rejects the three
-- near-miss shapes with identical op counts.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `WrPairGate.main`).
-- The predicate `isWrPairShape` accepts `wr_pair` (two
-- `__restrict__` params, two writer runs, the in-order dataflow pin:
-- each add feeds its in-order store into its in-order param cell
-- from that same cell) and rejects the single-writer `incr` leaf,
-- the borrow-return `choose`, the two-reader `sum_two`, the C++
-- `alias_reborrow` (single-reference root) and `alias_cond`
-- (branches/scopes) corpus shapes. The adversarial rows pin the
-- dataflow half: same-cell writers (`*p += 1; *p += 2` — cells
-- equal), swapped writers (`*q += 1; *p += 2` — arg order flipped),
-- and cross reads (`*q = *p + 1` — elt source is the other cell).
-- Admission and the near-miss message routing are pinned too
-- (the wrong shape keeps the pair-check rejection, never admission).
import Circe.Validator

namespace WrPairGate

def checkPred (cir name : String) (want : Bool) : IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"wrpair-gate: parse failed for {cir}")
    | some r => pure r
  match raw.funcs.find? (fun f => f.name == name) with
  | none =>
    throw (IO.userError s!"wrpair-gate: {cir}: no definition {name}")
  | some func =>
    let got := isWrPairShape func
    if got != want then
      throw (IO.userError s!"wrpair-gate: {cir}:{name}: pred {got} != {want}")
    IO.println s!"PASS wrpair-pred {name} ({got})"
    pure 1

/-- Adversarial predicate row: transformed corpus text must reject
    (`want = false`; all three keep the op counts, so only the
    dataflow pin can catch them). -/
def checkAdvPred (tag : String) (text : String) : IO Nat := do
  match parseModule text with
  | none => throw (IO.userError s!"wrpair-gate: {tag}: parse failed")
  | some raw =>
    match raw.funcs.find? (fun f => f.name == "wr_pair") with
    | none => throw (IO.userError s!"wrpair-gate: {tag}: no definition")
    | some func =>
      if isWrPairShape func then
        throw (IO.userError s!"wrpair-gate: {tag}: unsound accept")
      IO.println s!"PASS wrpair-adv {tag} (false)"
      pure 1

def checkAdmit (cir name : String) : IO Nat := do
  let text ← IO.FS.readFile cir
  match validateModule text [⟨name, .noalias⟩] with
  | [(n, .ok _)] =>
    if n != name then
      throw (IO.userError s!"wrpair-gate: {cir}: admitted {n} != {name}")
    IO.println s!"PASS wrpair-admit {n}"
    pure 1
  | rows =>
    throw (IO.userError s!"wrpair-gate: {cir}: expected single admission, got {rows.length} rows")

def checkMsg (tag text needle : String) : IO Nat := do
  let mut n := 0
  for (name, res) in validateModule text [⟨"wr_pair", .noalias⟩] do
    match res with
    | .ok _ =>
      throw (IO.userError s!"wrpair-gate: {tag}:{name}: unexpectedly admitted")
    | .error rej =>
      if !containsSubstr rej.message needle then
        throw (IO.userError s!"wrpair-gate: {tag}:{name}: message missing {needle}")
      IO.println s!"PASS wrpair-msg {name}"
      n := n + 1
  pure n

def main : IO Unit := do
  let mut passed := 0
  let c ← checkPred "tests/cir/wr_pair.cir" "wr_pair" true
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
  let base ← IO.FS.readFile "tests/cir/wr_pair.cir"
  -- Same-cell writers: the second run reads/writes `p`'s alloca.
  let c ← checkAdvPred "same-cell"
    (base.replace "%7 = cir.load deref align(8) %1" "%7 = cir.load deref align(8) %0"
      |>.replace "%11 = cir.load deref align(8) %1" "%11 = cir.load deref align(8) %0")
  passed := passed + c
  -- Swapped writers: `%0` takes `arg1`, `%1` takes `arg0`.
  let c ← checkAdvPred "swapped"
    (base.replace "cir.store %arg0, %0" "cir.store %arg1, %0"
      |>.replace "cir.store %arg1, %1" "cir.store %arg0, %1")
  passed := passed + c
  -- Cross read: the second elt comes from `p`'s address chain.
  let c ← checkAdvPred "cross-read"
    (base.replace "%8 = cir.load align(4) %7" "%8 = cir.load align(4) %2")
  passed := passed + c
  let c ← checkAdmit "tests/cir/wr_pair.cir" "wr_pair"
  passed := passed + c
  -- The near-miss keeps the pair-check rejection (never admission).
  let c ← checkMsg "same-cell"
    (base.replace "%7 = cir.load deref align(8) %1" "%7 = cir.load deref align(8) %0"
      |>.replace "%11 = cir.load deref align(8) %1" "%11 = cir.load deref align(8) %0")
    "live pointer parameters"
  passed := passed + c
  IO.println s!"WRPAIRGATE-OK passed={passed}"

end WrPairGate
