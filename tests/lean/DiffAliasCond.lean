-- Differential test for the open-contract admission (G3/S3): the
-- executable open-contract mirror vs `Mem` evaluation of the emitted
-- body vs the native C++ binary, under both verdicts.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffAliasCond.main [bin trials]`).
-- Every trial runs three independent paths: `aliasCondSpec` (the
-- mirror), `memEvalStmtFuel` over `aliasCondFunc.body` (pinned entry
-- for disjoint trials via `bindMemArgs`, shared-cell caller `Mem`
-- for aliased trials — the emitted body itself, not the mirror),
-- and, when the evaluated adds are `.ok`, the native binary (the
-- driver calls the real `alias_cond` on two cells, or twice on one
-- shared cell when `aliased`, and prints both words, so tampering
-- the C++ under test is caught). Overflow cases assert Lean-Lean
-- agreement only — signed overflow is UB, so native has nothing to
-- compare (the `nsw` error legs, plus the `c = false` masking leg
-- where native never computes the first add). Mismatch = P0.
import Circe.Emit.AliasCond
import Circe.Mem

namespace DiffAliasCond

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed edges: both verdicts under both branches, `q`-irrelevant
    aliased inputs, first-add overflow taken and masked, second-add
    overflow on both legs. -/
def aliasCondEdges : List (BitVec 32 × BitVec 32 × Bool × Bool) :=
  [(10, 20, true, false), (10, 20, false, false),
   (10, 10, true, true), (10, 10, false, true),
   (10, 20, true, true), (0, 0, true, true),
   (0x7FFFFFFF, 0, true, false), (0x7FFFFFFF, 0, false, false),
   (0, 0x7FFFFFFF, true, false),
   (0x7FFFFFFF, 0x7FFFFFFF, true, true)]

/-- `Mem`-level run of the emitted body: pinned entry for disjoint
    trials, shared-cell caller `Mem` for aliased trials. Returns the
    outcome plus the final `Mem` for cell read-back. -/
def runMemBody (p q : BitVec 32) (c aliased : Bool) :
    Except Panic ((Env × Mem × Layout) × Outcome) × Mem :=
  if aliased then
    let (m0, a) := memAllocData emptyMem [p]
    let ρ : Env := [("p", .i32 p), ("q", .i32 q), ("c", .b c)]
    let π : Layout := [("p", a, a), ("q", a, a)]
    match memEvalStmtFuel 20 aliasCondFunc.body ρ m0 π with
    | .error e => (.error e, m0)
    | .ok ((ρ', m', π'), o) => (.ok ((ρ', m', π'), o), m')
  else
    match bindMemArgs aliasCondFunc.args [.i32 p, .i32 q, .b c]
      emptyMem with
    | none => (.error .AssertFail, emptyMem)
    | some (ρ, m, π) =>
      match memEvalStmtFuel 20 aliasCondFunc.body ρ m π with
      | .error e => (.error e, m)
      | .ok ((ρ', m', π'), o) => (.ok ((ρ', m', π'), o), m')

def checkAliasCond (aliasCondBin : String) (p q : BitVec 32)
    (c aliased : Bool) : IO Nat := do
  let spec := aliasCondSpec p q c aliased
  -- `Mem` path agrees with the mirror (cell read-back, verdict-aware).
  let (ev, m') := runMemBody p q c aliased
  match spec, ev with
  | .ok (a, b), .ok ((_, _, π'), .returned (.u32 0)) =>
    if aliased then
      -- Stores shadow-cons (`memFind_cons_hit`); first-wins lookup
      -- reads the newest word. Pins are untouched by evaluation.
      match layoutLookup π' "p" with
      | some (addr, _) =>
        match memFind m' addr with
        | some blk =>
          if blk.data != [b] then
            throw (IO.userError s!"alias_cond mem/spec mismatch: cell={blk.data} spec={b}")
        | none =>
          throw (IO.userError s!"alias_cond mem cell missing under aliasing")
      | none =>
        throw (IO.userError s!"alias_cond pin missing under aliasing")
    else
      match memFind m' 1, memFind m' 0 with
      | some bp, some bq =>
        if bp.data != [a] || bq.data != [b] then
          throw (IO.userError s!"alias_cond mem/spec mismatch: cells={bp.data},{bq.data} spec=({a}, {b})")
      | _, _ =>
        throw (IO.userError s!"alias_cond mem cells missing")
  | .error e1, .error e2 =>
    if (repr e1).pretty != (repr e2).pretty then
      throw (IO.userError s!"alias_cond mem/spec error mismatch: {(repr e1).pretty} vs {(repr e2).pretty}")
  | _, _ =>
    throw (IO.userError s!"alias_cond mem/spec ok-err mismatch")
  -- Native only when the mirror is `.ok`; otherwise Lean-Lean only.
  match spec with
  | .ok (a, b) =>
    let native ← runNative aliasCondBin
      #[toString p.toInt, toString q.toInt, if c then "1" else "0",
        if aliased then "1" else "0"]
    match native.splitOn " " with
    | [sp, sq] =>
      match sp.toInt?, sq.toInt? with
      | some m, some n =>
        if m != a.toInt || n != b.toInt then
          throw (IO.userError s!"alias_cond mismatch: lean=({a.toInt}, {b.toInt}) native=({m}, {n})")
        pure 1
      | _, _ =>
        throw (IO.userError s!"alias_cond native unparsable: {native}")
    | _ =>
      throw (IO.userError s!"alias_cond native unparsable: {native}")
  | _ => pure 1

def main (args : List String) : IO Unit := do
  let aliasCondBin := args.getD 0 "/tmp/opencode/circe_alias_cond_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (p, q, c, aliased) in aliasCondEdges do
    let r ← checkAliasCond aliasCondBin p q c aliased
    passed := passed + r
  let mut s := 0x9E3779B97F4A7C15
  for i in List.range trials do
    s := lcgNext s
    -- Small words stay in range (native agrees); every 8th trial is
    -- full-width (overflows exercise the Lean-Lean path); `c` and
    -- `aliased` alternate (all four modes covered).
    let xi : Int :=
      if i % 8 == 7 then ((s : Int) % 2 ^ 32) - 2 ^ 31
      else (((s % 101 : Nat) : Int) - 50)
    s := lcgNext s
    let yi : Int :=
      if i % 8 == 3 then ((s : Int) % 2 ^ 32) - 2 ^ 31
      else (((s % 101 : Nat) : Int) - 50)
    let c := i % 2 == 0
    let aliased := i % 4 < 2
    let r ← checkAliasCond aliasCondBin (BitVec.ofInt 32 xi)
      (BitVec.ofInt 32 yi) c aliased
    passed := passed + r
  IO.println s!"DIFFALIASCOND-OK passed={passed} (edges + {trials} random trials)"

end DiffAliasCond
