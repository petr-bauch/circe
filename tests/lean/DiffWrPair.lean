-- Differential test for the writer-pair admission (G2): verified
-- Lean forward (plus `evalFunc` composition) vs the native C binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffWrPair.main [bin trials]`).
-- Every trial asserts evaluation agrees with the independent
-- checked-add pair (runtime composition check) and, when both adds
-- are in range, the entry agrees with native (the driver calls the
-- real `wr_pair` on two disjoint cells and prints the updated pair,
-- so tampering the C under test is caught). Overflow cases assert
-- Lean-Lean agreement only — signed overflow is UB, so native has
-- nothing to compare (the `nsw` error legs). Aliased callers are
-- caller-UB under the `noalias` verdict: documented, never fuzzed.
-- Mismatch = P0.
import Circe.Emit
import Circe.Emit.WrPair

namespace DiffWrPair

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed pairs: zero, small increments, `-1` on either side,
    `INT32_MIN`, first-add overflow, second-add overflow. -/
def wrPairEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (10, 20), (0xFFFFFFFF, 0), (0, 0xFFFFFFFF),
   (0x80000000, 0x80000000), (0x7FFFFFFF, 0), (0, 0x7FFFFFFF)]

def checkWrPair (wrPairBin : String) (p q : BitVec 32) : IO Nat := do
  -- Entry: call-free evaluation agrees with the checked-add pair
  -- (runtime composition check).
  let fwd := wrPairFwd p q
  let ev := evalFunc wrPairFunc [.i32 p, .i32 q]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "wr_pair eval/fwd mismatch")
  -- Native only when both checked adds are `.ok`; otherwise
  -- Lean-Lean agreement only.
  match fwd with
  | .ok (.structVal "IPair" [("a", a), ("b", b)]) =>
    let native ← runNative wrPairBin #[toString p.toInt, toString q.toInt]
    match native.splitOn " " with
    | [sp, sq] =>
      match sp.toInt?, sq.toInt? with
      | some m, some n =>
        if m != a.toInt || n != b.toInt then
          throw (IO.userError s!"wr_pair mismatch: lean=({a.toInt}, {b.toInt}) native=({m}, {n})")
        pure 1
      | _, _ =>
        throw (IO.userError s!"wr_pair native unparsable: {native}")
    | _ =>
      throw (IO.userError s!"wr_pair native unparsable: {native}")
  | _ => pure 1

def main (args : List String) : IO Unit := do
  let wrPairBin := args.getD 0 "/tmp/opencode/circe_wr_pair_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (p, q) in wrPairEdges do
    let r ← checkWrPair wrPairBin p q
    passed := passed + r
  let mut s := 0x9E3779B97F4A7C15
  for i in List.range trials do
    s := lcgNext s
    -- Small words stay in range (native agrees); every 8th trial is
    -- full-width (overflows exercise the Lean-Lean path).
    let xi : Int :=
      if i % 8 == 7 then ((s : Int) % 2 ^ 32) - 2 ^ 31
      else (((s % 101 : Nat) : Int) - 50)
    s := lcgNext s
    let yi : Int :=
      if i % 8 == 3 then ((s : Int) % 2 ^ 32) - 2 ^ 31
      else (((s % 101 : Nat) : Int) - 50)
    let r ← checkWrPair wrPairBin (BitVec.ofInt 32 xi) (BitVec.ofInt 32 yi)
    passed := passed + r
  IO.println s!"DIFFWRPAIR-OK passed={passed} (edges + {trials} random trials)"

end DiffWrPair
