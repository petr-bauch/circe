-- Differential test for the N7a `std::string_view` range-for
-- fragment: verified Lean forwards (plus `evalFunc` composition) vs
-- the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffView.main [bin trials]`).
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check) and the entry agrees with native
-- (with `n ≤ 8` every checked-add fold is `.ok`, so native always
-- has something to compare — the overflow path is proof-covered
-- only; OOB reads never reach native).
-- Mismatch = P0.
import Circe.Emit

namespace DiffView

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed views: empty, singletons, short sums, high-bit bytes
    (the `sext8` pin: `0xFF` sums as `-1`, `0x80` as `-128`),
    embedded NUL. -/
def viewEdges : List (List (BitVec 8)) :=
  [[], [0], [1, 2, 3], [0xFF], [0x80], [0x7F, 0x7F],
   [0x00, 65, 0x00], [42, 0xFF, 7]]

def checkView (viewBin : String) (l : List (BitVec 8)) : IO Nat := do
  -- Leaves: program-free evaluation agrees with the forwards
  -- (runtime composition check on the fused edges).
  let fwdBegin := viewBeginFwd
  let evBegin := evalFunc viewBeginFunc [.viewVal l]
  if (repr fwdBegin).pretty != (repr evBegin).pretty then
    throw (IO.userError "view_begin eval/fwd mismatch")
  let fwdEnd := viewEndFwd l
  let evEnd := evalFunc viewEndFunc [.viewVal l]
  if (repr fwdEnd).pretty != (repr evEnd).pretty then
    throw (IO.userError "view_end eval/fwd mismatch")
  -- Entry: call-free evaluation agrees with the checked-add fold
  -- (runtime composition check).
  let fwdSum := viewSumFwd l
  let evSum := evalFunc viewSumFunc [.viewVal l]
  if (repr fwdSum).pretty != (repr evSum).pretty then
    throw (IO.userError "view_sum eval/fwd mismatch")
  -- Native agrees whenever the fold is `.ok` (always, for `n ≤ 8`;
  -- otherwise Lean-Lean agreement only).
  match fwdSum with
  | .ok (.i32 s) =>
    let native ← runNative viewBin
      (#[toString l.length] ++ (l.toArray.map fun x => toString x.toInt))
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"view_sum mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"view_sum native unparsable: {native}")
  | _ => pure 1

def main (args : List String) : IO Unit := do
  let viewBin := args.getD 0 "/tmp/opencode/circe_view_sum_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for l in viewEdges do
    let q ← checkView viewBin l
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8): full signed-byte range, so the
    -- high-bit sext path is covered against native every trial.
    let n := s % 9
    let mut l : List (BitVec 8) := []
    for _ in List.range n do
      s := lcgNext s
      let xi : Int := ((s % 256 : Nat) : Int) - 128
      l := l ++ [BitVec.ofInt 8 xi]
    let q ← checkView viewBin l
    passed := passed + q
  IO.println s!"DIFFVIEW-OK passed={passed} (edges + {trials} random trials)"

end DiffView
