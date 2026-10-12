-- Differential test for the `std::vector::at` checked sum:
-- verified Lean forward (plus `evalFunc` composition) vs the native
-- C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecAtSum.main [bin trials]`).
-- Every trial asserts evaluation agrees with the inherited
-- checked-add fold (runtime composition check) and, when the fold
-- is `.ok` (all adds in range), the entry agrees with native (exact
-- words: the driver requires `argc == 2 + n`, the N2d window-shift
-- lesson). Overflow cases assert Lean-Lean agreement only — signed
-- overflow is UB, so native has nothing to compare. There is no OOB
-- leg: the loop bound `i < size` subsumes the guard, so `AssertFail`
-- is unreachable here (pinned by `vecAtSumBody_guard_false`); the
-- OOB behavior of the underlying read is covered by `DiffVecAt`.
-- Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecAtSum

namespace DiffVecAtSum

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed vectors: empty sum, singletons, short sums, per-site
    overflow, double-min. -/
def vecAtSumEdges : List (List (BitVec 32)) :=
  [[], [0], [1, 2, 3], [0x7FFFFFFF], [0x7FFFFFFF, 1],
   [1, 0x7FFFFFFF], [0x80000000, 0x80000000], [42, 0xFFFFFFFF, 7]]

def checkVecAtSum (sumBin : String) (l : List (BitVec 32)) : IO Nat := do
  -- Entry: call-free evaluation agrees with the checked-add fold
  -- (runtime composition check).
  let fwdSum := vecAtSumFwd l
  let evSum := evalFunc vecAtSumFunc [.stdVecVal l]
  if (repr fwdSum).pretty != (repr evSum).pretty then
    throw (IO.userError "vec_at_sum eval/fwd mismatch")
  -- Native only when the driver accepts the inputs (the checked-add
  -- fold is `.ok`); otherwise Lean-Lean agreement only.
  match fwdSum with
  | .ok (.i32 s) =>
    let native ← runNative sumBin
      (#[toString l.length] ++ (l.toArray.map fun x => toString x.toInt))
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"vec_at_sum mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"vec_at_sum native unparsable: {native}")
  | _ => pure 1

def main (args : List String) : IO Unit := do
  let sumBin := args.getD 0 "/tmp/opencode/circe_vec_at_sum_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for l in vecAtSumEdges do
    let q ← checkVecAtSum sumBin l
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8): sums usually stay in range (native
    -- agrees); overflows exercise the Lean-Lean path.
    let n := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range n do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      l := l ++ [BitVec.ofInt 32 xi]
    let q ← checkVecAtSum sumBin l
    passed := passed + q
  IO.println s!"DIFFVECATSUM-OK passed={passed} (edges + {trials} random trials)"

end DiffVecAtSum
