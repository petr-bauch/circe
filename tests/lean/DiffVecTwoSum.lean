-- Differential test for brute-force two-sum over `const std::vector<int>&`:
-- verified Lean forward (plus `evalFunc` composition) vs the native
-- C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecTwoSum.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward model
-- (runtime composition check) and the forward agrees with native on
-- non-overflowing inputs (exact words: the driver requires
-- `argc == 3 + n`). The `i32` element add is loud: on overflow the
-- forward is `.error .Overflow` and native is skipped (Lean-Lean
-- agreement only — the `vec_at_sum` `nsw` precedent). Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecTwoSum

namespace DiffVecTwoSum

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed cases: empty miss, singleton miss (`j` loop never runs),
    early/late hits, miss, duplicates, negatives, `int32` boundary
    values, the overflow leg (Lean-Lean only). -/
def vecTwoSumEdges : List (List (BitVec 32) × BitVec 32) :=
  [([], 0), ([7], 7), ([7], 3),
   ([1, 2, 3], 3), ([1, 2, 3], 5), ([1, 2, 3], 4),
   ([1, 2, 3], 9), ([5, 5, 5], 10), ([5, 5, 5], 3),
   ([-3, 1, 2], -1), ([3, 2, 1], 5),
   ([0x7FFFFFFF], 0), ([0x7FFFFFFF, 0x7FFFFFFF], 0),
   ([0x7FFFFFFF, 1], 0), ([0x80000000, 0x80000000], 0)]

def checkVecTwoSum (bin : String) (l : List (BitVec 32))
    (t : BitVec 32) : IO Nat := do
  -- Entry: call-free evaluation agrees with the forward model
  -- (runtime composition check).
  let fwd := vecTwoSumFwd l t
  let ev := evalFunc vecTwoSumFunc [.stdVecVal l, .i32 t]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_two_sum eval/fwd mismatch")
  -- Native agrees on every non-overflowing input.
  match fwd with
  | .ok (.structVal "IPair" [(("a", a)), (("b", b))]) =>
    let native ← runNative bin
      (#[toString l.length] ++ (l.toArray.map fun x => toString x.toInt)
        ++ #[toString t.toInt])
    match native.splitOn " " with
    | [sa, sb] =>
      match sa.toInt?, sb.toInt? with
      | some ma, some mb =>
        if ma != a.toInt || mb != b.toInt then
          throw (IO.userError s!"vec_two_sum mismatch: lean=({a.toInt},{b.toInt}) native=({ma},{mb})")
        pure 1
      | _, _ =>
        throw (IO.userError s!"vec_two_sum native unparsable: {native}")
    | _ =>
      throw (IO.userError s!"vec_two_sum native unparsable: {native}")
  | .ok _ =>
    throw (IO.userError "vec_two_sum unexpected non-pair forward")
  | .error _ =>
    -- Loud overflow leg: Lean-Lean agreement only, native skipped.
    pure 1

def main (args : List String) : IO Unit := do
  let tsBin := args.getD 0 "/tmp/opencode/circe_vec_two_sum_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (l, t) in vecTwoSumEdges do
    let q ← checkVecTwoSum tsBin l t
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..6, pairs are quadratic); values are
    -- small ints most trials, `int32` boundary words every 8th trial
    -- (exercises the loud overflow leg); targets are pair sums
    -- half the time (hit-rich), arbitrary otherwise.
    let n := s % 7
    let mut l : List (BitVec 32) := []
    for _ in List.range n do
      s := lcgNext s
      if s % 8 == 0 then
        l := l ++ [if s % 2 == 0 then 0x7FFFFFFF else 0x80000000]
      else
        let xi : Int := ((s % 61 : Nat) : Int) - 30
        l := l ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let t : BitVec 32 :=
      match l[s % 7]?, l[(s + 1) % 7]? with
      | some x, some y =>
        if s % 2 == 0 then
          match checkedAddI32 x y with
          | .ok sum => sum
          | .error _ => BitVec.ofInt 32 (((s % 61 : Nat) : Int) - 30)
        else BitVec.ofInt 32 (((s % 61 : Nat) : Int) - 30)
      | _, _ => BitVec.ofInt 32 (((s % 61 : Nat) : Int) - 30)
    let q ← checkVecTwoSum tsBin l t
    passed := passed + q
  IO.println s!"DIFFVECTWOSUM-OK passed={passed} (edges + {trials} random trials)"

end DiffVecTwoSum
