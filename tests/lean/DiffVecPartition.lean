-- Differential test for the in-place Lomuto partition over
-- `std::vector<int>`: verified Lean forward (plus `evalFunc`
-- composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecPartition.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward model
-- (runtime composition check); the native binary must print the
-- partitioned words exactly (total kernel: every access is
-- guard-justified, so there are no miss legs). Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecPartition

namespace DiffVecPartition

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Directed cases: empty, all-below, all-above, mixed, pivot-equal. -/
def vecPartitionEdges :
    List (List (BitVec 32) × BitVec 32) :=
  [([], 5),
   ([3, 1, 2], 5),
   ([7, 8], 5),
   ([3, 7, 1, 8, 2], 5),
   ([5, 1], 5),
   ([5, 5, 5], 5)]

def checkVecPartition (bin : String) (l : List (BitVec 32))
    (pivot : BitVec 32) : IO Nat := do
  -- Entry: call-free evaluation agrees with the forward model
  -- (runtime composition check).
  let fwd := vecPartitionFwd l pivot
  let ev := evalFunc vecPartitionFunc
    [.stdVecVal l, .i32 pivot]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_partition eval/fwd mismatch")
  let args := #[toString l.length]
    ++ (l.toArray.map fun w => toString w.toInt)
    ++ #[toString pivot.toInt]
  match fwd with
  | .ok (.stdVecVal l') =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"vec_partition native failed: {out.stderr}")
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != l'.length || got.length != l'.length ||
            got != l'.map (·.toInt) then
          throw (IO.userError s!"vec_partition mismatch: lean={l'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError s!"vec_partition native unparsable: {out.stdout}")
    | [] =>
      throw (IO.userError s!"vec_partition native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "vec_partition unexpected non-vector forward")
  | .error _ =>
    throw (IO.userError "vec_partition unexpected forward error (total kernel)")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_partition_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (l, pivot) in vecPartitionEdges do
    let q ← checkVecPartition asBin l pivot
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8); words and pivot in -20..20.
    let len := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range len do
      s := lcgNext s
      let xi : Int := ((s % 41 : Nat) : Int) - 20
      l := l ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let pv : Int := ((s % 41 : Nat) : Int) - 20
    let pivot := BitVec.ofInt 32 pv
    let q ← checkVecPartition asBin l pivot
    passed := passed + q
  IO.println s!"DIFFVECPARTITION-OK passed={passed} (edges + {trials} random trials)"

end DiffVecPartition
