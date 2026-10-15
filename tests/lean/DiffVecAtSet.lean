-- Differential test for the checked `at()` store over
-- `std::vector<int>&`: verified Lean forward (plus `evalFunc`
-- composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecAtSet.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward model
-- (runtime composition check). On hit the native binary must print
-- the updated vector words exactly (the driver requires
-- `argc == 4 + n`); on miss the native must exit 4 (caught
-- `std::out_of_range`) while Lean reports `.error .AssertFail`
-- (the `vec_at_one` empty-read precedent). Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecAtSet

namespace DiffVecAtSet

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Directed cases: empty miss, first/last hit, past-the-end miss,
    singleton hit, negatives, `int32` boundary words. -/
def vecAtSetEdges : List (List (BitVec 32) × BitVec 64 × BitVec 32) :=
  [([], 0, 9), ([1, 2, 3], 0, 9), ([1, 2, 3], 2, 9),
   ([1, 2, 3], 3, 9), ([7], 0, -5), ([-3, 1, 2], 1, -7),
   ([0x7FFFFFFF, 0x80000000], 0, 0), ([0x7FFFFFFF, 0x80000000], 1, 0)]

def checkVecAtSet (bin : String) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32) : IO Nat := do
  -- Entry: call-free evaluation agrees with the forward model
  -- (runtime composition check).
  let fwd := vecAtSetFwd l n x
  let ev := evalFunc vecAtSetFunc [.stdVecVal l, .u64 n, .i32 x]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_at_set eval/fwd mismatch")
  let args := #[toString l.length]
    ++ (l.toArray.map fun w => toString w.toInt)
    ++ #[toString n.toNat, toString x.toInt]
  match fwd with
  | .ok (.stdVecVal l') =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"vec_at_set native failed on hit: {out.stderr}")
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != l'.length || got.length != l'.length ||
            got != l'.map (·.toInt) then
          throw (IO.userError s!"vec_at_set mismatch: lean={l'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError s!"vec_at_set native unparsable: {out.stdout}")
    | [] =>
      throw (IO.userError s!"vec_at_set native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "vec_at_set unexpected non-vector forward")
  | .error _ =>
    -- Miss leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"vec_at_set native exit={out.exitCode}, expected 4 on miss")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_at_set_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (l, n, x) in vecAtSetEdges do
    let q ← checkVecAtSet asBin l n x
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8, driver cap); the index is
    -- in-bounds two trials in three, past-the-end otherwise (miss
    -- leg exercises the native exit-4 path).
    let len := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range len do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      l := l ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let n : BitVec 64 :=
      if s % 3 == 2 then BitVec.ofNat 64 (len + (s % 3))
      else BitVec.ofNat 64 (s % 9)
    s := lcgNext s
    let x : BitVec 32 :=
      BitVec.ofInt 32 (((s % 61 : Nat) : Int) - 30)
    let q ← checkVecAtSet asBin l n x
    passed := passed + q
  IO.println s!"DIFFVECATSET-OK passed={passed} (edges + {trials} random trials)"

end DiffVecAtSet
