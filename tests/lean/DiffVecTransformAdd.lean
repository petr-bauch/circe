-- Differential test for the out-of-place checked transform over
-- `std::vector<int>`: verified Lean forward (plus `evalFunc`
-- composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecTransformAdd.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward model
-- (runtime composition check). On hit the native binary must print
-- the transformed `out` words exactly; on short-`out` miss the native
-- must exit 4 (caught `std::out_of_range`) while Lean reports
-- `.error .AssertFail`. Overflow is Lean-only (native `nsw` add is
-- UB, never compared). Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecTransformAdd

namespace DiffVecTransformAdd

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Directed cases: hit, empty, short-`out` miss, negatives hit,
    overflow (Lean-only). -/
def vecTransformAddEdges :
    List (List (BitVec 32) × List (BitVec 32) × BitVec 32) :=
  [([1, 2, 3], [0, 0, 0], 10),
   ([], [], 5),
   ([1], [], 5),
   ([-3, 1], [0, 0], -7),
   ([2147483647], [0], 1)]

def checkVecTransformAdd (bin : String) (li lo : List (BitVec 32))
    (c : BitVec 32) : IO Nat := do
  -- Entry: call-free evaluation agrees with the forward model
  -- (runtime composition check).
  let fwd := vecTransformAddFwd li lo c
  let ev := evalFunc vecTransformAddFunc
    [.stdVecVal li, .stdVecVal lo, .i32 c]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_transform_add eval/fwd mismatch")
  let args := #[toString li.length]
    ++ (li.toArray.map fun w => toString w.toInt)
    ++ #[toString lo.length, toString c.toInt]
  match fwd with
  | .ok (.stdVecVal lo') =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"vec_transform_add native failed on hit: {out.stderr}")
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != lo'.length || got.length != lo'.length ||
            got != lo'.map (·.toInt) then
          throw (IO.userError s!"vec_transform_add mismatch: lean={lo'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError s!"vec_transform_add native unparsable: {out.stdout}")
    | [] =>
      throw (IO.userError s!"vec_transform_add native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "vec_transform_add unexpected non-vector forward")
  | .error .Overflow =>
    -- Overflow leg: Lean-only (native `nsw` add is UB, never compared).
    pure 1
  | .error _ =>
    -- Miss leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"vec_transform_add native exit={out.exitCode}, expected 4 on miss")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_transform_add_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (li, lo, c) in vecTransformAddEdges do
    let q ← checkVecTransformAdd asBin li lo c
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..5); words in -20..20, constant in
    -- -5..5 (no overflow in fuzz — the overflow edge is directed).
    let leni := s % 6
    let mut li : List (BitVec 32) := []
    for _ in List.range leni do
      s := lcgNext s
      let xi : Int := ((s % 41 : Nat) : Int) - 20
      li := li ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let cv : Int := ((s % 11 : Nat) : Int) - 5
    let c := BitVec.ofInt 32 cv
    s := lcgNext s
    -- `out` is exact-size one trial in two, short otherwise.
    let nout := if s % 2 == 1 then leni else leni - (s % 2) - 1
    let lo : List (BitVec 32) := List.replicate nout (BitVec.ofNat 32 0)
    let q ← checkVecTransformAdd asBin li lo c
    passed := passed + q
  IO.println s!"DIFFVECTRANSFORMADD-OK passed={passed} (edges + {trials} random trials)"

end DiffVecTransformAdd
