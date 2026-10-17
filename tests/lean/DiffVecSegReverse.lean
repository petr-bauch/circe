-- Differential test for in-place `std::vector<int>` segment reverse:
-- the verified Lean forward (plus `evalProgFunc` composition) vs the
-- native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecSegReverse.main [bin trials]`).
-- Every trial asserts program evaluation agrees with the forward model
-- (runtime composition check, which also validates fuel sufficiency:
-- `F = n + 1` covers `revIters lo hi + 1`). The native binary must
-- print the window-reversed words exactly (length preserved).
-- Mismatch = P0.
import Circe.Emit

namespace DiffVecSegReverse

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def bv (x : Int) : BitVec 32 := BitVec.ofInt 32 x

/-- Directed cases: empty/full windows, prefix, suffix, interior,
    singleton, empty window at the end, boundaries. -/
def segEdges : List (List (BitVec 32) × Nat × Nat) :=
  [([], 0, 0),
   ([bv 7], 0, 1),
   ([bv 1, bv 2, bv 3], 0, 3),
   ([bv 1, bv 2, bv 3], 0, 2),
   ([bv 1, bv 2, bv 3], 1, 3),
   ([bv 1, bv 2, bv 3], 1, 2),
   ([bv 4, bv 3, bv 2, bv 1], 1, 3),
   ([bv 5, bv 4, bv 3, bv 2, bv 1], 0, 0),
   ([bv 5, bv 4, bv 3, bv 2, bv 1], 5, 5),
   ([bv 0, bv 1, bv 0xFFFFFFFF, bv 0x7FFFFFFF, bv 0x80000000, bv 42],
     1, 5),
   ([bv 0x7FFFFFFF, bv 0x80000000], 0, 1),
   ([bv 1, bv 1, bv 1, bv 1], 0, 4)]

def checkSeg (bin : String) (l : List (BitVec 32)) (lo hi : Nat) :
    IO Nat := do
  -- Program evaluation agrees with the forward model (runtime
  -- composition check; `F = n + 1` covers the countdown fuel).
  let F := l.length + 1
  let loB := BitVec.ofNat 64 lo
  let hiB := BitVec.ofNat 64 hi
  let fwd := vecSegReverseFwd l loB hiB
  let ev := evalProgFunc vecSegReverseProg F vecSegReverseFunc
    [.stdVecVal l, .u64 loB, .u64 hiB]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_seg_reverse eval/fwd mismatch")
  let args := #[toString l.length]
    ++ (l.toArray.map fun w => toString w.toInt)
    ++ #[toString lo, toString hi]
  let out ← IO.Process.output { cmd := bin, args := args }
  if out.exitCode != 0 then
    throw (IO.userError s!"vec_seg_reverse native failed: {out.stderr}")
  match fwd with
  | .ok (.stdVecVal l') =>
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != l'.length || got.length != l'.length ||
            got != l'.map (·.toInt) then
          throw (IO.userError s!"vec_seg_reverse mismatch: lean={l'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError "vec_seg_reverse native bad length")
    | [] =>
      throw (IO.userError "vec_seg_reverse native empty output")
  | _ =>
    throw (IO.userError "vec_seg_reverse forward unexpected shape")

def main (args : List String) : IO Unit := do
  let bin := args.getD 0 "/tmp/opencode/circe_vec_seg_reverse_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (l, lo, hi) in segEdges do
    let q ← checkSeg bin l lo hi
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    let len := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range len do
      s := lcgNext s
      -- Words in -30..30, every sixteenth a boundary word.
      let xi : Int := if s % 16 == 0 then
        match s % 4 with
        | 0 => 0x7FFFFFFF
        | 1 => -0x80000000
        | 2 => -1
        | _ => 0
      else ((s % 61 : Nat) : Int) - 30
      l := l ++ [bv xi]
    s := lcgNext s
    let lo := s % (len + 1)
    s := lcgNext s
    let hi := lo + s % (len + 1 - lo)
    let q ← checkSeg bin l lo hi
    passed := passed + q
  IO.println s!"DIFFVECSEGREVERSE-OK passed={passed}"

end DiffVecSegReverse
