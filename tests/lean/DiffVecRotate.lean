-- Differential test for in-place `std::vector<int>` left rotation:
-- the verified Lean forward (plus `evalProgFunc` composition) vs the
-- native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecRotate.main [bin trials]`).
-- Every trial asserts program evaluation agrees with the forward model
-- (runtime composition check, which also validates fuel sufficiency:
-- `F = 3 * (n + 1) + 8` covers the three countdowns plus the
-- composition step). The native binary must print the rotated words
-- exactly (length preserved). Mismatch = P0.
import Circe.Emit

namespace DiffVecRotate

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def bv (x : Int) : BitVec 32 := BitVec.ofInt 32 x

/-- Directed cases: empty, zero/full rotation, single steps,
    boundaries. -/
def rotEdges : List (List (BitVec 32) × Nat) :=
  [([], 0),
   ([bv 7], 0),
   ([bv 7], 1),
   ([bv 1, bv 2, bv 3], 0),
   ([bv 1, bv 2, bv 3], 1),
   ([bv 1, bv 2, bv 3], 2),
   ([bv 1, bv 2, bv 3], 3),
   ([bv 4, bv 3, bv 2, bv 1], 1),
   ([bv 4, bv 3, bv 2, bv 1], 3),
   ([bv 5, bv 4, bv 3, bv 2, bv 1], 0),
   ([bv 5, bv 4, bv 3, bv 2, bv 1], 5),
   ([bv 0, bv 1, bv 0xFFFFFFFF, bv 0x7FFFFFFF, bv 0x80000000, bv 42],
     4),
   ([bv 0x7FFFFFFF, bv 0x80000000], 1),
   ([bv 1, bv 1, bv 1, bv 1], 2)]

def checkRot (bin : String) (l : List (BitVec 32)) (k : Nat) :
    IO Nat := do
  -- Program evaluation agrees with the forward model (runtime
  -- composition check; generous fuel covers all three countdowns).
  let F := 3 * (l.length + 1) + 8
  let kB := BitVec.ofNat 64 k
  let fwd := vecRotateFwd l kB
  let ev := evalProgFunc vecRotateProg F vecRotateFunc
    [.stdVecVal l, .u64 kB]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_rotate eval/fwd mismatch")
  let args := #[toString l.length]
    ++ (l.toArray.map fun w => toString w.toInt)
    ++ #[toString k]
  let out ← IO.Process.output { cmd := bin, args := args }
  if out.exitCode != 0 then
    throw (IO.userError s!"vec_rotate native failed: {out.stderr}")
  match fwd with
  | .ok (.stdVecVal l') =>
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != l'.length || got.length != l'.length ||
            got != l'.map (·.toInt) then
          throw (IO.userError s!"vec_rotate mismatch: lean={l'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError "vec_rotate native bad length")
    | [] =>
      throw (IO.userError "vec_rotate native empty output")
  | _ =>
    throw (IO.userError "vec_rotate forward unexpected shape")

def main (args : List String) : IO Unit := do
  let bin := args.getD 0 "/tmp/opencode/circe_vec_rotate_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (l, k) in rotEdges do
    let q ← checkRot bin l k
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
    let k := s % (len + 1)
    let q ← checkRot bin l k
    passed := passed + q
  IO.println s!"DIFFVECROTATE-OK passed={passed}"

end DiffVecRotate
