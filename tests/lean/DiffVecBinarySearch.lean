-- Differential test for binary search over `const std::vector<int>&`:
-- verified Lean forward (plus `evalFunc` composition) vs the native
-- C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecBinarySearch.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward model
-- (runtime composition check) and the forward agrees with native
-- (exact words: the driver requires `argc == 3 + n`, the N2d
-- window-shift lesson). There is no overflow/UBB leg: the midpoint
-- `lo + (hi - lo) / 2` cannot overflow and every element goes through
-- the checked `at()`; sortedness is caller debt for the functional
-- spec, not for entry/native agreement, so unsorted vectors fuzz
-- agreement too. Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecBinarySearch

namespace DiffVecBinarySearch

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed cases: empty, singleton hit/miss, first/middle/last hit,
    below/above miss, `int32` boundary values, all-equal, descending
    (unsorted: agreement only). -/
def vecBinSearchEdges : List (List (BitVec 32) × BitVec 32) :=
  [([], 0), ([7], 7), ([7], 3),
   ([1, 2, 3], 1), ([1, 2, 3], 2), ([1, 2, 3], 3),
   ([1, 2, 3], 0), ([1, 2, 3], 5),
   ([0x80000000], 0x80000000), ([0x7FFFFFFF], 0x7FFFFFFF),
   ([0x80000000, 0x7FFFFFFF], 0x7FFFFFFF),
   ([0x80000000, 0x7FFFFFFF], 0),
   ([5, 5, 5, 5], 5), ([5, 5, 5, 5], 4),
   ([3, 2, 1], 2), ([3, 2, 1], 9)]

def checkVecBinarySearch (bin : String) (l : List (BitVec 32))
    (t : BitVec 32) : IO Nat := do
  -- Entry: call-free evaluation agrees with the forward model
  -- (runtime composition check).
  let fwd := vecBinarySearchFwd l t
  let ev := evalFunc vecBinSearchFunc [.stdVecVal l, .i32 t]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_binary_search eval/fwd mismatch")
  -- Native agrees on every input (no UB leg).
  match fwd with
  | .ok (.u64 w) =>
    let native ← runNative bin
      (#[toString l.length] ++ (l.toArray.map fun x => toString x.toInt)
        ++ #[toString t.toInt])
    match native.toNat? with
    | some m =>
      if m != w.toNat then
        throw (IO.userError s!"vec_binary_search mismatch: lean={w.toNat} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"vec_binary_search native unparsable: {native}")
  | _ =>
    throw (IO.userError "vec_binary_search unexpected non-u64 forward")

def main (args : List String) : IO Unit := do
  let bsBin := args.getD 0 "/tmp/opencode/circe_vec_binary_search_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (l, t) in vecBinSearchEdges do
    let q ← checkVecBinarySearch bsBin l t
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8); even trials ascending (cumulative
    -- steps, hit-rich), odd trials arbitrary (agreement everywhere).
    let n := s % 9
    let mut l : List (BitVec 32) := []
    if s % 2 == 0 then
      let mut acc : Int := ((s % 21 : Nat) : Int) - 10
      for _ in List.range n do
        s := lcgNext s
        acc := acc + ((s % 5 : Nat) : Int)
        l := l ++ [BitVec.ofInt 32 acc]
    else
      for _ in List.range n do
        s := lcgNext s
        let xi : Int := ((s % 61 : Nat) : Int) - 30
        l := l ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let t : BitVec 32 :=
      match l[s % 9]? with
      | some x => if s % 3 == 0 then x else BitVec.ofInt 32 (((s % 61 : Nat) : Int) - 30)
      | none => BitVec.ofInt 32 (((s % 61 : Nat) : Int) - 30)
    let q ← checkVecBinarySearch bsBin l t
    passed := passed + q
  IO.println s!"DIFFVECBINARYSEARCH-OK passed={passed} (edges + {trials} random trials)"

end DiffVecBinarySearch
