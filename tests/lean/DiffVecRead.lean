-- Differential test for the N4d-iv-a `std::vector<int32_t>`
-- reads fragment: verified Lean forwards (plus `evalFunc`
-- composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecRead.main [bin trials]`).
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check) and, when the checked-add fold is
-- `.ok` (all adds in range), the entry agrees with native (overflow
-- cases assert Lean-Lean agreement only — signed overflow is UB, so
-- native has nothing to compare; OOB indices likewise never reach
-- native).
-- Mismatch = P0.
import Circe.Emit

namespace DiffVecRead

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed vectors: empty, singletons, short sums, per-site
    overflow, double-min. -/
def vecReadEdges : List (List (BitVec 32)) :=
  [[], [0], [1, 2, 3], [0x7FFFFFFF], [0x7FFFFFFF, 1],
   [1, 0x7FFFFFFF], [0x80000000, 0x80000000], [42, 0xFFFFFFFF, 7]]

def checkVecRead (vecBin : String) (l : List (BitVec 32)) : IO Nat := do
  -- Leaves: program-free evaluation agrees with the forwards
  -- (runtime composition check on the fused edges).
  let fwdSize := stdVecSizeFwd l
  let evSize := evalFunc stdVecSizeFunc [.stdVecVal l]
  if (repr fwdSize).pretty != (repr evSize).pretty then
    throw (IO.userError "vec_size eval/fwd mismatch")
  for k in List.range l.length do
    let n : BitVec 64 := BitVec.ofNat 64 k
    let fwdAt := stdVecIndexFwd l n
    let evAt := evalFunc stdVecIndexFunc [.stdVecVal l, .u64 n]
    if (repr fwdAt).pretty != (repr evAt).pretty then
      throw (IO.userError s!"vec_index eval/fwd mismatch at {k}")
  -- OOB index: Lean-Lean agreement only (unchecked indexing is UB,
  -- so the model reports it and native has nothing to compare).
  let nOob : BitVec 64 := BitVec.ofNat 64 l.length
  let fwdOob := stdVecIndexFwd l nOob
  let evOob := evalFunc stdVecIndexFunc [.stdVecVal l, .u64 nOob]
  if (repr fwdOob).pretty != (repr evOob).pretty then
    throw (IO.userError "vec_index OOB eval/fwd mismatch")
  -- Entry: call-free evaluation agrees with the checked-add fold
  -- (runtime composition check).
  let fwdSum := stdVecReadSumFwd l
  let evSum := evalFunc stdVecReadSumFunc [.stdVecVal l]
  if (repr fwdSum).pretty != (repr evSum).pretty then
    throw (IO.userError "vec_read_sum eval/fwd mismatch")
  -- Native only when the driver accepts the inputs (the checked-add
  -- fold is `.ok`); otherwise Lean-Lean agreement only.
  match fwdSum with
  | .ok (.i32 s) =>
    let native ← runNative vecBin
      (#[toString l.length] ++ (l.toArray.map fun x => toString x.toInt))
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"vec_read_sum mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"vec_read_sum native unparsable: {native}")
  | _ => pure 1

def main (args : List String) : IO Unit := do
  let vecBin := args.getD 0 "/tmp/opencode/circe_vec_read_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for l in vecReadEdges do
    let q ← checkVecRead vecBin l
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
    let q ← checkVecRead vecBin l
    passed := passed + q
  IO.println s!"DIFFVECREAD-OK passed={passed} (edges + {trials} random trials)"

end DiffVecRead
