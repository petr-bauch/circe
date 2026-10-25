-- Differential test for Kadane maximum subarray:
-- verified Lean forward (plus `evalFunc` composition) vs the native
-- C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecKadane.main [bin trials]`).
-- Every trial asserts evaluation agrees with the Kadane fold
-- (runtime composition check) and, when the fold is `.ok` (all adds
-- in range), the entry agrees with native (exact words: the driver
-- requires `argc == 2 + n`, the N2d window-shift lesson). Overflow
-- cases assert Lean-Lean agreement only — signed overflow is UB, so
-- native has nothing to compare. The empty-seed leg (`AssertFail`,
-- the `at()`-throw precedent) is Lean-only: native would throw.
-- Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecKadane

namespace DiffVecKadane

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed vectors: empty seed, singletons, short sums, all-negative,
    per-site overflow, double-min, mixed signs, the canonical mix. -/
def vecKadaneEdges : List (List (BitVec 32)) :=
  [[], [0], [5], [0xFFFFFFFF], [1, 2, 3], [0xFFFFFFFF, 0xFFFFFFFF],
   [0x7FFFFFFF, 1], [0x80000000, 0x80000000], [2, 0xFFFFFFFF, 3],
   [0xFFFFFFFE, 1, 0xFFFFFFFD, 4, 0xFFFFFFFF, 2, 1, 0xFFFFFFFB, 4]]

def checkVecKadane (kadaneBin : String) (l : List (BitVec 32)) : IO Nat := do
  -- Entry: call-free evaluation agrees with the Kadane fold
  -- (runtime composition check).
  let fwdKad := kadaneFwd l
  let evKad := evalFunc vecKadaneFunc [.stdVecVal l]
  if (repr fwdKad).pretty != (repr evKad).pretty then
    throw (IO.userError "vec_kadane eval/fwd mismatch")
  -- Native only when the driver accepts the inputs (the Kadane fold
  -- is `.ok`); otherwise Lean-Lean agreement only.
  match fwdKad with
  | .ok (.i32 s) =>
    let native ← runNative kadaneBin
      (#[toString l.length] ++ (l.toArray.map fun x => toString x.toInt))
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"vec_kadane mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"vec_kadane native unparsable: {native}")
  | _ => pure 1

def main (args : List String) : IO Unit := do
  let kadaneBin := args.getD 0 "/tmp/opencode/circe_vec_kadane_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for l in vecKadaneEdges do
    let q ← checkVecKadane kadaneBin l
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8): small sums stay in range (native
    -- agrees); large magnitudes overflow into the Lean-Lean path.
    let n := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range n do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      l := l ++ [BitVec.ofInt 32 xi]
    let q ← checkVecKadane kadaneBin l
    passed := passed + q
  IO.println s!"DIFFVECKADANE-OK passed={passed} (edges + {trials} random trials)"

end DiffVecKadane
