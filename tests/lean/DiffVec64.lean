-- Differential test for the M1b `u64` heap fragment: verified Lean
-- `vec_alloc_u64` (forward) vs the native C binary.
--
-- Run: `lake env lean --run tests/lean/DiffVec64.lean <vec64_bin> [trials]`
-- Every trial asserts evaluated `evalFunc` agrees with `vec64Fwd`
-- (runtime loop check) and both agree with native. Indices are small
-- (`n ≤ 64 ≪ EVAL_FUEL`), so fuel hypotheses always hold; mismatch = P0.
import Circe.Emit

namespace DiffVec64

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Fixed edge cases for `vec_alloc_u64` (lengths). -/
def vec64Edges : List Nat :=
  [0, 1, 2, 3, 7, 8, 16, 31, 32, 63, 64]

def checkVec64 (vecBin : String) (k : Nat) : IO Nat := do
  let n := BitVec.ofNat 64 k
  match vec64Fwd n, evalFunc vec64Func [.u64 n] with
  | .ok (.u64 r), .ok (.u64 r2) =>
    if r != r2 then
      throw (IO.userError s!"vec64 eval/fwd mismatch (emit_correct violated at runtime)")
    let native ← runNative vecBin #[toString k]
    match native.toNat? with
    | none => throw (IO.userError s!"vec64 native unparsable: {native}")
    | some m =>
      if m != r.toNat then
        throw (IO.userError s!"vec64 mismatch: n={k} lean={r.toNat} native={m}")
      pure 1
  | .ok _, _ =>
    throw (IO.userError s!"vec64 eval shape unexpected")
  | .error e, _ =>
    throw (IO.userError s!"vec64 wrongly strict on small input: {(repr e).pretty}")

def main (args : List String) : IO Unit := do
  let vecBin := args.getD 0 "/tmp/opencode/circe_vec64_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for k in vec64Edges do
    let c ← checkVec64 vecBin k
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    let k := s % 65
    let c ← checkVec64 vecBin k
    passed := passed + c
  IO.println s!"DIFFVEC64-OK passed={passed} (edges + {trials} random trials)"

end DiffVec64
