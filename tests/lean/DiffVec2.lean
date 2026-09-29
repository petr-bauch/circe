-- Differential test for the M1a two-block heap fragment: verified Lean
-- `vec_copy_sum` (forward) vs the native C binary.
--
-- Run: `lake env lean --run tests/lean/DiffVec2.lean <vec2_bin> [trials]`
-- Every trial asserts evaluated `evalFunc` agrees with `vec2Fwd`
-- (runtime loop check) and both agree with native. Indices are small
-- (`n ≤ 64 ≪ EVAL_FUEL`), so fuel hypotheses always hold; mismatch = P0.
-- The copy is value-invisible, so native must agree with the same
-- index-sum as `vec_alloc`.
import Circe.Emit

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Fixed edge cases for `vec_copy_sum` (lengths). -/
def vec2Edges : List Nat :=
  [0, 1, 2, 3, 7, 8, 16, 31, 32, 63, 64]

def checkVec2 (vecBin : String) (k : Nat) : IO Nat := do
  let n := BitVec.ofNat 32 k
  match vec2Fwd n, evalFunc vec2Func [.u32 n] with
  | .ok (.u32 r), .ok (.u32 r2) =>
    if r != r2 then
      throw (IO.userError s!"vec2 eval/fwd mismatch (emit_correct violated at runtime)")
    let native ← runNative vecBin #[toString k]
    match native.toNat? with
    | none => throw (IO.userError s!"vec2 native unparsable: {native}")
    | some m =>
      if m != r.toNat then
        throw (IO.userError s!"vec2 mismatch: n={k} lean={r.toNat} native={m}")
      pure 1
  | .ok _, _ =>
    throw (IO.userError s!"vec2 eval shape unexpected")
  | .error e, _ =>
    throw (IO.userError s!"vec2 wrongly strict on small input: {(repr e).pretty}")

def main (args : List String) : IO Unit := do
  let vecBin := args.getD 0 "/tmp/opencode/circe_vec2_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for k in vec2Edges do
    let c ← checkVec2 vecBin k
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    let k := s % 65
    let c ← checkVec2 vecBin k
    passed := passed + c
  IO.println s!"DIFFVEC2-OK passed={passed} (edges + {trials} random trials)"
