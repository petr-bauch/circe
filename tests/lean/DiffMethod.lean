-- Differential test for the M2a const-method fragment: verified Lean
-- `point_sum_ref` (program evaluation + forward) vs the native C++ binary.
--
-- Run: `lake env lean --run tests/lean/DiffMethod.lean <method_bin> [trials]`
-- Every trial asserts evaluated `evalProgFunc` agrees with the value
-- forward (runtime composition check) and both agree with native
-- (in-range cases; overflow cases only assert Lean-Lean agreement —
-- signed overflow is UB, so native has nothing to compare).
-- Mismatch = P0.
import Circe.Emit

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed `point_sum_ref` cases: ok paths, x-overflow, y-overflow,
    both-overflow, boundary values. -/
def methodEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (1, 2), (0x7FFFFFFF, 0), (0, 0x7FFFFFFF),
   (0x7FFFFFFF, 1), (1, 0x7FFFFFFF), (0x7FFFFFFF, 0x7FFFFFFF),
   (0x80000000, 0), (0, 0x80000000), (0x80000000, 0x80000000),
   (0xFFFFFFFF, 0xFFFFFFFF), (0x80000000, 0x7FFFFFFF)]

def checkMethod (methodBin : String)
    (px py : BitVec 32) : IO Nat := do
  let fwd := pointSumRefFwd px py
  let ev := evalProgFunc [methodSumFunc] EVAL_FUEL pointSumRefFunc
    [.structVal "Point" [("x", px), ("y", py)]]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.i32 s) =>
      let native ← runNative methodBin
        #[toString px.toInt, toString py.toInt]
      match native.toInt? with
      | some m =>
        if m != s.toInt then
          throw (IO.userError s!"method mismatch: lean={s.toInt} native={m}")
        pure 1
      | none => throw (IO.userError s!"method native unparsable: {native}")
    | .ok _ => throw (IO.userError s!"method eval shape unexpected")
  else
    throw (IO.userError s!"method eval/fwd mismatch (emit_correct violated at runtime)")

def main (args : List String) : IO Unit := do
  let methodBin := args.getD 0 "/tmp/opencode/circe_method_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (px, py) in methodEdges do
    let c ← checkMethod methodBin px py
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values: the field add stays in range, so native agrees.
    let pxi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let pyi : Int := ((s % 61 : Nat) : Int) - 30
    let c ← checkMethod methodBin (BitVec.ofInt 32 pxi)
      (BitVec.ofInt 32 pyi)
    passed := passed + c
  IO.println s!"DIFFMETHOD-OK passed={passed} (edges + {trials} random trials)"
