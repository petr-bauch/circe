-- Differential test for the S2 struct-by-value fragment: verified Lean
-- `translate` (evaluation + forward) vs the native C binary.
--
-- Run: `lake env lean --run tests/lean/DiffStruct.lean <struct_bin> [trials]`
-- Every trial asserts evaluated `evalFuncFuel` agrees with the value
-- forward (runtime composition check) and both agree with native
-- (in-range cases; overflow cases only assert Lean-Lean agreement —
-- signed overflow is UB, so native has nothing to compare).
-- Mismatch = P0.
import Circe.Emit

namespace DiffStruct

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed `translate` cases: ok paths, x-only overflow, y-only
    overflow, both-overflow, boundary values. -/
def translateEdges : List (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) :=
  [(0, 0, 0, 0), (1, 2, 3, 4), (0x7FFFFFFF, 0, 0, 0),
   (0x7FFFFFFF, 5, 1, 0), (5, 0x7FFFFFFF, 0, 1),
   (0x7FFFFFFF, 0x7FFFFFFF, 1, 1), (0x80000000, 0, 0, 0),
   (0x80000000, 7, 0xFFFFFFFF, 0), (7, 0x80000000, 0, 0xFFFFFFFF),
   (0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF),
   (0, 0, 1, 1), (100, 200, 300, 400)]

def checkTranslate (structBin : String)
    (px py dx dy : BitVec 32) : IO Nat := do
  let fwd := translateFwd px py dx dy
  let ev := evalFuncFuel EVAL_FUEL translateFunc
    [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.structVal _ [("x", qx), ("y", qy)]) =>
      let native ← runNative structBin
        #[toString px.toInt, toString py.toInt,
          toString dx.toInt, toString dy.toInt]
      match native.splitOn " " with
      | [sx, sy] =>
        match sx.toInt?, sy.trimAscii.toString.toInt? with
        | some mx, some my =>
          if mx != qx.toInt || my != qy.toInt then
            throw (IO.userError s!"translate mismatch: lean=({qx.toInt},{qy.toInt}) native=({mx},{my})")
          pure 1
        | _, _ => throw (IO.userError s!"translate native unparsable: {native}")
      | _ => throw (IO.userError s!"translate native unparsable: {native}")
    | .ok _ => throw (IO.userError s!"translate eval shape unexpected")
  else
    throw (IO.userError s!"translate eval/fwd mismatch (emit_correct violated at runtime)")

def main (args : List String) : IO Unit := do
  let structBin := args.getD 0 "/tmp/opencode/circe_struct_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (px, py, dx, dy) in translateEdges do
    let c ← checkTranslate structBin px py dx dy
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values: the field adds stay in range, so native agrees.
    let pxi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let pyi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let dxi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let dyi : Int := ((s % 61 : Nat) : Int) - 30
    let c ← checkTranslate structBin (BitVec.ofInt 32 pxi)
      (BitVec.ofInt 32 pyi) (BitVec.ofInt 32 dxi) (BitVec.ofInt 32 dyi)
    passed := passed + c
  IO.println s!"DIFFSTRUCT-OK passed={passed} (edges + {trials} random trials)"

end DiffStruct
