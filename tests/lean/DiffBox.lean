-- Differential test for the M2c `new` / `delete` fragment: verified
-- Lean `box_through` (evaluated `evalFuncFuel` + forward) vs the native
-- C++ binary.
--
-- Run: `lake env lean --run tests/lean/DiffBox.lean <box_bin> [trials]`
-- Every trial asserts evaluated `evalFuncFuel` agrees with the value
-- forward (runtime composition check) and both agree with native (the
-- passthrough is total, so every input compares — no UB carve-out).
-- Mismatch = P0.
import Circe.Emit

namespace DiffBox

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed `box_through` cases: zero, unit, extrema, wraparound. -/
def boxEdges : List (BitVec 32) :=
  [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 42]

def checkBox (boxBin : String)
    (x : BitVec 32) : IO Nat := do
  let fwd := boxThroughFwd x
  let ev := evalFuncFuel EVAL_FUEL boxThroughFunc [.i32 x]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => throw (IO.userError s!"box eval unexpected error")
    | .ok (.i32 r) =>
      let native ← runNative boxBin
        #[toString x.toInt]
      match native.toInt? with
      | some m =>
        if m != r.toInt then
          throw (IO.userError s!"box mismatch: lean={r.toInt} native={m}")
        pure 1
      | none => throw (IO.userError s!"box native unparsable: {native}")
    | .ok _ => throw (IO.userError s!"box eval shape unexpected")
  else
    throw (IO.userError s!"box eval/fwd mismatch (emit_correct violated at runtime)")

def main (args : List String) : IO Unit := do
  let boxBin := args.getD 0 "/tmp/opencode/circe_box_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for x in boxEdges do
    let c ← checkBox boxBin x
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    let xi : Int := ((s % 61 : Nat) : Int) - 30
    let c ← checkBox boxBin (BitVec.ofInt 32 xi)
    passed := passed + c
  IO.println s!"DIFFBOX-OK passed={passed} (edges + {trials} random trials)"

end DiffBox
