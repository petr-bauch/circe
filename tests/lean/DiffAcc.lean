-- Differential test for the M2b ctor/dtor fragment: verified Lean
-- `acc_two` (program evaluation + forward) vs the native C++ binary.
--
-- Run: `lake env lean --run tests/lean/DiffAcc.lean <acc_bin> [trials]`
-- Every trial asserts evaluated `evalProgFunc` agrees with the value
-- forward (runtime composition check) and both agree with native
-- (in-range cases; overflow cases only assert Lean-Lean agreement —
-- signed overflow is UB, so native has nothing to compare).
-- Mismatch = P0.
import Circe.Emit

namespace DiffAcc

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed `acc_two` cases: ok paths, first-add overflow,
    second-add overflow, boundary values. -/
def accEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (1, 2), (0x7FFFFFFF, 0), (0, 0x7FFFFFFF),
   (0x7FFFFFFF, 1), (1, 0x7FFFFFFF), (0x7FFFFFFF, 0x7FFFFFFF),
   (0x80000000, 0), (0, 0x80000000), (0x80000000, 0x80000000),
   (0xFFFFFFFF, 0xFFFFFFFF), (0x80000000, 0x7FFFFFFF)]

def checkAcc (accBin : String)
    (a b : BitVec 32) : IO Nat := do
  let fwd := accTwoFwd a b
  let ev := evalProgFunc accProg EVAL_FUEL accTwoFunc [.i32 a, .i32 b]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.i32 s) =>
      let native ← runNative accBin
        #[toString a.toInt, toString b.toInt]
      match native.toInt? with
      | some m =>
        if m != s.toInt then
          throw (IO.userError s!"acc mismatch: lean={s.toInt} native={m}")
        pure 1
      | none => throw (IO.userError s!"acc native unparsable: {native}")
    | .ok _ => throw (IO.userError s!"acc eval shape unexpected")
  else
    throw (IO.userError s!"acc eval/fwd mismatch (emit_correct violated at runtime)")

def main (args : List String) : IO Unit := do
  let accBin := args.getD 0 "/tmp/opencode/circe_acc_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (a, b) in accEdges do
    let c ← checkAcc accBin a b
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values: both adds stay in range, so native agrees.
    let ai : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let bi : Int := ((s % 61 : Nat) : Int) - 30
    let c ← checkAcc accBin (BitVec.ofInt 32 ai)
      (BitVec.ofInt 32 bi)
    passed := passed + c
  IO.println s!"DIFFACC-OK passed={passed} (edges + {trials} random trials)"

end DiffAcc
