-- Differential test for the N4b-i `move_int` leaf: the verified Lean
-- forward (plus `evalFunc` composition) vs the native C++ binary.
--
-- Run: `lake env lean --run tests/lean/DiffMove.lean <move_int_bin> <move_acc_bin> <scope_early_bin> [trials]`
-- `std::move` on `int` erases to a copy, so the check is `addFwd` /
-- renamed-`addFunc` evaluation vs native on all-ok pairs (overflow
-- cases assert Lean-Lean agreement only — signed overflow is UB, so
-- native has nothing to compare). Mismatch = P0.
import Circe.Emit

namespace DiffMove

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed move pairs: ok paths, overflow, negatives, boundaries. -/
def moveEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (1, 2), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF),
   (0x7FFFFFFF, 0x7FFFFFFF), (0x80000000, 0x80000000),
   (0x80000000, 0xFFFFFFFF)]

def checkMoveInt (moveBin : String) (x y : BitVec 32) : IO Nat := do
  let fwd := addFwd x y
  let ev := evalFunc { addFunc with name := "_Z8move_intii" } [.i32 x, .i32 y]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "move_int eval/fwd mismatch")
  match fwd with
  | .error _ => pure 1
  | .ok (.i32 s) =>
    let native ← runNative moveBin #[toString x.toInt, toString y.toInt]
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"move_int mismatch: lean={s.toInt} native={m}")
      pure 1
    | none => throw (IO.userError s!"move_int native unparsable: {native}")
  | .ok _ => throw (IO.userError "move_int eval shape unexpected")

/-- Directed `move_acc` pairs: ok paths, first-add overflow,
    second-add overflow, negatives, boundaries. -/
def moveAccEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (1, 2), (0x7FFFFFFF, 0), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF),
   (0x7FFFFFFF, 0x7FFFFFFF), (0x80000000, 0x80000000)]

def checkMoveAcc (moveAccBin : String) (x y : BitVec 32) : IO Nat := do
  let fwd := moveAccFwd x y
  let ev := evalProgFunc moveProg EVAL_FUEL moveAccFunc [.i32 x, .i32 y]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "move_acc eval/fwd mismatch")
  match fwd with
  | .error _ => pure 1
  | .ok (.i32 s) =>
    let native ← runNative moveAccBin #[toString x.toInt, toString y.toInt]
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"move_acc mismatch: lean={s.toInt} native={m}")
      pure 1
    | none => throw (IO.userError s!"move_acc native unparsable: {native}")
  | .ok _ => throw (IO.userError "move_acc eval shape unexpected")

/-- Directed `scope_early` pairs: the early path (`x = y`), the
    fallthrough, first-add overflow, second-add overflow, boundaries. -/
def scopeEarlyEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (1, 1), (5, 5), (1, 2), (0x7FFFFFFF, 0), (0x7FFFFFFF, 1),
   (1, 0x7FFFFFFF), (0x7FFFFFFF, 0x7FFFFFFF), (0x80000000, 0x80000000)]

def checkScopeEarly (earlyBin : String) (x y : BitVec 32) : IO Nat := do
  let fwd := scopeEarlyFwd x y
  let ev := evalProgFunc earlyProg EVAL_FUEL scopeEarlyFunc [.i32 x, .i32 y]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "scope_early eval/fwd mismatch")
  match fwd with
  | .error _ => pure 1
  | .ok (.i32 s) =>
    let native ← runNative earlyBin #[toString x.toInt, toString y.toInt]
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"scope_early mismatch: lean={s.toInt} native={m}")
      pure 1
    | none => throw (IO.userError s!"scope_early native unparsable: {native}")
  | .ok _ => throw (IO.userError "scope_early eval shape unexpected")

def main (args : List String) : IO Unit := do
  let moveBin := args.getD 0 "/tmp/opencode/circe_move_int_native"
  let moveAccBin := args.getD 1 "/tmp/opencode/circe_move_acc_native"
  let earlyBin := args.getD 2 "/tmp/opencode/circe_scope_early_native"
  let trials := (args.getD 3 "1000").toNat?.getD 1000
  let mut passed := 0
  for (x, y) in moveEdges do
    let c ← checkMoveInt moveBin x y
    passed := passed + c
  for (x, y) in moveAccEdges do
    let c ← checkMoveAcc moveAccBin x y
    passed := passed + c
  for (x, y) in scopeEarlyEdges do
    let c ← checkScopeEarly earlyBin x y
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values: sums usually stay in range (native agrees);
    -- overflows exercise the Lean-Lean path. Every 7th trial repeats
    -- the same value twice to hit the early path natively.
    let xi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let yi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let zi : Int := ((s % 7 : Nat) : Int)
    let yi' := if zi == 0 then xi else yi
    let c ← checkMoveInt moveBin (BitVec.ofInt 32 xi) (BitVec.ofInt 32 yi)
    passed := passed + c
    let c2 ← checkMoveAcc moveAccBin (BitVec.ofInt 32 xi) (BitVec.ofInt 32 yi)
    passed := passed + c2
    let c3 ← checkScopeEarly earlyBin (BitVec.ofInt 32 xi) (BitVec.ofInt 32 yi')
    passed := passed + c3
  IO.println s!"DIFFMOVE-OK passed={passed} (edges + {trials} random trials)"

end DiffMove
