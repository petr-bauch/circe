-- Differential test for the Phase 3 fragment: verified Lean forward
-- functions (`Circe.Emit.addFwd` / `incrFwd`) vs native C binaries.
--
-- Run: `lake env lean --run tests/lean/DiffPhase3.lean <add_bin> <incr_bin> [trials]`
-- For each random in-range input the native output must equal the Lean
-- result; on out-of-range inputs Lean must report `Overflow` (native is not
-- consulted: signed overflow is UB in C) and the mathematical sum is
-- cross-checked to be genuinely out of range (catches a wrongly-strict
-- Lean side); on ok paths the sum is cross-checked in range (catches a
-- wrongly-lenient Lean side agreeing with wrapping native code).
import Circe.Emit

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Draw an `Int` in `[int32Min, int32Max]` from the stream. -/
def drawI32 (s : Nat) : Int × Nat :=
  let s' := lcgNext s
  (Int.ofNat (s' % 2 ^ 32) + int32Min, s')

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

def checkAdd (addBin : String) (a b : BitVec 32) : IO Nat := do
  let sum := a.toInt + b.toInt
  match addFwd a b with
  | .ok (.i32 r) =>
    if !(decide (int32Min ≤ sum ∧ sum ≤ int32Max)) then
      throw (IO.userError s!"add wrongly lenient: {a.toInt}+{b.toInt}")
    let native ← runNative addBin #[toString a.toInt, toString b.toInt]
    match native.toInt? with
    | none => throw (IO.userError s!"add native unparsable: {native}")
    | some n =>
      if n != r.toInt then
        throw (IO.userError s!"add mismatch: {a.toInt}+{b.toInt} lean={r.toInt} native={n}")
      pure 1
  | .ok v =>
    throw (IO.userError s!"add unexpected value shape: {(repr v).pretty}")
  | .error .Overflow =>
    if decide (int32Min ≤ sum ∧ sum ≤ int32Max) then
      throw (IO.userError s!"add wrongly strict: {a.toInt}+{b.toInt}")
    pure 1
  | .error e =>
    throw (IO.userError s!"add unexpected error: {(repr e).pretty}")

def checkIncr (incrBin : String) (p : BitVec 32) : IO Nat := do
  let sum := p.toInt + 1
  match incrFwd p with
  | .ok (.i32 r) =>
    if !(decide (int32Min ≤ sum ∧ sum ≤ int32Max)) then
      throw (IO.userError s!"incr wrongly lenient: {p.toInt}")
    let native ← runNative incrBin #[toString p.toInt]
    match native.toInt? with
    | none => throw (IO.userError s!"incr native unparsable: {native}")
    | some n =>
      if n != r.toInt then
        throw (IO.userError s!"incr mismatch: {p.toInt} lean={r.toInt} native={n}")
      pure 1
  | .ok v =>
    throw (IO.userError s!"incr unexpected value shape: {(repr v).pretty}")
  | .error .Overflow =>
    if decide (int32Min ≤ sum ∧ sum ≤ int32Max) then
      throw (IO.userError s!"incr wrongly strict: {p.toInt}")
    pure 1
  | .error e =>
    throw (IO.userError s!"incr unexpected error: {(repr e).pretty}")

/-- Fixed edge cases (exercised before random trials). -/
def addEdges : List (Int × Int) :=
  [(0, 0), (1, 2), (-1, 1), (2147483647, 0), (-2147483648, 0),
   (2147483647, 1), (-2147483648, -1), (2147483647, 2147483647),
   (-2147483648, -2147483648), (2147483647, -2147483648), (100, -200)]

def incrEdges : List Int :=
  [0, 1, -1, 42, -1000, 2147483646, 2147483647, -2147483648]

def main (args : List String) : IO Unit := do
  let addBin := args.getD 0 "/tmp/opencode/circe_add_native"
  let incrBin := args.getD 1 "/tmp/opencode/circe_incr_native"
  let trials := (args.getD 2 "1000").toNat?.getD 1000
  let mut passed := 0
  for (x, y) in addEdges do
    let c ← checkAdd addBin (BitVec.ofInt 32 x) (BitVec.ofInt 32 y)
    passed := passed + c
  for x in incrEdges do
    let c ← checkIncr incrBin (BitVec.ofInt 32 x)
    passed := passed + c
  let mut s := 0x243F6A8885A308D3
  for _ in List.range trials do
    let (x, s1) := drawI32 s
    let (y, s2) := drawI32 s1
    s := s2
    let c1 ← checkAdd addBin (BitVec.ofInt 32 x) (BitVec.ofInt 32 y)
    passed := passed + c1
    let c2 ← checkIncr incrBin (BitVec.ofInt 32 x)
    passed := passed + c2
  IO.println s!"DIFF-OK passed={passed} (edges + {trials} random trials × 2)"
