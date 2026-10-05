-- Differential test for the N6a arithmetic fragment: verified Lean
-- `neg` / `sdiv` (evaluation + forwards) vs the native C binaries.
--
-- Run: `lake env lean --run tests/lean/DiffArith.lean <negbin> <sdivbin> [trials]`
-- Every trial asserts evaluated `evalFunc` agrees with the value
-- forward (runtime composition check) and both agree with native
-- (`neg` on `x ≠ INT_MIN`, `sdiv` on defined divisions — UB cases
-- only assert Lean-Lean agreement since negation overflow, division
-- by zero, and `INT_MIN / -1` are UB in C).
-- Mismatch = P0.
import Circe.Emit

namespace DiffArith

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed `neg` cases: zero, unit, `INT32_MAX`, `INT32_MIN`
    (overflow, Lean-Lean), `-1`, near-misses. -/
def negEdges : List (BitVec 32) :=
  [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x80000001, 42]

def checkNeg (negBin : String) (x : BitVec 32) : IO Nat := do
  let fwd := negFwd x
  let ev := evalFunc negFunc [.i32 x]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.i32 r) =>
      let native ← runNative negBin #[toString x.toInt]
      match native.toInt? with
      | none => throw (IO.userError s!"neg native unparsable: {native}")
      | some m =>
        if m != r.toInt then
          throw (IO.userError s!"neg mismatch: lean={r.toInt} native={m}")
        pure 1
    | _ => throw (IO.userError s!"neg eval shape unexpected")
  else
    throw (IO.userError s!"neg eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `sdiv` cases: exact, truncating both signs, zero divisor
    (`DivZero`, Lean-Lean), `INT_MIN / -1` (overflow, Lean-Lean),
    `INT_MIN / 1`, `INT32_MAX / -1`. -/
def sdivEdges : List (BitVec 32 × BitVec 32) :=
  [(6, 3), (7, 3), (7, 0xFFFFFFFD), (0xFFFFFFF9, 3), (0, 5), (5, 0),
   (0x80000000, 0xFFFFFFFF), (0x80000000, 1), (0x7FFFFFFF, 0xFFFFFFFF),
   (1, 1), (0xFFFFFFFF, 0xFFFFFFFF)]

def checkSdiv (sdivBin : String) (a b : BitVec 32) : IO Nat := do
  let fwd := sdivFwd a b
  let ev := evalFunc sdivFunc [.i32 a, .i32 b]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.i32 r) =>
      let native ← runNative sdivBin #[toString a.toInt, toString b.toInt]
      match native.toInt? with
      | none => throw (IO.userError s!"sdiv native unparsable: {native}")
      | some m =>
        if m != r.toInt then
          throw (IO.userError s!"sdiv mismatch: lean={r.toInt} native={m}")
        pure 1
    | _ => throw (IO.userError s!"sdiv eval shape unexpected")
  else
    throw (IO.userError s!"sdiv eval/fwd mismatch (emit_correct violated at runtime)")

/-- Boundary pool for 32-bit fuzz: extremes plus near-misses, so random
    trials hit ok, `DivZero`, and overflow paths. -/
def bound32Pool : List Nat :=
  [0, 1, 2, 0x7FFFFFFE, 0x7FFFFFFF, 0x80000000, 0x80000001,
   0xFFFFFFFE, 0xFFFFFFFF, 30, 61]

def main (args : List String) : IO Unit := do
  let negBin := args.getD 0 "/tmp/opencode/circe_neg_native"
  let sdivBin := args.getD 1 "/tmp/opencode/circe_sdiv_native"
  let trials := (args.getD 2 "1000").toNat?.getD 1000
  let mut passed := 0
  for x in negEdges do
    let c ← checkNeg negBin x
    passed := passed + c
  for (a, b) in sdivEdges do
    let c ← checkSdiv sdivBin a b
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values: neg stays in range except INT_MIN hits.
    let x := BitVec.ofInt 32 (((s % 61 : Nat) : Int) - 30)
    let c ← checkNeg negBin x
    passed := passed + c
    s := lcgNext s
    -- Boundary-biased pairs: zero divisors and INT_MIN / -1 exercise
    -- the Lean-Lean paths; the rest compare against native.
    let a := BitVec.ofNat 32 (bound32Pool.getD (s % bound32Pool.length) 0)
    s := lcgNext s
    let b := BitVec.ofNat 32 (bound32Pool.getD (s % bound32Pool.length) 0)
    let c ← checkSdiv sdivBin a b
    passed := passed + c
    s := lcgNext s
  IO.println s!"DIFFARITH-OK passed={passed} (edges + {trials} random trials)"

end DiffArith
