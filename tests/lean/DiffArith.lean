-- Differential test for the N6a arithmetic fragment: verified Lean
-- `neg` / `sdiv` (evaluation + forwards) vs the native C binaries,
-- plus the K1 `u32` bitwise leaves (`xor` / `and` / `or` total;
-- `shl` / `shr` with `OOB` on amounts ≥ 32).
--
-- Run: `lake env lean --run tests/lean/DiffArith.lean <negbin> <sdivbin> <xorbin> <andbin> <orbin> <shlbin> <shrbin> [trials]`
-- Every trial asserts evaluated `evalFunc` agrees with the value
-- forward (runtime composition check) and both agree with native
-- (`neg` on `x ≠ INT_MIN`, `sdiv` on defined divisions, shifts on
-- amounts < 32 — UB cases only assert Lean-Lean agreement since
-- negation overflow, division by zero, `INT_MIN / -1`, and shift
-- amounts ≥ 32 are UB in C).
-- Mismatch = P0.
import Circe.Emit
import Circe.Validator

namespace DiffArith

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Leaf pipeline acceptance: real `.cir` validates under `unknown`
    and emits byte-identical text to the golden (gate VERIFY-OK). -/
def checkLeafPipeline (name cir golden : String) : IO Nat := do
  let text ← IO.FS.readFile cir
  let want ← IO.FS.readFile golden
  match runPipeline text ⟨name, .unknown⟩ with
  | .error msg =>
    throw (IO.userError s!"leaf pipeline unexpectedly rejected {name}: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for {name}")
    IO.println s!"PASS pipeline {name}"
    pure 1

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

/-- Directed `xor_u32` cases: zeros, all-ones, nibble-split, unit,
    high-bit, mixed. -/
def xorEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (0xFFFFFFFF, 0xFFFFFFFF), (0xF0F0F0F0, 0x0F0F0F0F),
   (1, 0), (0x80000000, 0xFFFFFFFF), (0x12345678, 0x9ABCDEF0), (42, 17)]

def checkXorU32 (xorBin : String) (a b : BitVec 32) : IO Nat := do
  let fwd := xorU32Fwd a b
  let ev := evalFunc xorU32Func [.u32 a, .u32 b]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error e => throw (IO.userError s!"xor total op errored: {repr e}")
    | .ok (.u32 r) =>
      let native ← runNative xorBin #[toString a.toNat, toString b.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"xor native unparsable: {native}")
      | some m =>
        if m != r.toNat then
          throw (IO.userError s!"xor mismatch: lean={r.toNat} native={m}")
        pure 1
    | _ => throw (IO.userError s!"xor eval shape unexpected")
  else
    throw (IO.userError s!"xor eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `and_u32` cases: zeros, all-ones, nibble-split, masks. -/
def andEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (0xFFFFFFFF, 0xFFFFFFFF), (0xF0F0F0F0, 0x0F0F0F0F),
   (0, 1), (0x80000000, 0x80000000), (0x12345678, 0x9ABCDEF0)]

def checkAndU32 (andBin : String) (a b : BitVec 32) : IO Nat := do
  let fwd := andU32Fwd a b
  let ev := evalFunc andU32Func [.u32 a, .u32 b]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error e => throw (IO.userError s!"and total op errored: {repr e}")
    | .ok (.u32 r) =>
      let native ← runNative andBin #[toString a.toNat, toString b.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"and native unparsable: {native}")
      | some m =>
        if m != r.toNat then
          throw (IO.userError s!"and mismatch: lean={r.toNat} native={m}")
        pure 1
    | _ => throw (IO.userError s!"and eval shape unexpected")
  else
    throw (IO.userError s!"and eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `or_u32` cases: zeros, all-ones, nibble-split, masks. -/
def orEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (0xFFFFFFFF, 0), (0xF0F0F0F0, 0x0F0F0F0F),
   (0, 1), (0x80000000, 0x7FFFFFFF), (0x12345678, 0x9ABCDEF0)]

def checkOrU32 (orBin : String) (a b : BitVec 32) : IO Nat := do
  let fwd := orU32Fwd a b
  let ev := evalFunc orU32Func [.u32 a, .u32 b]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error e => throw (IO.userError s!"or total op errored: {repr e}")
    | .ok (.u32 r) =>
      let native ← runNative orBin #[toString a.toNat, toString b.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"or native unparsable: {native}")
      | some m =>
        if m != r.toNat then
          throw (IO.userError s!"or mismatch: lean={r.toNat} native={m}")
        pure 1
    | _ => throw (IO.userError s!"or eval shape unexpected")
  else
    throw (IO.userError s!"or eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `shl_u32` cases: zero/unit amounts, bit 31, `OOB`
    amounts (Lean-Lean), all-ones. -/
def shlEdges : List (BitVec 32 × BitVec 32) :=
  [(1, 0), (1, 1), (1, 31), (1, 32), (0xFFFFFFFF, 4),
   (0x80000000, 31), (0, 0), (5, 33)]

def checkShlU32 (shlBin : String) (a b : BitVec 32) : IO Nat := do
  let fwd := shlU32Fwd a b
  let ev := evalFunc shlU32Func [.u32 a, .u32 b]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.u32 r) =>
      let native ← runNative shlBin #[toString a.toNat, toString b.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"shl native unparsable: {native}")
      | some m =>
        if m != r.toNat then
          throw (IO.userError s!"shl mismatch: lean={r.toNat} native={m}")
        pure 1
    | _ => throw (IO.userError s!"shl eval shape unexpected")
  else
    throw (IO.userError s!"shl eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `shr_u32` cases: high bit walks, `OOB` amounts
    (Lean-Lean), all-ones. -/
def shrEdges : List (BitVec 32 × BitVec 32) :=
  [(0x80000000, 0), (0x80000000, 1), (0x80000000, 31), (1, 32),
   (0xFFFFFFFF, 4), (0xFFFFFFFF, 0), (7, 35), (0x12345678, 16)]

def checkShrU32 (shrBin : String) (a b : BitVec 32) : IO Nat := do
  let fwd := shrU32Fwd a b
  let ev := evalFunc shrU32Func [.u32 a, .u32 b]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.u32 r) =>
      let native ← runNative shrBin #[toString a.toNat, toString b.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"shr native unparsable: {native}")
      | some m =>
        if m != r.toNat then
          throw (IO.userError s!"shr mismatch: lean={r.toNat} native={m}")
        pure 1
    | _ => throw (IO.userError s!"shr eval shape unexpected")
  else
    throw (IO.userError s!"shr eval/fwd mismatch (emit_correct violated at runtime)")

/-- Boundary pool for 32-bit fuzz: extremes plus near-misses, so random
    trials hit ok, `DivZero`, and overflow paths. -/
def bound32Pool : List Nat :=
  [0, 1, 2, 0x7FFFFFFE, 0x7FFFFFFF, 0x80000000, 0x80000001,
   0xFFFFFFFE, 0xFFFFFFFF, 30, 61]

def main (args : List String) : IO Unit := do
  let negBin := args.getD 0 "/tmp/opencode/circe_neg_native"
  let sdivBin := args.getD 1 "/tmp/opencode/circe_sdiv_native"
  let xorBin := args.getD 2 "/tmp/opencode/circe_xor_u32_native"
  let andBin := args.getD 3 "/tmp/opencode/circe_and_u32_native"
  let orBin := args.getD 4 "/tmp/opencode/circe_or_u32_native"
  let shlBin := args.getD 5 "/tmp/opencode/circe_shl_u32_native"
  let shrBin := args.getD 6 "/tmp/opencode/circe_shr_u32_native"
  let trials := (args.getD 7 "1000").toNat?.getD 1000
  let mut passed := 0
  let p1 ← checkLeafPipeline "xor_u32" "tests/cir/xor_u32.cir"
    "tests/golden/XorU32.lean"
  passed := passed + p1
  let p2 ← checkLeafPipeline "and_u32" "tests/cir/and_u32.cir"
    "tests/golden/AndU32.lean"
  passed := passed + p2
  let p3 ← checkLeafPipeline "or_u32" "tests/cir/or_u32.cir"
    "tests/golden/OrU32.lean"
  passed := passed + p3
  let p4 ← checkLeafPipeline "shl_u32" "tests/cir/shl_u32.cir"
    "tests/golden/ShlU32.lean"
  passed := passed + p4
  let p5 ← checkLeafPipeline "shr_u32" "tests/cir/shr_u32.cir"
    "tests/golden/ShrU32.lean"
  passed := passed + p5
  for x in negEdges do
    let c ← checkNeg negBin x
    passed := passed + c
  for (a, b) in sdivEdges do
    let c ← checkSdiv sdivBin a b
    passed := passed + c
  for (a, b) in xorEdges do
    let c ← checkXorU32 xorBin a b
    passed := passed + c
  for (a, b) in andEdges do
    let c ← checkAndU32 andBin a b
    passed := passed + c
  for (a, b) in orEdges do
    let c ← checkOrU32 orBin a b
    passed := passed + c
  for (a, b) in shlEdges do
    let c ← checkShlU32 shlBin a b
    passed := passed + c
  for (a, b) in shrEdges do
    let c ← checkShrU32 shrBin a b
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
    -- Full-range bitwise pairs: every trial compares against native.
    let u := BitVec.ofNat 32 (bound32Pool.getD (s % bound32Pool.length) 0)
    s := lcgNext s
    let v := BitVec.ofNat 32 (bound32Pool.getD (s % bound32Pool.length) 0)
    let c1 ← checkXorU32 xorBin u v
    passed := passed + c1
    let c2 ← checkAndU32 andBin u v
    passed := passed + c2
    let c3 ← checkOrU32 orBin u v
    passed := passed + c3
    s := lcgNext s
    -- Shift amounts from the pool: in-range amounts compare against
    -- native, `OOB` amounts assert Lean-Lean agreement.
    let w := BitVec.ofNat 32 ((bound32Pool.getD (s % bound32Pool.length) 0) % 40)
    let c4 ← checkShlU32 shlBin u w
    passed := passed + c4
    let c5 ← checkShrU32 shrBin u w
    passed := passed + c5
    s := lcgNext s
  IO.println s!"DIFFARITH-OK passed={passed} (edges + {trials} random trials, incl. u32 bitwise)"

end DiffArith
