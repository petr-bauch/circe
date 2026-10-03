-- Differential test for the S3b 64-bit fragment: verified Lean
-- `add64` / `addu64` (evaluation + forwards) vs the native C binaries.
--
-- Run: `lake env lean --run tests/lean/DiffWidth.lean <add64bin> <addu64bin> [trials]`
-- Every trial asserts evaluated `evalFuncFuel` agrees with the value
-- forward (runtime composition check) and both agree with native
-- (`addu64` always; `add64` on in-range sums — overflow cases only
-- assert Lean-Lean agreement since signed overflow is UB in C).
-- Mismatch = P0.
import Circe.Emit

namespace DiffWidth

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed `add64` cases: ok paths, both overflow directions,
    boundary values (`INT64_MIN`/`MAX`, ±1, mixed extremes). -/
def add64Edges : List (BitVec 64 × BitVec 64) :=
  [(0, 0), (1, 2), (0x7FFFFFFFFFFFFFFF, 0), (0x7FFFFFFFFFFFFFFF, 1),
   (0x7FFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF),
   (0x8000000000000000, 0), (0x8000000000000000, 0xFFFFFFFFFFFFFFFF),
   (0x8000000000000000, 0x8000000000000000),
   (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF),
   (0x8000000000000000, 0x7FFFFFFFFFFFFFFF),
   (0x7FFFFFFFFFFFFFFE, 1), (0x8000000000000001, 0xFFFFFFFFFFFFFFFF),
   (100, 0xFFFFFFFFFFFFFF38), (123456789012345, 987654321098765)]

def checkAdd64 (add64Bin : String) (a b : BitVec 64) : IO Nat := do
  let fwd := add64Fwd a b
  let ev := evalFunc add64Func [.i64 a, .i64 b]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.i64 r) =>
      let native ← runNative add64Bin #[toString a.toInt, toString b.toInt]
      match native.toInt? with
      | none => throw (IO.userError s!"add64 native unparsable: {native}")
      | some m =>
        if m != r.toInt then
          throw (IO.userError s!"add64 mismatch: lean={r.toInt} native={m}")
        pure 1
    | _ => throw (IO.userError s!"add64 eval shape unexpected")
  else
    throw (IO.userError s!"add64 eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `addu64` cases: zero, unit, `UINT64_MAX` wrap edges,
    high-bit folds. Wrapping is defined, so native always agrees. -/
def addu64Edges : List (BitVec 64 × BitVec 64) :=
  [(0, 0), (1, 2), (0xFFFFFFFFFFFFFFFF, 0), (0xFFFFFFFFFFFFFFFF, 1),
   (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF),
   (0x8000000000000000, 0x8000000000000000),
   (0x8000000000000000, 0xFFFFFFFFFFFFFFFF),
   (0xFFFFFFFFFFFFFFFE, 1), (123456789012345, 987654321098765),
   (0xFFFFFFFF00000000, 0xFFFFFFFF)]

def checkAddu64 (addu64Bin : String) (a b : BitVec 64) : IO Nat := do
  let fwd := addu64Fwd a b
  let ev := evalFunc addu64Func [.u64 a, .u64 b]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .ok (.u64 r) =>
      let native ← runNative addu64Bin #[toString a.toNat, toString b.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"addu64 native unparsable: {native}")
      | some m =>
        if m != r.toNat then
          throw (IO.userError s!"addu64 mismatch: lean={r.toNat} native={m}")
        pure 1
    | _ => throw (IO.userError s!"addu64 eval shape unexpected")
  else
    throw (IO.userError s!"addu64 eval/fwd mismatch (emit_correct violated at runtime)")

/-- Boundary pool for 64-bit fuzz: extremes plus near-misses, so random
    trials hit both the ok and overflow paths. -/
def bound64Pool : List Nat :=
  [0, 1, 2, 0x7FFFFFFFFFFFFFFE, 0x7FFFFFFFFFFFFFFF,
   0x8000000000000000, 0x8000000000000001, 0xFFFFFFFFFFFFFFFE,
   0xFFFFFFFFFFFFFFFF, 30, 61]

def main (args : List String) : IO Unit := do
  let add64Bin := args.getD 0 "/tmp/opencode/circe_add64_native"
  let addu64Bin := args.getD 1 "/tmp/opencode/circe_addu64_native"
  let trials := (args.getD 2 "1000").toNat?.getD 1000
  let mut passed := 0
  for (a, b) in add64Edges do
    let c ← checkAdd64 add64Bin a b
    passed := passed + c
  for (a, b) in addu64Edges do
    let c ← checkAddu64 addu64Bin a b
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for i in List.range trials do
    s := lcgNext s
    if i % 2 == 0 then
      -- Small signed values: sums stay in range, native agrees.
      let ai : Int := ((s % 61 : Nat) : Int) - 30
      s := lcgNext s
      let bi : Int := ((s % 61 : Nat) : Int) - 30
      let c ← checkAdd64 add64Bin (BitVec.ofInt 64 ai) (BitVec.ofInt 64 bi)
      passed := passed + c
      s := lcgNext s
      let c ← checkAddu64 addu64Bin (BitVec.ofNat 64 (s % 1000))
        (BitVec.ofNat 64 ((s / 7) % 1000))
      passed := passed + c
    else
      -- Boundary-biased full-range values: overflow paths (Lean-Lean)
      -- and wrap edges (native) both get exercised.
      let a := BitVec.ofNat 64 (bound64Pool.getD (s % bound64Pool.length) 0)
      s := lcgNext s
      let b := BitVec.ofNat 64 s
      let c ← checkAdd64 add64Bin a b
      passed := passed + c
      s := lcgNext s
      let c ← checkAddu64 addu64Bin (BitVec.ofNat 64 s)
        (BitVec.ofNat 64 (bound64Pool.getD (s % bound64Pool.length) 0))
      passed := passed + c
  IO.println s!"DIFFWIDTH-OK passed={passed} (edges + {trials} random trials)"

end DiffWidth
