-- Differential test for the N4c template-instantiation fragment:
-- verified Lean forwards (plus `evalFunc` composition) vs the native
-- C++ binary.
--
-- Run: `lake env lean --run tests/lean/DiffTadd.lean <tadd_bin> [trials]`
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check) and, on all-ok (in-range) pairs, all
-- agree with native (overflow cases assert Lean-Lean agreement only —
-- signed overflow is UB, so native has nothing to compare).
-- Mismatch = P0.
import Circe.Emit

namespace DiffTadd

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed pairs: ok paths, 32-bit overflow, 64-bit range, boundaries. -/
def taddEdges : List (BitVec 64 × BitVec 64) :=
  [(0, 0), (1, 2), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF),
   (0x7FFFFFFF, 0x7FFFFFFF), (0x80000000, 0x80000000),
   (0x7FFFFFFFFFFFFFFF, 1), (1, 0x7FFFFFFFFFFFFFFF)]

def checkTadd (taddBin : String) (x y : BitVec 64) : IO Nat := do
  let x32 := x.truncate 32
  let y32 := y.truncate 32
  let fwd32 := addFwd x32 y32
  let ev32 := evalFunc { addFunc with name := "_Z4taddIiET_S0_S0_" }
    [.i32 x32, .i32 y32]
  let fwd64 := add64Fwd x y
  let ev64 := evalFunc { add64Func with name := "_Z4taddIlET_S0_S0_" }
    [.i64 x, .i64 y]
  if (repr fwd32).pretty != (repr ev32).pretty then
    throw (IO.userError "tadd32 leaf eval/fwd mismatch")
  if (repr fwd64).pretty != (repr ev64).pretty then
    throw (IO.userError "tadd64 leaf eval/fwd mismatch")
  -- Entries: program evaluation over the renamed leaves agrees with
  -- the delegating forwards (runtime composition check).
  let fwdU32 := useTadd32Fwd x32 y32
  let evU32 := evalProgFunc [{ addFunc with name := "_Z4taddIiET_S0_S0_" }]
    EVAL_FUEL useTadd32Func [.i32 x32, .i32 y32]
  let fwdU64 := useTadd64Fwd x y
  let evU64 := evalProgFunc [{ add64Func with name := "_Z4taddIlET_S0_S0_" }]
    EVAL_FUEL useTadd64Func [.i64 x, .i64 y]
  if (repr fwdU32).pretty != (repr evU32).pretty then
    throw (IO.userError "use_tadd32 eval/fwd mismatch")
  if (repr fwdU64).pretty != (repr evU64).pretty then
    throw (IO.userError "use_tadd64 eval/fwd mismatch")
  -- Native only when the driver accepts the inputs (both fit `int32`
  -- and both sums are in range); otherwise Lean-Lean agreement only.
  let in32 : Bool :=
    -2147483648 ≤ x.toInt && x.toInt ≤ 2147483647 &&
    -2147483648 ≤ y.toInt && y.toInt ≤ 2147483647
  match fwd32, fwd64, fwdU32, fwdU64, in32 with
  | .ok (.i32 s32), .ok (.i64 s64), .ok (.i32 u32), .ok (.i64 u64), true =>
    let native ← runNative taddBin #[toString x.toInt, toString y.toInt]
    match native.splitOn " " with
    | [t32s, t64s, u32s, u64s] =>
      match t32s.toInt?, t64s.toInt?, u32s.toInt?, u64s.toInt? with
      | some m32, some m64, some mu32, some mu64 =>
        if m32 != s32.toInt || m64 != s64.toInt ||
            mu32 != u32.toInt || mu64 != u64.toInt then
          throw (IO.userError s!"tadd mismatch: lean={(s32.toInt, s64.toInt, u32.toInt, u64.toInt)} native={(m32, m64, mu32, mu64)}")
        pure 1
      | _, _, _, _ => throw (IO.userError s!"tadd native unparsable: {native}")
    | _ => throw (IO.userError s!"tadd native shape unexpected: {native}")
  | _, _, _, _, _ => pure 1

def main (args : List String) : IO Unit := do
  let taddBin := args.getD 0 "/tmp/opencode/circe_tadd_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (x, y) in taddEdges do
    let c ← checkTadd taddBin x y
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values: sums usually stay in range (native agrees);
    -- overflows exercise the Lean-Lean path.
    let xi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let yi : Int := ((s % 61 : Nat) : Int) - 30
    let c ← checkTadd taddBin (BitVec.ofInt 64 xi) (BitVec.ofInt 64 yi)
    passed := passed + c
  IO.println s!"DIFFTADD-OK passed={passed} (edges + {trials} random trials)"

end DiffTadd
