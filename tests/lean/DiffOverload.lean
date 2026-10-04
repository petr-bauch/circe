-- Differential test for the N4a overload/namespace fragment: verified
-- Lean forwards (plus `evalFunc`/`evalProgFunc` composition) vs the
-- native C++ binaries.
--
-- Run: `lake env lean --run tests/lean/DiffOverload.lean <overload_bin> <ns_bin> [trials]`
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check) and, on all-ok (in-range) triples, all
-- three agree with native (overflow cases assert Lean-Lean agreement
-- only — signed overflow is UB, so native has nothing to compare).
-- Mismatch = P0.
import Circe.Emit

namespace DiffOverload

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed overload triples: ok paths, first-add overflow,
    second-add overflow, negatives, boundaries. -/
def overloadEdges : List (BitVec 32 × BitVec 32 × BitVec 32) :=
  [(0, 0, 0), (1, 2, 3), (0x7FFFFFFF, 1, 0), (0x7FFFFFFF, 0, 1),
   (1, 0x7FFFFFFF, 1), (0x80000000, 0xFFFFFFFF, 1),
   (0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF), (0x80000000, 0x80000000, 0)]

def checkOverload (overloadBin : String)
    (x y z : BitVec 32) : IO Nat := do
  let fwd2 := addFwd x y
  let ev2 := evalFunc { addFunc with name := "_Z3addii" } [.i32 x, .i32 y]
  let fwd3 := add3Fwd x y z
  let ev3 := evalFunc add3Func [.i32 x, .i32 y, .i32 z]
  let fwdU := useAddFwd x y
  let evU := evalProgFunc [{ addFunc with name := "_Z3addii" }] EVAL_FUEL
    useAddFunc [.i32 x, .i32 y]
  if (repr fwd2).pretty != (repr ev2).pretty then
    throw (IO.userError "overload leaf-2 eval/fwd mismatch")
  if (repr fwd3).pretty != (repr ev3).pretty then
    throw (IO.userError "overload leaf-3 eval/fwd mismatch")
  if (repr fwdU).pretty != (repr evU).pretty then
    throw (IO.userError "use_add eval/fwd mismatch")
  match fwd2, fwd3, fwdU with
  | .ok (.i32 s2), .ok (.i32 s3), .ok (.i32 su) =>
    let native ← runNative overloadBin
      #[toString x.toInt, toString y.toInt, toString z.toInt]
    match native.splitOn " " with
    | [a2s, a3s, us] =>
      match a2s.toInt?, a3s.toInt?, us.toInt? with
      | some m2, some m3, some mu =>
        if m2 != s2.toInt || m3 != s3.toInt || mu != su.toInt then
          throw (IO.userError s!"overload mismatch: lean={(s2.toInt, s3.toInt, su.toInt)} native={(m2, m3, mu)}")
        pure 1
      | _, _, _ => throw (IO.userError s!"overload native unparsable: {native}")
    | _ => throw (IO.userError s!"overload native shape unexpected: {native}")
  | _, _, _ => pure 1

/-- Directed namespace pairs: ok paths, overflow, boundaries. -/
def nsEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (1, 2), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF),
   (0x7FFFFFFF, 0x7FFFFFFF), (0x80000000, 0x80000000)]

def checkNsAdd (nsBin : String) (x y : BitVec 32) : IO Nat := do
  let fwd := useNsAddFwd x y
  let ev := evalProgFunc [{ addFunc with name := "_ZN2ns3addEii" }] EVAL_FUEL
    useNsAddFunc [.i32 x, .i32 y]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "use_ns_add eval/fwd mismatch")
  match fwd with
  | .error _ => pure 1
  | .ok (.i32 s) =>
    let native ← runNative nsBin #[toString x.toInt, toString y.toInt]
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"ns_add mismatch: lean={s.toInt} native={m}")
      pure 1
    | none => throw (IO.userError s!"ns_add native unparsable: {native}")
  | .ok _ => throw (IO.userError "ns_add eval shape unexpected")

def main (args : List String) : IO Unit := do
  let overloadBin := args.getD 0 "/tmp/opencode/circe_overload_native"
  let nsBin := args.getD 1 "/tmp/opencode/circe_ns_add_native"
  let trials := (args.getD 2 "1000").toNat?.getD 1000
  let mut passed := 0
  for (x, y, z) in overloadEdges do
    let c ← checkOverload overloadBin x y z
    passed := passed + c
  for (x, y) in nsEdges do
    let c ← checkNsAdd nsBin x y
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values: sums usually stay in range (native agrees);
    -- overflows exercise the Lean-Lean path.
    let xi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let yi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let zi : Int := ((s % 61 : Nat) : Int) - 30
    let c ← checkOverload overloadBin (BitVec.ofInt 32 xi)
      (BitVec.ofInt 32 yi) (BitVec.ofInt 32 zi)
    passed := passed + c
    let c2 ← checkNsAdd nsBin (BitVec.ofInt 32 xi) (BitVec.ofInt 32 yi)
    passed := passed + c2
  IO.println s!"DIFFOVERLOAD-OK passed={passed} (edges + {trials} random trials)"

end DiffOverload
