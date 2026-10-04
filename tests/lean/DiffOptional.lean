-- Differential test for the N4d-ii `std::optional<int32_t>` fragment:
-- verified Lean forwards (plus `evalFunc` / `evalProgFunc` composition)
-- vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffOptional.main [bin trials]`).
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check) and, on both engaged and disengaged
-- inputs, the entry agrees with native (engaged returns the word,
-- disengaged the `-1` sentinel — both defined; only a direct
-- disengaged deref would be UB, and the model reports that path as
-- `AssertFail`, asserted Lean-Lean only and never sent to native).
-- Mismatch = P0.
import Circe.Emit

namespace DiffOptional

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed payload words: zero, unit, sentinel, boundaries. -/
def optEdges : List (BitVec 32) :=
  [0, 1, 0xFFFFFFFF, 0x7FFFFFFF, 0x80000000, 42]

def checkOptional (optBin : String)
    (x : BitVec 32) (engaged : Bool) : IO Nat := do
  let v : Option (BitVec 32) := if engaged then some x else none
  -- Leaves: program-free evaluation agrees with the forwards
  -- (runtime composition check on the fused edges).
  let fwdHas := optHasFwd v
  let evHas := evalFunc optHasFunc [.optVal v]
  if (repr fwdHas).pretty != (repr evHas).pretty then
    throw (IO.userError "opt_has eval/fwd mismatch")
  let fwdHasValue := optHasValueFwd v
  let evHasValue := evalFunc optHasValueFunc [.optVal v]
  if (repr fwdHasValue).pretty != (repr evHasValue).pretty then
    throw (IO.userError "opt_has_value eval/fwd mismatch")
  let fwdGet := optGetFwd v
  let evGet := evalFunc optGetFunc [.optVal v]
  if (repr fwdGet).pretty != (repr evGet).pretty then
    throw (IO.userError "opt_get eval/fwd mismatch")
  let fwdOp := optDerefOpFwd v
  let evOp := evalFunc optDerefOpFunc [.optVal v]
  if (repr fwdOp).pretty != (repr evOp).pretty then
    throw (IO.userError "opt_deref_op eval/fwd mismatch")
  -- Impl `_M_get`: program evaluation over the payload leaf agrees
  -- with the delegating forward (runtime composition check).
  let fwdImpl := optGetFwd v
  let evImpl := evalProgFunc [optGetFunc] EVAL_FUEL optImplGetFunc
    [.optVal v]
  if (repr fwdImpl).pretty != (repr evImpl).pretty then
    throw (IO.userError "opt_impl_get eval/fwd mismatch")
  -- Entry: program evaluation over the two leaves agrees with the
  -- sentinel forward (runtime composition check).
  let fwdDeref := optDerefFwd v
  let evDeref := evalProgFunc optDerefProg EVAL_FUEL optDerefFunc
    [.optVal v]
  if (repr fwdDeref).pretty != (repr evDeref).pretty then
    throw (IO.userError "opt_deref eval/fwd mismatch")
  -- Native on both paths (both defined: word on engaged, `-1`
  -- sentinel on disengaged).
  let native ← runNative optBin
    #[toString x.toInt, if engaged then "1" else "0"]
  match native.toInt? with
  | some m =>
    let want := if engaged then x.toInt else -1
    if m != want then
      throw (IO.userError s!"opt_deref mismatch: lean={want} native={m}")
    pure 1
  | none =>
    throw (IO.userError s!"opt_deref native unparsable: {native}")

def main (args : List String) : IO Unit := do
  let optBin := args.getD 0 "/tmp/opencode/circe_opt_deref_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for x in optEdges do
    let q ← checkOptional optBin x true
    passed := passed + q
    let q ← checkOptional optBin x false
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values exercise words and the sentinel path.
    let xi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let engaged := s % 2 == 0
    let q ← checkOptional optBin (BitVec.ofInt 32 xi) engaged
    passed := passed + q
  IO.println s!"DIFFOPTIONAL-OK passed={passed} (edges + {trials} random trials)"

end DiffOptional
