-- Differential test for the `std::vector::at` checked read:
-- verified Lean forwards (plus `evalFunc` composition) vs the native
-- C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecAt.main [bin trials]`).
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check): the `_M_range_check` guard, the `at()`
-- read at each in-range index plus the OOB index, and the entry. The
-- entry additionally agrees with native on nonempty vectors (exact
-- words: the driver requires `argc == 2 + n`, the N2d window-shift
-- lesson). The empty vector never reaches native on the value leg
-- (`at(0)` throws `std::out_of_range`); the OOB leg asserts
-- Lean-Lean `AssertFail` agreement plus the native-abort leg (the
-- binary must exit nonzero). There is no alias leg: the entry takes
-- a single reader, so two-reader aliasing is inexpressible here
-- (unlike N2d); the single-ref attr triple is pinned by the golden
-- rejection suite instead.
-- Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecAt

namespace DiffVecAt

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed vectors: empty (OOB), singletons, short reads,
    sign-extreme first elements (native print/parse roundtrip). -/
def vecAtEdges : List (List (BitVec 32)) :=
  [[], [0], [7], [1, 2, 3], [0x80000000], [0xFFFFFFFF]]

def checkVecAt (atBin : String) (l : List (BitVec 32)) : IO Nat := do
  -- Guard: evaluation agrees with the forward at index zero
  -- (runtime composition check on the fused guard).
  let n0 : BitVec 64 := BitVec.ofNat 64 0
  let fwdGuard := stdVecRangeCheckFwd l n0
  let evGuard := evalFunc stdVecRangeCheckFunc [.stdVecVal l, .u64 n0]
  if (repr fwdGuard).pretty != (repr evGuard).pretty then
    throw (IO.userError "range_check eval/fwd mismatch")
  -- Reads: every in-range index plus the OOB index agree
  -- Lean-Lean (the OOB leg is `AssertFail` on both sides).
  for k in List.range (l.length + 1) do
    let n : BitVec 64 := BitVec.ofNat 64 k
    let fwdAt := stdVecAtFwd l n
    let evAt := evalFunc stdVecAtFunc [.stdVecVal l, .u64 n]
    if (repr fwdAt).pretty != (repr evAt).pretty then
      throw (IO.userError s!"at eval/fwd mismatch at {k}")
  -- Entry: evaluation agrees with the forward.
  let fwdOne := vecAtOneFwd l
  let evOne := evalFunc vecAtOneFunc [.stdVecVal l]
  if (repr fwdOne).pretty != (repr evOne).pretty then
    throw (IO.userError "vec_at_one eval/fwd mismatch")
  match fwdOne with
  | .ok (.i32 s) =>
    let native ← runNative atBin
      (#[toString l.length] ++ (l.toArray.map fun x => toString x.toInt))
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"vec_at_one mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"vec_at_one native unparsable: {native}")
  | .error .AssertFail =>
    -- OOB leg: the native binary must abort on the empty vector
    -- (uncaught `std::out_of_range`), never print a value.
    let out ← IO.Process.output { cmd := atBin, args := #["0"] }
    if out.exitCode != 0 then pure 1
    else throw (IO.userError "vec_at_one native wrongly succeeded on empty vector")
  | _ =>
    throw (IO.userError "vec_at_one forward shape unexpected")

def main (args : List String) : IO Unit := do
  let atBin := args.getD 0 "/tmp/opencode/circe_vec_at_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for l in vecAtEdges do
    let q ← checkVecAt atBin l
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8, driver cap): empties exercise the
    -- OOB + native-abort leg, nonempties the native-agreement leg.
    let n := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range n do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      l := l ++ [BitVec.ofInt 32 xi]
    let q ← checkVecAt atBin l
    passed := passed + q
  IO.println s!"DIFFVECAT-OK passed={passed} (edges + {trials} random trials)"

end DiffVecAt
