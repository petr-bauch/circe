-- Differential test for the N4d-i `std::array<int, 4>` fragment:
-- verified Lean forwards (plus `evalFunc` / `evalProgFunc` composition)
-- vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffArray.main [bin trials]`).
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check) and, when all three `nsw` adds are
-- in-range, all agree with native (overflow cases assert Lean-Lean
-- agreement only — signed overflow is UB, so native has nothing to
-- compare; OOB indices likewise never reach native).
-- Mismatch = P0.
import Circe.Emit

namespace DiffArray

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed quads: ok paths, per-site overflow, boundaries. -/
def arrayEdges : List (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) :=
  [(0, 0, 0, 0), (1, 2, 3, 4), (0x7FFFFFFF, 0, 0, 0),
   (0x7FFFFFFF, 1, 0, 0), (1, 0x7FFFFFFF, 1, 0),
   (1, 1, 1, 0x7FFFFFFF), (0x80000000, 0x80000000, 0, 0)]

def checkArray (arrayBin : String)
    (a b c d : BitVec 32) : IO Nat := do
  let l : List (BitVec 32) := [a, b, c, d]
  -- Leaves: program-free evaluation agrees with the forwards at every
  -- const index (runtime composition check on the fused edge).
  for k in [0, 1, 2, 3] do
    let n : BitVec 64 := BitVec.ofNat 64 k
    let fwdRef := arrayRefFwd l n
    let evRef := evalFunc arrayRefFunc [.arr32 l, .u64 n]
    if (repr fwdRef).pretty != (repr evRef).pretty then
      throw (IO.userError s!"array_ref eval/fwd mismatch at {k}")
    let fwdAt := arrayAtFwd l n
    let evAt := evalFunc arrayAtFunc [.arr32 l, .u64 n]
    if (repr fwdAt).pretty != (repr evAt).pretty then
      throw (IO.userError s!"array_at eval/fwd mismatch at {k}")
  -- Entry: program evaluation over `arrayAtFunc` agrees with the
  -- threaded-add forward (runtime composition check).
  let fwdSum := arraySumFwd a b c d
  let evSum := evalProgFunc [arrayAtFunc] EVAL_FUEL arraySumFunc
    [.arr32 [a, b, c, d]]
  if (repr fwdSum).pretty != (repr evSum).pretty then
    throw (IO.userError "array_sum eval/fwd mismatch")
  -- Native only when the driver accepts the inputs (all three `nsw`
  -- sites in range); otherwise Lean-Lean agreement only.
  match fwdSum with
  | .ok (.i32 s) =>
    let native ← runNative arrayBin
      #[toString a.toInt, toString b.toInt, toString c.toInt,
        toString d.toInt]
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"array_sum mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"array_sum native unparsable: {native}")
  | _ => pure 1

def main (args : List String) : IO Unit := do
  let arrayBin := args.getD 0 "/tmp/opencode/circe_array_sum_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (a, b, c, d) in arrayEdges do
    let q ← checkArray arrayBin a b c d
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values: sums usually stay in range (native agrees);
    -- overflows exercise the Lean-Lean path.
    let ai : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let bi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let ci : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let di : Int := ((s % 61 : Nat) : Int) - 30
    let q ← checkArray arrayBin (BitVec.ofInt 32 ai) (BitVec.ofInt 32 bi)
      (BitVec.ofInt 32 ci) (BitVec.ofInt 32 di)
    passed := passed + q
  IO.println s!"DIFFARRAY-OK passed={passed} (edges + {trials} random trials)"

end DiffArray
