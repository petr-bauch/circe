-- Differential test for the N7b `std::vector<int32_t>` `reserve`
-- fragment: verified Lean forwards (plus `evalFunc` /
-- `evalProgFunc` composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffReserve.main [bin trials]`).
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check) and the closed entry agrees with
-- native (`reserve(10)` + two pushes + two reads + add = `3`).
-- The `max_size` throw path asserts Lean-Lean agreement on `.error`
-- only (throwing has no native return to compare — `length_error`
-- is proof-covered). Mismatch = P0.
import Circe.Emit

namespace DiffReserve

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed `(len, cap, n)` triples: no-op (`n ≤ cap`), realloc
    (`cap < n`, zero and nonzero relocated words), boundary
    (`n == cap`). All respect the vector invariant (`len ≤ cap`)
    and keep the buffer length at `len`. -/
def reserveEdges : List (Nat × Nat × Nat) :=
  [(0, 0, 0), (0, 0, 10), (2, 2, 2), (2, 5, 3), (3, 3, 16), (1, 4, 4)]

def checkReserve (len cap n : Nat) : IO Nat := do
  let mut l : List (BitVec 32) := []
  for k in List.range len do
    l := l ++ [BitVec.ofNat 32 (k + 1)]
  let b : Vec32 := ⟨l, false⟩
  -- Capacity leaf: program-free evaluation agrees with the forward.
  let fwdCap := stdVecGrowCapacityFwd cap
  let evCap := evalFunc stdVecGrowCapacityFunc [.stdVecOwned b len cap]
  if (repr fwdCap).pretty != (repr evCap).pretty then
    throw (IO.userError s!"vec_capacity eval/fwd mismatch at ({len}, {cap})")
  -- Reserve composer: program evaluation agrees with the forward
  -- (runtime composition check over the allocate → relocate →
  -- deallocate pipeline, or the passthrough).
  let nbv := BitVec.ofNat 64 n
  let fwd := stdVecReserveFwd b len cap nbv
  let ev := evalProgFunc vecGrowProg EVAL_FUEL stdVecReserveFunc
    [.stdVecOwned b len cap, .u64 nbv]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError s!"vec_reserve eval/fwd mismatch at ({len}, {cap}, {n})")
  pure 1

/-- `max_size` throw: both sides report `.error` (no native return to
    compare — `n = 2 ^ 64 - 1` exceeds `max_size`). -/
def checkReserveThrow : IO Nat := do
  let b : Vec32 := ⟨[], false⟩
  let nbv := BitVec.ofNat 64 (2 ^ 64 - 1)
  match stdVecReserveFwd b 0 0 nbv,
      evalProgFunc vecGrowProg EVAL_FUEL stdVecReserveFunc
        [.stdVecOwned b 0 0, .u64 nbv] with
  | .error _, .error _ => pure 1
  | fwd, ev =>
    throw (IO.userError s!"vec_reserve throw disagreement: fwd={repr fwd} ev={repr ev}")

def checkEntry (reserveBin : String) : IO Nat := do
  -- Entry: program evaluation agrees with the value forward
  -- (runtime composition check over the closed script).
  let fwd := vecReserveSumEntryFwd
  let ev := evalProgFunc vecGrowProg EVAL_FUEL vecReserveSumEntryFunc []
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_reserve_sum eval/fwd mismatch")
  -- Native agrees (the closed script returns `3`).
  match fwd with
  | .ok (.i32 s) =>
    let native ← runNative reserveBin #[]
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"vec_reserve_sum mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"vec_reserve_sum native unparsable: {native}")
  | _ => throw (IO.userError "vec_reserve_sum forward not `.ok (.i32 _)`")

def main (args : List String) : IO Unit := do
  let reserveBin := args.getD 0 "/tmp/opencode/circe_vec_reserve_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  let e ← checkEntry reserveBin
  passed := passed + e
  let t ← checkReserveThrow
  passed := passed + t
  for (len, cap, n) in reserveEdges do
    let q ← checkReserve len cap n
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    let len := s % 5
    s := lcgNext s
    let extra := s % 5
    s := lcgNext s
    let n := s % 17
    let q ← checkReserve len (len + extra) n
    passed := passed + q
  IO.println s!"DIFFRESERVE-OK passed={passed} (entry + throw + {reserveEdges.length} edges + {trials} random trials)"

end DiffReserve
