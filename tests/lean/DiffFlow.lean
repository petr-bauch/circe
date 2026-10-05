-- Differential test for the S3a control-flow fragment: verified Lean
-- `nested_sum` / `skip_sum` / `find_eq` / `cls` (evaluation + forwards)
-- vs the native C binaries.
--
-- Run: `lake env lean --run tests/lean/DiffFlow.lean <nested> <skip> <find> <cls> <cls_fall> <cls_dense> [trials]`
-- Every trial asserts evaluated `evalFuncFuel` agrees with the value
-- forward (runtime composition check) and both agree with native
-- (fuel-sufficient, in-range cases; fuel-exhausted / OOB cases only
-- assert Lean-Lean agreement — C has nothing to compare there).
-- Mismatch = P0.
import Circe.Emit

namespace DiffFlow

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed `nested_sum` bounds: empty ranges, unit, asymmetric,
    break-adjacent sizes, and the largest fuel-sufficient square
    (`60 * 61 = 3660 ≤ EVAL_FUEL`). -/
def nestedEdges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (0, 5), (5, 0), (1, 1), (2, 3), (3, 2), (5, 5),
   (7, 9), (8, 8), (10, 4), (60, 60)]

def checkNested (nestBin : String) (n m : BitVec 32) : IO Nat := do
  let fwd := nestedFwd n m
  let ev := evalFuncFuel EVAL_FUEL nestedFunc [.u32 n, .u32 m]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .ok (.u32 r) =>
      let native ← runNative nestBin #[toString n.toNat, toString m.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"nested_sum native unparsable: {native}")
      | some v =>
        if v != r.toNat then
          throw (IO.userError s!"nested_sum mismatch: n={n.toNat} m={m.toNat} lean={r.toNat} native={v}")
        pure 1
    | _ => throw (IO.userError s!"nested_sum eval shape unexpected")
  else
    throw (IO.userError s!"nested_sum eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `skip_sum` bounds: empty, below/at/above the `continue`
    (`2`) and `break` (`8`) points. -/
def skipEdges : List (BitVec 32) :=
  [0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 20, 100]

def checkSkip (skipBin : String) (n : BitVec 32) : IO Nat := do
  let fwd := skipFwd n
  let ev := evalFuncFuel EVAL_FUEL skipFunc [.u32 n]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .ok (.u32 r) =>
      let native ← runNative skipBin #[toString n.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"skip_sum native unparsable: {native}")
      | some v =>
        if v != r.toNat then
          throw (IO.userError s!"skip_sum mismatch: n={n.toNat} lean={r.toNat} native={v}")
        pure 1
    | _ => throw (IO.userError s!"skip_sum eval shape unexpected")
  else
    throw (IO.userError s!"skip_sum eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `find_eq` cases: empty, hit-first, hit-last, miss,
    needle past the bound, OOB length, early-hit past the length
    (Lean-Lean only: native would read out of bounds). -/
def findEdges : List (List (BitVec 32) × BitVec 32 × BitVec 32) :=
  [([], 0, 5), ([5], 1, 5), ([5], 1, 3), ([1, 2, 3], 3, 1),
   ([1, 2, 3], 3, 2), ([1, 2, 3], 3, 3), ([1, 2, 3], 3, 9),
   ([1, 2, 3], 2, 3), ([1, 2], 5, 9), ([7, 8], 5, 8)]

def checkFind (findBin : String) (l : List (BitVec 32)) (nv kv : BitVec 32) :
    IO Nat := do
  let fwd := findEqFwd l nv kv
  let ev := evalFuncFuel EVAL_FUEL findEqFunc [.arr32 l, .u32 nv, .u32 kv]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .ok (.u32 r) =>
      if nv.toNat ≤ l.length then
        let native ← runNative findBin
          (([toString kv.toNat, toString nv.toNat]
            ++ l.map (fun v => toString v.toNat)).toArray)
        match native.toNat? with
        | none => throw (IO.userError s!"find_eq native unparsable: {native}")
        | some v =>
          if v != r.toNat then
            throw (IO.userError s!"find_eq mismatch: lean={r.toNat} native={v}")
          pure 1
      else pure 1
    | .error _ => pure 1
    | _ => throw (IO.userError s!"find_eq eval shape unexpected")
  else
    throw (IO.userError s!"find_eq eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `cls` inputs: both cases, default, large values. -/
def clsEdges : List (BitVec 32) :=
  [0, 1, 2, 3, 10, 20, 30, 0xFFFFFFFF]

def checkCls (clsBin : String) (x : BitVec 32) : IO Nat := do
  let fwd := clsFwd x
  let ev := evalFunc clsFunc [.u32 x]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .ok (.u32 r) =>
      let native ← runNative clsBin #[toString x.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"cls native unparsable: {native}")
      | some v =>
        if v != r.toNat then
          throw (IO.userError s!"cls mismatch: x={x.toNat} lean={r.toNat} native={v}")
        pure 1
    | _ => throw (IO.userError s!"cls eval shape unexpected")
  else
    throw (IO.userError s!"cls eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `cls_fall` inputs: the fallthrough case, the target case,
    default, large values. -/
def clsFallEdges : List (BitVec 32) :=
  [0, 1, 2, 3, 10, 30, 0xFFFFFFFF]

def checkClsFall (clsFallBin : String) (x : BitVec 32) : IO Nat := do
  let fwd := clsFallFwd x
  let ev := evalFunc clsFallFunc [.u32 x]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .ok (.u32 r) =>
      let native ← runNative clsFallBin #[toString x.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"cls_fall native unparsable: {native}")
      | some v =>
        if v != r.toNat then
          throw (IO.userError s!"cls_fall mismatch: x={x.toNat} lean={r.toNat} native={v}")
        pure 1
    | _ => throw (IO.userError s!"cls_fall eval shape unexpected")
  else
    throw (IO.userError s!"cls_fall eval/fwd mismatch (emit_correct violated at runtime)")

/-- Directed `cls_dense` inputs: every case, default, large values. -/
def clsDenseEdges : List (BitVec 32) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 70, 80, 0xFFFFFFFF]

def checkClsDense (clsDenseBin : String) (x : BitVec 32) : IO Nat := do
  let fwd := clsDenseFwd x
  let ev := evalFunc clsDenseFunc [.u32 x]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .ok (.u32 r) =>
      let native ← runNative clsDenseBin #[toString x.toNat]
      match native.toNat? with
      | none => throw (IO.userError s!"cls_dense native unparsable: {native}")
      | some v =>
        if v != r.toNat then
          throw (IO.userError s!"cls_dense mismatch: x={x.toNat} lean={r.toNat} native={v}")
        pure 1
    | _ => throw (IO.userError s!"cls_dense eval shape unexpected")
  else
    throw (IO.userError s!"cls_dense eval/fwd mismatch (emit_correct violated at runtime)")

def main (args : List String) : IO Unit := do
  let nestBin := args.getD 0 "/tmp/opencode/circe_nested_native"
  let skipBin := args.getD 1 "/tmp/opencode/circe_skip_native"
  let findBin := args.getD 2 "/tmp/opencode/circe_find_native"
  let clsBin := args.getD 3 "/tmp/opencode/circe_cls_native"
  let clsFallBin := args.getD 4 "/tmp/opencode/circe_cls_fall_native"
  let clsDenseBin := args.getD 5 "/tmp/opencode/circe_cls_dense_native"
  let trials := (args.getD 6 "1000").toNat?.getD 1000
  let mut passed := 0
  for (n, m) in nestedEdges do
    let c ← checkNested nestBin n m
    passed := passed + c
  for n in skipEdges do
    let c ← checkSkip skipBin n
    passed := passed + c
  for (l, n, k) in findEdges do
    let c ← checkFind findBin l n k
    passed := passed + c
  for x in clsEdges do
    let c ← checkCls clsBin x
    passed := passed + c
  for x in clsFallEdges do
    let c ← checkClsFall clsFallBin x
    passed := passed + c
  for x in clsDenseEdges do
    let c ← checkClsDense clsDenseBin x
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    -- Fuel-sufficient squares: `n * (m + 1) ≤ 61 * 61 < EVAL_FUEL`.
    s := lcgNext s
    let n := BitVec.ofNat 32 (s % 61)
    s := lcgNext s
    let m := BitVec.ofNat 32 (s % 61)
    let c ← checkNested nestBin n m
    passed := passed + c
    -- Small bounds exercise both sides of the break/continue points.
    s := lcgNext s
    let c ← checkSkip skipBin (BitVec.ofNat 32 (s % 21))
    passed := passed + c
    -- Small arrays, small values, lengths around the bound.
    s := lcgNext s
    let len := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range len do
      s := lcgNext s
      l := l ++ [BitVec.ofNat 32 (s % 6)]
    s := lcgNext s
    let nn := BitVec.ofNat 32 (s % 11)
    s := lcgNext s
    let kk := BitVec.ofNat 32 (s % 6)
    let c ← checkFind findBin l nn kk
    passed := passed + c
    -- Full-range switch scrutinee (never fails, native always agrees).
    s := lcgNext s
    let c ← checkCls clsBin (BitVec.ofNat 32 s)
    passed := passed + c
    s := lcgNext s
    let c ← checkClsFall clsFallBin (BitVec.ofNat 32 s)
    passed := passed + c
    s := lcgNext s
    let c ← checkClsDense clsDenseBin (BitVec.ofNat 32 s)
    passed := passed + c
  IO.println s!"DIFFFLOW-OK passed={passed} (edges + {trials} random trials)"

end DiffFlow
