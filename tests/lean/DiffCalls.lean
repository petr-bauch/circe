-- Differential test for the S1 DAG-call fragment: verified Lean
-- `add_caller` / `sum_caller` (program evaluation + forwards) vs the
-- native C binaries.
--
-- Run: `lake env lean --run tests/lean/DiffCalls.lean <add_bin> <sum_bin> [trials]`
-- Every trial asserts evaluated `evalProgFunc` agrees with the value
-- forward (runtime composition check) and both agree with native
-- (in-range cases; overflow/err cases only assert Lean-Lean agreement —
-- signed overflow is UB, so native has nothing to compare).
-- Mismatch = P0.
import Circe.Emit

namespace DiffCalls

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed `add_caller` triples: ok paths, first-call overflow,
    second-call overflow, boundary values. -/
def addEdges : List (BitVec 32 × BitVec 32 × BitVec 32) :=
  [(0, 0, 0), (1, 2, 3), (0x7FFFFFFF, 0, 0), (0x7FFFFFFF, 1, 0),
   (0, 0x7FFFFFFF, 1), (0x80000000, 0, 0), (0x80000000, 0, 0xFFFFFFFF),
   (0x80000000, 0xFFFFFFFF, 0), (0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF),
   (0, 0, 1), (42, 58, 100)]

def checkAddCaller (addBin : String) (x y z : BitVec 32) : IO Nat := do
  let fwd := addCallerFwd x y z
  let ev := evalProgFunc [addFunc] EVAL_FUEL addCallerFunc [.i32 x, .i32 y, .i32 z]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.i32 r) =>
      let native ← runNative addBin
        #[toString x.toInt, toString y.toInt, toString z.toInt]
      match native.toInt? with
      | none => throw (IO.userError s!"add_caller native unparsable: {native}")
      | some m =>
        if m != r.toInt then
          throw (IO.userError s!"add_caller mismatch: ({x.toInt},{y.toInt},{z.toInt}) lean={r.toInt} native={m}")
        pure 1
    | .ok _ => throw (IO.userError s!"add_caller eval shape unexpected")
  else
    throw (IO.userError s!"add_caller eval/fwd mismatch (emit_correct violated at runtime)")

/-- Fixed edge cases for `sum_caller` (lengths; values fill below). -/
def sumCallEdges : List Nat :=
  [0, 1, 2, 3, 7, 8, 16, 31, 32, 63, 64]

def checkSumCaller (sumBin : String) (k : Nat) (vals : List (BitVec 32))
    (_hk : vals.length = k) : IO Nat := do
  let n := BitVec.ofNat 32 k
  let fwd := sumCallerFwd vals n
  let ev := evalProgFunc [sumFunc] EVAL_FUEL sumCallerFunc [.arr32 vals, .u32 n]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .ok (.u32 r) =>
      let native ← runNative sumBin
        ((toString k) :: vals.map (fun v => toString (BitVec.toNat v))).toArray
      match native.toNat? with
      | none => throw (IO.userError s!"sum_caller native unparsable: {native}")
      | some m =>
        if m != r.toNat then
          throw (IO.userError s!"sum_caller mismatch: n={k} lean={r.toNat} native={m}")
        pure 1
    | _ => throw (IO.userError s!"sum_caller eval shape unexpected")
  else
    throw (IO.userError s!"sum_caller eval/fwd mismatch (emit_correct violated at runtime)")

/-- `k` pseudorandom `u32` words from seed `s`. -/
def genVals : Nat → Nat → List (BitVec 32)
  | 0, _ => []
  | k + 1, s => BitVec.ofNat 32 (s % 2 ^ 32) :: genVals k (lcgNext s)

theorem genVals_length (k s : Nat) : (genVals k s).length = k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp [genVals, ih]

def main (args : List String) : IO Unit := do
  let addBin := args.getD 0 "/tmp/opencode/circe_add_caller_native"
  let sumBin := args.getD 1 "/tmp/opencode/circe_sum_caller_native"
  let trials := (args.getD 2 "1000").toNat?.getD 1000
  let mut passed := 0
  for (x, y, z) in addEdges do
    let c ← checkAddCaller addBin x y z
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Small signed values: the double add stays in range, so native agrees.
    let xi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let yi : Int := ((s % 61 : Nat) : Int) - 30
    s := lcgNext s
    let zi : Int := ((s % 61 : Nat) : Int) - 30
    let c ← checkAddCaller addBin (BitVec.ofInt 32 xi) (BitVec.ofInt 32 yi)
      (BitVec.ofInt 32 zi)
    passed := passed + c
  for k in sumCallEdges do
    let vals := genVals k (s + k)
    let c ← checkSumCaller sumBin k vals (genVals_length k (s + k))
    passed := passed + c
  for _ in List.range trials do
    s := lcgNext s
    let k := s % 65
    s := lcgNext s
    let vals := genVals k s
    let c ← checkSumCaller sumBin k vals (genVals_length k s)
    passed := passed + c
  IO.println s!"DIFFCALLS-OK passed={passed} (add edges + {trials} random triples, sum edges + {trials} random trials)"

end DiffCalls
