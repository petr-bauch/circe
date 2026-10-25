-- Differential test for the cursor-stack push kernel: verified
-- Lean forward (plus `evalFunc` composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecStackPush.main [bin trials]`).
-- Every trial asserts evaluation agrees with the guarded store
-- (runtime composition check: the updated workspace) and the
-- emitted pair-forward agrees with native (the updated vector plus
-- the advanced cursor — the cursor is pure wrapping `uadd`, so the
-- Diff asserts it directly; the driver requires `argc == 4 + n`,
-- the N2d window-shift lesson). There is no overflow leg: the only
-- arithmetic is the wrapping cursor add (no UB anywhere), and loud
-- legs (past-the-end cursor) assert the native exit-4 path against
-- the Lean `.error`. Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecStackPush

namespace DiffVecStackPush

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Directed vectors: hit, miss, singleton hit, empty miss,
    last-slot hit (cursor lands past the end — still in bounds for
    the store). -/
def vecStackPushEdges : List (List (BitVec 32) × BitVec 64 × BitVec 32) :=
  [([1, 2, 3], 1, 9), ([1, 2, 3], 3, 9), ([0], 0, 7),
   ([], 0, 7), ([1, 2], 1, 5)]

def checkVecStackPush (bin : String) (l : List (BitVec 32))
    (top : BitVec 64) (x : BitVec 32) : IO Nat := do
  -- Entry: call-free evaluation agrees with the guarded store
  -- (runtime composition check: the updated workspace).
  let fwd := stackPushFwd l top x
  let ev := evalFunc stackPushFunc [.stdVecVal l, .u64 top, .i32 x]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "stack_push eval/fwd mismatch")
  let args := #[toString l.length]
    ++ (l.toArray.map fun x => toString x.toInt)
    ++ #[toString top.toNat, toString x.toInt]
  match fwd with
  | .ok (.stdVecVal l') =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"stack_push native failed on hit: {out.stderr}")
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: t :: ws =>
      match m.toNat?, t.toNat? with
      | some k, some ntop =>
        let got := ws.filterMap (·.toInt?)
        if k != l'.length || got.length != l'.length ||
            got != l'.map (·.toInt) || ntop != (top + 1).toNat then
          throw (IO.userError s!"stack_push mismatch: lean={l'.map (·.toInt)}/{(top + 1).toNat} native={got}/{ntop}")
        pure 1
      | _, _ =>
        throw (IO.userError s!"stack_push native unparsable: {out.stdout}")
    | _ =>
      throw (IO.userError s!"stack_push native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "stack_push unexpected non-vector forward")
  | .error _ =>
    -- Loud leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"stack_push native exit={out.exitCode}, expected 4 on miss")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_stack_push_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (l, top, x) in vecStackPushEdges do
    let q ← checkVecStackPush asBin l top x
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8, driver cap); values stay small
    -- (±30) for hit rate; the cursor is in-bounds two trials in
    -- three, past-the-end otherwise (miss legs exercise the native
    -- exit-4 path).
    let len := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range len do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      l := l ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let top : BitVec 64 :=
      if s % 3 == 2 then BitVec.ofNat 64 (len + (s % 3))
      else BitVec.ofNat 64 (s % 9)
    s := lcgNext s
    let x : BitVec 32 :=
      BitVec.ofInt 32 (((s % 61 : Nat) : Int) - 30)
    let q ← checkVecStackPush asBin l top x
    passed := passed + q
  IO.println s!"DIFFVECSTACKPUSH-OK passed={passed} (edges + {trials} random trials)"

end DiffVecStackPush
