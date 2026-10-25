-- Differential test for the flat-2D index read: verified Lean
-- forward (plus `evalFunc` composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecMatAt.main [bin trials]`).
-- Every trial asserts evaluation agrees with the single checked read
-- at the wrapped index (runtime composition check) and the entry
-- agrees with native (exact words: the driver requires
-- `argc == 5 + n`, the N2d window-shift lesson). The index
-- computation wraps on both sides (C++ unsigned arithmetic — no UB
-- anywhere), so the native leg runs on every trial; miss legs assert
-- the native exit-4 path against the Lean `AssertFail`. Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecMatAt

namespace DiffVecMatAt

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Directed vectors: hit, miss, wrapping hit (lands on element 0),
    zero-stride hit, empty miss. -/
def vecMatAtEdges : List (List (BitVec 32) × BitVec 64 × BitVec 64 × BitVec 64) :=
  [([1, 2, 3], 3, 0, 2), ([1, 2, 3], 3, 1, 0),
   ([9, 8], 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF),
   ([5, 6], 0, 7, 1), ([], 3, 0, 0)]

def checkVecMatAt (bin : String) (l : List (BitVec 32))
    (ncols i j : BitVec 64) : IO Nat := do
  -- Entry: call-free evaluation agrees with the forward
  -- (runtime composition check).
  let fwd := matAtFwd l ncols i j
  let ev := evalFunc matAtFunc [.stdVecVal l, .u64 ncols, .u64 i, .u64 j]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "mat_at eval/fwd mismatch")
  let args := #[toString l.length]
    ++ (l.toArray.map fun x => toString x.toInt)
    ++ #[toString ncols.toNat, toString i.toNat, toString j.toNat]
  match fwd with
  | .ok (.i32 w) =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"mat_at native failed on hit: {out.stderr}")
    match (out.stdout.trimAscii.toString).toInt? with
    | some got =>
      if got != w.toInt then
        throw (IO.userError s!"mat_at mismatch: lean={w.toInt} native={got}")
      pure 1
    | none =>
      throw (IO.userError s!"mat_at native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "mat_at unexpected non-integer forward")
  | .error _ =>
    -- Loud leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"mat_at native exit={out.exitCode}, expected 4 on miss")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_mat_at_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (l, ncols, i, j) in vecMatAtEdges do
    let q ← checkVecMatAt asBin l ncols i j
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8, driver cap); values stay small
    -- (±30) for hit rate; dims/indices stay small three trials in
    -- four, go huge on the fourth (wrap legs exercise wrapping on
    -- both sides — no UB, native always runs).
    let len := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range len do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      l := l ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let big := s % 4 == 3
    s := lcgNext s
    let ncols : BitVec 64 :=
      if big then BitVec.ofNat 64 (2 ^ 64 - 1 - (s % 3)) else BitVec.ofNat 64 (s % 9)
    s := lcgNext s
    let i : BitVec 64 :=
      if big then BitVec.ofNat 64 (2 ^ 64 - 1 - (s % 3)) else BitVec.ofNat 64 (s % 9)
    s := lcgNext s
    let j : BitVec 64 :=
      if big then BitVec.ofNat 64 (2 ^ 64 - 1 - (s % 3)) else BitVec.ofNat 64 (s % 9)
    let q ← checkVecMatAt asBin l ncols i j
    passed := passed + q
  IO.println s!"DIFFVECMATAT-OK passed={passed} (edges + {trials} random trials)"

end DiffVecMatAt
