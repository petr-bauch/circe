-- Differential test for the visited-mark idiom over two live
-- vectors: verified Lean forward (plus `evalFunc` composition) vs
-- the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecMarkCount.main [bin trials]`).
-- Every trial asserts evaluation agrees with the gated fold
-- (runtime composition check) and, when the fold is `.ok` (all adds
-- in range), the entry agrees with native (exact words: the driver
-- requires `argc == 4 + nm + nv`, the N2d window-shift lesson).
-- Overflow cases assert Lean-Lean agreement only — signed overflow
-- is UB, so native has nothing to compare. Loud legs (seed miss,
-- short mask) assert the native exit-4 path against any Lean
-- `.error` (both failures throw `std::out_of_range` natively).
-- Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecMarkCount

namespace DiffVecMarkCount

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Directed vectors: seed hit, seed miss, short mask, all-masked,
    mask values above one, `nsw` overflow, empty inputs. -/
def vecMarkCountEdges : List (List (BitVec 32) × List (BitVec 32) × BitVec 64) :=
  [([1, 0, 1], [0, 0, 0], 0), ([1], [0], 5), ([1], [0, 0], 0),
   ([0, 0], [5, 6], 1), ([2], [7], 0),
   ([1, 1], [0x7FFFFFFF, 0x7FFFFFFF], 0), ([], [], 0), ([3], [], 0)]

def checkVecMarkCount (bin : String) (m vis : List (BitVec 32))
    (u : BitVec 64) : IO Nat := do
  -- Entry: call-free evaluation agrees with the gated fold
  -- (runtime composition check).
  let fwd := markFwd m vis u
  let ev := evalFunc vecMarkCountFunc [.stdVecVal m, .stdVecVal vis, .u64 u]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "mark_count eval/fwd mismatch")
  let args := #[toString m.length]
    ++ (m.toArray.map fun x => toString x.toInt)
    ++ #[toString vis.length]
    ++ (vis.toArray.map fun x => toString x.toInt)
    ++ #[toString u.toNat]
  match fwd with
  | .ok (.i32 t) =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"mark_count native failed on hit: {out.stderr}")
    match (out.stdout.trimAscii.toString).toInt? with
    | some got =>
      if got != t.toInt then
        throw (IO.userError s!"mark_count mismatch: lean={t.toInt} native={got}")
      pure 1
    | none =>
      throw (IO.userError s!"mark_count native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "mark_count unexpected non-integer forward")
  | .error (.Overflow) =>
    -- `nsw` overflow: Lean-Lean agreement only (signed overflow is
    -- UB — native wraps instead of throwing, so it has nothing to
    -- compare; the `vec_at_sum` overflow precedent).
    pure 1
  | .error _ =>
    -- Loud leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"mark_count native exit={out.exitCode}, expected 4 on miss")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_mark_count_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (m, vis, u) in vecMarkCountEdges do
    let q ← checkVecMarkCount asBin m vis u
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..5 per vector, driver cap 8); values
    -- stay small (±30) for hit rate; the vertex is in-bounds two
    -- trials in three, past-the-end otherwise (miss legs exercise
    -- the native exit-4 path).
    let nm := s % 6
    let mut m : List (BitVec 32) := []
    for _ in List.range nm do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      m := m ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let nv := s % 6
    let mut vis : List (BitVec 32) := []
    for _ in List.range nv do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      vis := vis ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let u : BitVec 64 :=
      if s % 3 == 2 then BitVec.ofNat 64 (nv + (s % 3))
      else BitVec.ofNat 64 (s % 6)
    let q ← checkVecMarkCount asBin m vis u
    passed := passed + q
  IO.println s!"DIFFVECMARKCOUNT-OK passed={passed} (edges + {trials} random trials)"

end DiffVecMarkCount
