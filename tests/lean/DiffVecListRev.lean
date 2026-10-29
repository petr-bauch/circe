-- Differential test for index-linked in-place reversal: verified Lean
-- forward (plus `evalFunc` composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecListRev.main [bin trials]`).
-- Every trial asserts evaluation agrees with the entry forward
-- (runtime composition check, which also validates model-fuel
-- sufficiency: the chase visits each link at most a bounded number of
-- times before it terminates or misses, so `nxt.length + 32` fuel
-- decides every input) and, when the chase is `.ok`, the native new
-- head AND the rewired link words agree with the forward chase (the
-- link leg is what sets reversal apart from a head-only spec: edges
-- pin the rewired links, not just the new head). The driver requires
-- `argc == 5 + nd + nn`, prints the head on line one and the final
-- `nxt` words on line two. Loud legs (OOB head, short `nxt`) assert
-- the native exit-4 path against any Lean `.error` (every miss throws
-- `std::out_of_range` natively). The native side runs under
-- `timeout 10`: a chase Lean cannot decide within model fuel would
-- hang the C++ (no fuel there), so a 124 is a loud disagreement
-- (P0), never a silent skip. Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecListRev

namespace DiffVecListRev

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846795005 + 1442695040888963407) % 2 ^ 64

/-- Reversal edges: 3-node chase (ret 2, links `[3,0,1]`), singleton,
    empty, mid-list head (index 0 untouched, ret 2), OOB head (loud),
    short `nxt` (loud), self-loop (the rewire diverts the chase, Lean
    and native agree on ret 0 with links `[0]`). -/
def vecListRevEdges : List (List (BitVec 32) × List (BitVec 32) ×
    BitVec 64 × BitVec 64) :=
  [([10, 20, 30], [1, 2, 3], 0, 3),
   ([7], [1], 0, 1),
   ([], [], 0, 0),
   ([10, 20, 30], [1, 2, 3], 1, 3),
   ([10], [0], 5, 1),
   ([10, 20], [1], 0, 2),
   ([9], [0], 0, 1)]

def checkVecListRev (bin : String) (data nxt : List (BitVec 32))
    (head n : BitVec 64) : IO Nat := do
  -- Entry: call-free evaluation agrees with the entry forward
  -- (runtime composition check; the fuel bound is sufficient: every
  -- chase either terminates, misses, or revisits a link, and a
  -- revisit cascades back to the seed, so `nxt.length + 32` decides
  -- every input).
  let F := nxt.length + 32
  let fwd := revFwd F data nxt head n
  let ev := evalFunc listRevFunc
    [.stdVecVal data, .stdVecVal nxt, .u64 head, .u64 n]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "list_rev eval/fwd mismatch")
  let args := #[toString data.length]
    ++ (data.toArray.map fun x => toString x.toInt)
    ++ #[toString nxt.length]
    ++ (nxt.toArray.map fun x => toString x.toInt)
    ++ #[toString head.toNat, toString n.toNat]
  let runNative : IO (Nat × List Int) := do
    let out ← IO.Process.output { cmd := "timeout", args := #["10", bin] ++ args }
    if out.exitCode == 124 then
      throw (IO.userError "list_rev native timed out on a chase Lean decides (P0)")
    if out.exitCode != 0 then
      throw (IO.userError s!"list_rev native failed on hit: {out.stderr}")
    let lines := (out.stdout.splitOn "\n").map (·.trimAscii.toString)
    match lines with
    | headLine :: nxtLine :: _ =>
      match headLine.toNat? with
      | none =>
        throw (IO.userError s!"list_rev native unparsable head: {out.stdout}")
      | some got =>
        let words := if nxtLine == "" then [] else
          nxtLine.splitOn " "
        let parsed ← words.mapM fun w =>
          match w.toInt? with
          | none => throw (IO.userError s!"list_rev native unparsable link word: {w}")
          | some i => pure i
        pure (got, parsed)
    | _ =>
      throw (IO.userError s!"list_rev native unparsable output: {out.stdout}")
  match revOuterFwd F nxt n n head with
  | .error _ =>
    -- Loud leg: native must exit 4 (caught `std::out_of_range`).
    let out ← IO.Process.output { cmd := "timeout", args := #["10", bin] ++ args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"list_rev native exit={out.exitCode}, expected 4 on miss")
  | .ok (nxt', prev, _) =>
    if (repr fwd).pretty != (repr (.ok (.u64 prev) : Result Value)).pretty then
      throw (IO.userError "list_rev entry/chase mismatch")
    let (got, words) ← runNative
    if got != prev.toNat then
      throw (IO.userError s!"list_rev mismatch: lean={prev.toNat} native={got}")
    if words.length != nxt'.length then
      throw (IO.userError s!"list_rev link count mismatch: lean={nxt'.length} native={words.length}")
    for k in List.range nxt'.length do
      match nxt'[k]?, words[k]? with
      | some w, some i =>
        if w.toInt != i then
          throw (IO.userError s!"list_rev link mismatch at {k}: lean={w.toInt} native={i}")
      | _, _ =>
        throw (IO.userError s!"list_rev link missing at {k}")
    pure 1

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_list_rev_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (data, nxt, head, n) in vecListRevEdges do
    let q ← checkVecListRev asBin data nxt head n
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    -- Small link values (indices, the sentinel region, occasional
    -- OOB): chains terminate, short vectors miss loudly, and
    -- original-link cycles exercise the rewire-divert legs (the
    -- chase is deterministic, so Lean decides every input and the
    -- native side is always comparable under the timeout backstop).
    s := lcgNext s
    let nn := s % 5
    let mut nxt : List (BitVec 32) := []
    for _ in List.range nn do
      s := lcgNext s
      nxt := nxt ++ [BitVec.ofNat 32 (s % (nn + 2))]
    s := lcgNext s
    let nd := s % 5
    let mut data : List (BitVec 32) := []
    for _ in List.range nd do
      s := lcgNext s
      data := data ++ [BitVec.ofNat 32 (s % 41)]
    s := lcgNext s
    let head : BitVec 64 := BitVec.ofNat 64 (s % (nn + 2))
    s := lcgNext s
    let n : BitVec 64 := BitVec.ofNat 64 (s % (nn + 2))
    let q ← checkVecListRev asBin data nxt head n
    passed := passed + q
  IO.println s!"DIFFVECLISTREV-OK passed={passed} (edges + {trials} random trials)"

end DiffVecListRev
