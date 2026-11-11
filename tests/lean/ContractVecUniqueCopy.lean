-- Contract-facade regression test (pillar-3 caller-record
-- contract): the squeeze-copy facade legs instantiate on
-- concrete data, the pack lemmas compute, and the invariant
-- entry composes. Run from the repo root via the driver
-- (`lake exe circe-test` runs `ContractVecUniqueCopy.main`).
import Circe.Contracts.VecUniqueCopy

namespace ContractVecUniqueCopy

/-- Fits leg on concrete data: an exact-size record returns
    the squeeze count over the squeezed prefix. -/
example : ∃ (w' : Nat) (lo' : List (BitVec 32)),
    memEvalProgFunc vecUniqueCopyProg 4 vecUniqueCopyFunc
      [.stdVecVal ([3, 1, 1] : List (BitVec 32)),
        .stdVecVal ([0, 0, 0] : List (BitVec 32))] =
      .ok (.u64 (BitVec.ofNat 64 w')) ∧
    lo'.take w' = dedupAdj [3, 1, 1] ∧
    w' = (dedupAdj ([3, 1, 1] : List (BitVec 32))).length ∧
    lo'.length = ([0, 0, 0] : List (BitVec 32)).length :=
  vec_unique_copy_contract 4 [3, 1, 1] [0, 0, 0]
    (by decide) (by decide) (by decide) (by decide)

/-- Fits leg with an oversized record: the extra tail words
    stay untouched, length preserved. -/
example : ∃ (w' : Nat) (lo' : List (BitVec 32)),
    memEvalProgFunc vecUniqueCopyProg 5 vecUniqueCopyFunc
      [.stdVecVal ([9, 8] : List (BitVec 32)),
        .stdVecVal ([7, 7, 7] : List (BitVec 32))] =
      .ok (.u64 (BitVec.ofNat 64 w')) ∧
    lo'.take w' = dedupAdj [9, 8] ∧
    w' = (dedupAdj ([9, 8] : List (BitVec 32))).length ∧
    lo'.length = ([7, 7, 7] : List (BitVec 32)).length :=
  vec_unique_copy_contract 5 [9, 8] [7, 7, 7]
    (by decide) (by decide) (by decide) (by decide)

/-- Short leg on concrete data: a one-word record for a
    two-word squeeze fails loud. -/
example : memEvalProgFunc vecUniqueCopyProg 3 vecUniqueCopyFunc
    [.stdVecVal ([1, 2] : List (BitVec 32)),
      .stdVecVal ([9] : List (BitVec 32))] =
    .error .AssertFail :=
  vec_unique_copy_contract_short 3 [1, 2] [9]
    (by decide) (by decide) (by decide) (by decide)

/-- Facade pieces compose: the `(1, 1)` seed establishes the
    invariant on a concrete nonempty input and record. -/
example : squeezeCopyInv ([3, 1, 1] : List (BitVec 32))
    ([0, 0, 0] : List (BitVec 32)) 1 1
    (([0, 0, 0] : List (BitVec 32)).set 0 3) :=
  squeezeCopyInv_entry 3 [1, 1] [0, 0, 0] (by decide)

/-- Pack lemma on concrete data: storing at the write head
    snocs the written word onto the taken prefix. -/
example : (([0, 0, 0] : List (BitVec 32)).set 0 3).take 1 =
    [3] := by
  have h := take_set_succ_self ([0, 0, 0] : List (BitVec 32))
    0 3 (by decide)
  simpa using h

def checkPack : IO Nat := do
  let mut n := 0
  let la : List (BitVec 32) := [3, 1, 1]
  let lo : List (BitVec 32) := [0, 0, 0]
  if (lo.set 0 3).take 1 != dedupAdj (la.take 1) then
    throw (IO.userError "contract-vecuniquecopy: seed prefix mismatch")
  IO.println "PASS contract-vecuniquecopy seed-prefix [concrete]"
  n := n + 1
  if ((lo.set 0 3).take 1).length != 1 then
    throw (IO.userError "contract-vecuniquecopy: take length mismatch")
  IO.println "PASS contract-vecuniquecopy take-length [concrete]"
  n := n + 1
  if (dedupAdj la).length != 2 then
    throw (IO.userError "contract-vecuniquecopy: squeezed length mismatch")
  IO.println "PASS contract-vecuniquecopy squeezed-length [concrete]"
  n := n + 1
  pure n

def main : IO Unit := do
  let c ← checkPack
  IO.println s!"CONTRACTVECUNIQUECOPY-OK passed={c}"

end ContractVecUniqueCopy
