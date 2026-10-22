-- Golden test for the `vec_partition` entry: the validator
-- pipeline maps the new `.cir` module function-by-function and the
-- rendered output agrees with the checked-in goldens (the shared
-- `size` / non-const `at` / `range_check` / non-const `index` leaves
-- reuse their existing goldens — one admission pin, no duplicate gold).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecPartition.main`).
import Circe.Validator

namespace GoldenVecPartition

def checkPartitionPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_partition.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecPartition.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_partition: {msg}")
  | .ok [("_Z13vec_partitionRSt6vectorIiSaIiEEi", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_partition entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    IO.println "PASS pipeline vec_partition (entry + size + at-mut + range_check + index-mut, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

def main : IO Unit := do
  let _ ← checkPartitionPipeline
  IO.println "GOLDENVECPARTITION-OK"

end GoldenVecPartition
