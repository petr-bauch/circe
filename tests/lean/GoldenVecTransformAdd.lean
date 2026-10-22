-- Golden test for the `vec_transform_add` entry: the validator
-- pipeline maps the new `.cir` module function-by-function and the
-- rendered output agrees with the checked-in goldens (the shared
-- `size` / `at` / `range_check` / `index` leaves reuse their
-- existing goldens — one admission pin, no duplicate gold).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecTransformAdd.main`).
import Circe.Validator

namespace GoldenVecTransformAdd

def checkTransformPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_transform_add.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecTransformAdd.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_transform_add: {msg}")
  | .ok [("_Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_transform_add entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for const at() composer")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for const operator[] leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    IO.println "PASS pipeline vec_transform_add (entry + size + at + at-mut + range_check + index + index-mut, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

def main : IO Unit := do
  let _ ← checkTransformPipeline
  IO.println "GOLDENVECTRANSFORMADD-OK"

end GoldenVecTransformAdd
