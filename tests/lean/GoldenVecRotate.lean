-- Golden test for in-place `std::vector<int>` left rotation by `k`
-- (triple entry-over-entry composition over the admitted
-- `vec_seg_reverse`: `seg(v, 0, k)`, `seg(v, k, n)`, `seg(v, 0, n)`,
-- no loop).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecRotate.main`).
-- 1. Corpus pipeline: `tests/cir/vec_rotate.cir` (real CIRGen
--    output: the 2-param `vec_rotate` entry with one `size` call and
--    three `vec_seg_reverse` calls with `(v, 0, k)`, `(v, k, n)`,
--    `(v, 0, n)` wiring, plus the `size` leaf; the seg callee is a
--    TU-local declaration) validates via `runModulePipeline` with NO
--    oracle facts and emits byte-identical text to
--    `tests/golden/VecRotate.lean` (new: the entry) and
--    `tests/golden/VecSize.lean` (shared leaf).
-- 2. Rejection suite: other entries are not rotate-shaped
--    (arity/call-targets), a self-recursive 2-param entry hits the
--    dedicated vector wrong-shape rejection, a bare vector pointer
--    without the attr triple hits `alias-reject`, and the
--    permuted-order near-miss (first/third seg calls swapped:
--    identical op counts, wrong wiring) is rejected by the
--    call-wiring pin.
import Circe.Validator

namespace GoldenVecRotate

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def checkRotatePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_rotate.cir"
  let wantRot ← IO.FS.readFile "tests/golden/VecRotate.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_rotate: {msg}")
  | .ok [("_Z10vec_rotateRSt6vectorIiSaIiEEm", gotRot),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize)] =>
    if gotRot != wantRot then
      throw (IO.userError "golden mismatch for vec_rotate entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    IO.println "PASS pipeline vec_rotate (entry + size, no oracle facts)"
    pure 2
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Shape probe: `name` in `file` must (or must not) match `shape`. -/
def checkShape (file entry : String) (shape : RawFunc → Bool)
    (want : Bool) (tag : String) : IO Nat := do
  let text ← IO.FS.readFile file
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-vecrotate: {file} failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == entry) with
    | none => throw (IO.userError s!"reject-vecrotate: {entry} not found")
    | some raw =>
      if shape raw != want then
        throw (IO.userError s!"reject-vecrotate: {tag} shape verdict wrong")
      IO.println s!"PASS reject-vecrotate {tag} [shape-exact]"
      pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectRot (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecrotate: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecrotate: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecrotate: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecrotate {name} [{code}]"
    pure 1

/-- Permuted-order near-miss: the corpus entry with the first and
    third `vec_seg_reverse` calls swapped (identical op counts, wrong
    wiring) must reject via the call-wiring pin. -/
def checkRejectPermuted : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_rotate.cir"
  let entry := (text.splitOn "cir.func @_ZNKSt6vectorIiSaIiEE4sizeEv")[0]!
  let calls := (entry.splitOn "\n").filter
    (containsSubstr · "cir.call @_Z15vec_seg_reverse")
  match calls with
  | [c1, _, c3] =>
    let perm := ((entry.replace c1 "@@@TMP@@@").replace c3 c1).replace
      "@@@TMP@@@" c3
    let oracle : OracleFact :=
      ⟨"_Z10vec_rotateRSt6vectorIiSaIiEEm", .unknown⟩
    match runPipeline perm oracle with
    | .ok got =>
      throw (IO.userError s!"reject-vecrotate: permuted unexpectedly accepted:\n{got}")
    | .error msg =>
      if !containsSubstr msg "out-of-subset" then
        throw (IO.userError s!"reject-vecrotate: permuted: expected code out-of-subset in: {msg}")
      IO.println "PASS reject-vecrotate permuted-order [out-of-subset]"
      pure 1
  | _ => throw (IO.userError "reject-vecrotate: permuted: corpus shape unexpected")

/-- Self-recursive 2-param entry: the call-multiset pin (no
    self-call) rejects via the wrong-shape branch. -/
def advRecursiveRot : String :=
  "module {\n  cir.func @vwrecrot(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    cir.call @vwrecrot(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> ()\n"
  ++ "    cir.return\n  }\n}"

/-- Bare vector pointer (plus one `u64` param) without the attr
    triple: the alias discipline rejects before shapes are even
    consulted. -/
def advBareRotPtr : String :=
  "module {\n  cir.func @vwbarerot(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.return\n  }\n}"

def rotateCir : String := "tests/cir/vec_rotate.cir"

def segCir : String := "tests/cir/vec_seg_reverse.cir"

def reverseCir : String := "tests/cir/vec_reverse.cir"

def sortCir : String := "tests/cir/vec_merge_sort.cir"

def rotateName : String :=
  "_Z10vec_rotateRSt6vectorIiSaIiEEm"

def sizeName : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def segName : String :=
  "_Z15vec_seg_reverseRSt6vectorIiSaIiEEmm"

def reverseName : String :=
  "_Z11vec_reverseRSt6vectorIiSaIiEE"

def sortName : String :=
  "_Z14vec_merge_sortRSt6vectorIiSaIiEES2_"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkRotatePipeline
  passed := passed + c0
  let r1 ← checkShape rotateCir rotateName isVecRotateShape true "rotate-accepts-vec_rotate"
  passed := passed + r1
  let r2 ← checkShape rotateCir sizeName isVecRotateShape false "size-not-rotate-shaped"
  passed := passed + r2
  let r3 ← checkShape segCir segName isVecRotateShape false "segentry-not-rotate-shaped"
  passed := passed + r3
  let r4 ← checkShape reverseCir reverseName isVecRotateShape false "reverse-not-rotate-shaped"
  passed := passed + r4
  let r5 ← checkShape sortCir sortName isVecRotateShape false "sort-not-rotate-shaped"
  passed := passed + r5
  let r6 ← checkShape segCir segName isVecSegReverseShape true "seg-sanity-still-seg-shaped"
  passed := passed + r6
  let r7 ← checkRejectRot "vwrecrot" advRecursiveRot .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r7
  let r8 ← checkRejectRot "vwbarerot" advBareRotPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r8
  let r9 ← checkRejectPermuted
  passed := passed + r9
  IO.println s!"GOLDENVECROTATE-OK passed={passed}"

end GoldenVecRotate
