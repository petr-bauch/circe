-- Golden test for N4d-iv-b1: `std::vector<int32_t>` growth leaves
-- pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenVecGrow.lean`
-- 1. Corpus pipeline: `tests/cir/vec_push_sum.cir` (real CIRGen
--    output: 53 defined defs) validates under per-def `.noalias`
--    oracle facts via `validateModule`: the 21 b1 leaf
--    representatives emit byte-identical text to
--    `tests/golden/VecGrow*.lean`, the admitted `_M_realloc_insert`,
--    `emplace_back`, `push_back`, and entry composers emit
--    byte-identical text to `tests/golden/VecGrowComposerRealloc*.lean`,
--    `tests/golden/VecGrowComposerEmplace*.lean`,
--    `tests/golden/VecGrowComposerPushBack*.lean`, and
--    `tests/golden/VecGrowComposerEntry*.lean`, and every other def
--    validates (53 ok, 53 total — the admitted frontier).
-- 2. Rejection suite: call to an unknown vector callee (generic),
--    double call into `max_size` (site-count pin), `check_len`
--    called at the wrong arity (arity pin), bare vector pointer
--    without the attr triple (alias discipline), and a `push_back`
--    call stub (composer pin at single-func level).
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

namespace GoldenVecGrow

/-- Per-def `.noalias` facts for the 53-def `vec_push_sum` frontier
    (the gate probe's fact list; erased `int*`/`s8*`/`void*` params
    need no uniqueness inside pinned b1 shapes). -/
def vecGrowFacts : List OracleFact :=
  [⟨"_Z12vec_push_sumv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEEC2Ev", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE9push_backEOi", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEEixEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEED2Ev", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEEC2Ev", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE12_Vector_implC2Ev", .noalias⟩,
   ⟨"_ZNSaIiEC2Ev", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE17_Vector_impl_dataC2Ev", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiEC2Ev", .noalias⟩,
   ⟨"_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEED2Ev", .noalias⟩,
   ⟨"_ZSt8_DestroyIPiEvT_S1_", .noalias⟩,
   ⟨"_ZNSt12_Destroy_auxILb1EE9__destroyIPiEEvT_S3_", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE12_Vector_implD2Ev", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE10deallocateEPim", .noalias⟩,
   ⟨"_ZNSaIiED2Ev", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiED2Ev", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT_", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE3endEv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE4backEv", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE9constructIiJiEEEvPT_DpOT0_", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc", .noalias⟩,
   ⟨"_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE5beginEv", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEE4baseEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE7destroyIiEEvRS0_PT_", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE8max_sizeEv", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE4sizeEv", .noalias⟩,
   ⟨"_ZSt3maxImERKT_S2_S2_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE11_S_max_sizeERKS0_", .noalias⟩,
   ⟨"_ZNKSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE8max_sizeERKS0_", .noalias⟩,
   ⟨"_ZSt3minImERKT_S2_S2_", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE8max_sizeEv", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx13new_allocatorIiE8max_sizeEv", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv", .noalias⟩,
   ⟨"_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1_", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE8allocateERS0_m", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE8allocateEmPKv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE14_S_do_relocateEPiS2_S2_RS0_St17integral_constantIbLb1EE", .noalias⟩,
   ⟨"_ZSt12__relocate_aIPiS0_SaIiEET0_T_S3_S2_RT1_", .noalias⟩,
   ⟨"_ZSt14__relocate_a_1IiiENSt9enable_ifIXsr3std24__is_bitwise_relocatableIT_EE5valueEPS1_E4typeES2_S2_S2_RSaIT0_E", .noalias⟩,
   ⟨"_ZSt12__niter_baseIPiET_S1_", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEdeEv", .noalias⟩]

/-- The 21 b1 leaf representatives: corpus def name × golden stem. -/
def vecGrowLeaves : List (String × String) :=
  [("_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm", "VecGrowAlloc"),
   ("_ZNSt6vectorIiSaIiEE4backEv", "VecGrowBack"),
   ("_ZNSt6vectorIiSaIiEE5beginEv", "VecGrowBegin"),
   ("_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc", "VecGrowCheckLen"),
   ("_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0_", "VecGrowConstruct"),
   ("_ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim", "VecGrowDealloc"),
   ("_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim", "VecGrowDeallocGuard"),
   ("_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E", "VecGrowDestroyNoop"),
   ("_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT_", "VecGrowDestroyPtr"),
   ("_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv", "VecGrowDiffMax"),
   ("_ZNSt6vectorIiSaIiEED2Ev", "VecGrowDtor"),
   ("_ZNSt6vectorIiSaIiEEC2Ev", "VecGrowEmptyCtor"),
   ("_ZNSt6vectorIiSaIiEE3endEv", "VecGrowEnd"),
   ("_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", "VecGrowGetTp"),
   ("_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1_", "VecGrowIterId"),
   ("_ZSt3maxImERKT_S2_S2_", "VecGrowMax"),
   ("_ZSt3minImERKT_S2_S2_", "VecGrowMin"),
   ("_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl", "VecGrowMinusEl"),
   ("_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB_", "VecGrowMinus"),
   ("_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0_", "VecGrowReloc"),
   ("_ZN9__gnu_cxx13new_allocatorIiEC2Ev", "VecGrowUnit")]

/-- The admitted N4d-iv-b2 composers: corpus def name × golden stem
    (each validates to its composer `Func` and emits byte-identical
    text). -/
def vecGrowAdmitted : List (String × String) :=
  [("_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT_",
    "VecGrowComposerRealloc"),
   ("_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT_",
    "VecGrowComposerEmplace"),
   ("_ZNSt6vectorIiSaIiEE9push_backEOi",
    "VecGrowComposerPushBack"),
   ("_Z12vec_push_sumv",
    "VecGrowComposerEntry")]

/-- Per-def `.noalias` facts for the 55-def `vec_reserve_sum` frontier
    (same discipline as `vecGrowFacts`: every defined def carries an
    explicit fact; erased params need no uniqueness inside pinned
    shapes). -/
def vecReserveFacts : List OracleFact :=
  [⟨"_Z15vec_reserve_sumv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEEC2Ev", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE7reserveEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE9push_backEOi", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEEixEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEED2Ev", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEEC2Ev", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE12_Vector_implC2Ev", .noalias⟩,
   ⟨"_ZNSaIiEC2Ev", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE17_Vector_impl_dataC2Ev", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiEC2Ev", .noalias⟩,
   ⟨"_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEED2Ev", .noalias⟩,
   ⟨"_ZSt8_DestroyIPiEvT_S1_", .noalias⟩,
   ⟨"_ZNSt12_Destroy_auxILb1EE9__destroyIPiEEvT_S3_", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE12_Vector_implD2Ev", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE10deallocateEPim", .noalias⟩,
   ⟨"_ZNSaIiED2Ev", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiED2Ev", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE8max_sizeEv", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE8capacityEv", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE4sizeEv", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE11_S_max_sizeERKS0_", .noalias⟩,
   ⟨"_ZNKSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE8max_sizeERKS0_", .noalias⟩,
   ⟨"_ZSt3minImERKT_S2_S2_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx13new_allocatorIiE8max_sizeEv", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE8allocateERS0_m", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE8allocateEmPKv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE14_S_do_relocateEPiS2_S2_RS0_St17integral_constantIbLb1EE", .noalias⟩,
   ⟨"_ZSt12__relocate_aIPiS0_SaIiEET0_T_S3_S2_RT1_", .noalias⟩,
   ⟨"_ZSt14__relocate_a_1IiiENSt9enable_ifIXsr3std24__is_bitwise_relocatableIT_EE5valueEPS1_E4typeES2_S2_S2_RSaIT0_E", .noalias⟩,
   ⟨"_ZSt12__niter_baseIPiET_S1_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT_", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE3endEv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE4backEv", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE9constructIiJiEEEvPT_DpOT0_", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc", .noalias⟩,
   ⟨"_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE5beginEv", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEE4baseEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE7destroyIiEEvRS0_PT_", .noalias⟩,
   ⟨"_ZSt3maxImERKT_S2_S2_", .noalias⟩,
   ⟨"_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1_", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEdeEv", .noalias⟩]

/-- The N7b admitted shapes: the `capacity` leaf, the `reserve`
    composer, and the closed `vec_reserve_sum` entry (each validates
    to its canonical `Func` and emits byte-identical text). -/
def vecReserveAdmitted : List (String × String) :=
  [("_ZNKSt6vectorIiSaIiEE8capacityEv", "VecGrowCapacity"),
   ("_ZNSt6vectorIiSaIiEE7reserveEm", "VecGrowComposerReserve"),
   ("_Z15vec_reserve_sumv", "VecGrowComposerReserveEntry")]

def checkVecGrowReservePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_reserve_sum.cir"
  let res := validateModule text vecReserveFacts
  if res.length != 55 then
    throw (IO.userError s!"vec-reserve frontier drift: {res.length} defs, expected 55")
  let errs := res.filter (fun (_, v) => !v.isOk)
  if errs.length != 0 then
    throw (IO.userError s!"vec-reserve rejects drift: {errs.length} errors, expected 0 (entry admitted)")
  for (name, g) in vecReserveAdmitted do
    match res.find? (fun (m, _) => m == name) with
    | none =>
      throw (IO.userError s!"vec-reserve admitted shape missing: {name}")
    | some (_, .error rej) =>
      throw (IO.userError s!"vec-reserve admitted shape rejected: {name}: {rej.message}")
    | some (_, .ok f) =>
      let want ← IO.FS.readFile s!"tests/golden/{g}.lean"
      let got := emitFileText (emitFunc f)
      if got != want then
        throw (IO.userError s!"golden mismatch for {g} ({name})")
      let wantSpec ← IO.FS.readFile s!"tests/golden/{g}_Spec.lean"
      let gotSpec ← match emitSpec f with
        | .ok s => pure s
        | .error _ => throw (IO.userError s!"spec emit failed for {g} ({name})")
      if gotSpec != wantSpec then
        throw (IO.userError s!"spec golden mismatch for {g} ({name})")
  IO.println "PASS pipeline vec_reserve_sum (capacity + reserve + entry byte-identical)"
  pure vecReserveAdmitted.length

/-- Per-def `.noalias` facts for the 73-def `vec_insert_sum` frontier
    (same discipline as `vecReserveFacts`: every defined def carries an
    explicit fact; erased params need no uniqueness inside pinned
    shapes, and the shift chain is covered by `isVecGrowShape`). -/
def vecInsertFacts : List OracleFact :=
  [⟨"_Z14vec_insert_sumv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEEC2Ev", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE7reserveEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE9push_backEOi", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE6insertEN9__gnu_cxx17__normal_iteratorIPKiS1_EEOi", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE5beginEv", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEplEl", .noalias⟩,
   ⟨"_ZN9__gnu_cxx17__normal_iteratorIPKiSt6vectorIiSaIiEEEC2IPiEERKNS0_IT_NS_11__enable_ifIXsr3std10__are_sameIS9_S8_EE7__valueES5_E6__typeEEE", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEEixEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEED2Ev", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEEC2Ev", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE12_Vector_implC2Ev", .noalias⟩,
   ⟨"_ZNSaIiEC2Ev", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE17_Vector_impl_dataC2Ev", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiEC2Ev", .noalias⟩,
   ⟨"_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEED2Ev", .noalias⟩,
   ⟨"_ZSt8_DestroyIPiEvT_S1_", .noalias⟩,
   ⟨"_ZNSt12_Destroy_auxILb1EE9__destroyIPiEEvT_S3_", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE12_Vector_implD2Ev", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE10deallocateEPim", .noalias⟩,
   ⟨"_ZNSaIiED2Ev", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiED2Ev", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE8max_sizeEv", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE8capacityEv", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE4sizeEv", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE11_S_max_sizeERKS0_", .noalias⟩,
   ⟨"_ZNKSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE8max_sizeERKS0_", .noalias⟩,
   ⟨"_ZSt3minImERKT_S2_S2_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx13new_allocatorIiE8max_sizeEv", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE8allocateERS0_m", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE8allocateEmPKv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE14_S_do_relocateEPiS2_S2_RS0_St17integral_constantIbLb1EE", .noalias⟩,
   ⟨"_ZSt12__relocate_aIPiS0_SaIiEET0_T_S3_S2_RT1_", .noalias⟩,
   ⟨"_ZSt14__relocate_a_1IiiENSt9enable_ifIXsr3std24__is_bitwise_relocatableIT_EE5valueEPS1_E4typeES2_S2_S2_RSaIT0_E", .noalias⟩,
   ⟨"_ZSt12__niter_baseIPiET_S1_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT_", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE3endEv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE4backEv", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE9constructIiJiEEEvPT_DpOT0_", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc", .noalias⟩,
   ⟨"_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEE4baseEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE7destroyIiEEvRS0_PT_", .noalias⟩,
   ⟨"_ZSt3maxImERKT_S2_S2_", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT_", .noalias⟩,
   ⟨"_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEdeEv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE14_M_insert_rvalEN9__gnu_cxx17__normal_iteratorIPKiS1_EEOi", .noalias⟩,
   ⟨"_ZN9__gnu_cxxmiIPKiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS9_SC_", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE6cbeginEv", .noalias⟩,
   ⟨"_ZN9__gnu_cxxeqIPKiSt6vectorIiSaIiEEEEbRKNS_17__normal_iteratorIT_T0_EESB_", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE4cendEv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE13_M_insert_auxIiEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEOT_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPKiSt6vectorIiSaIiEEE4baseEv", .noalias⟩,
   ⟨"_ZN9__gnu_cxx17__normal_iteratorIPKiSt6vectorIiSaIiEEEC2ERKS2_", .noalias⟩,
   ⟨"_ZSt13move_backwardIPiS0_ET0_T_S2_S1_", .noalias⟩,
   ⟨"_ZSt22__copy_move_backward_aILb1EPiS0_ET1_T0_S2_S1_", .noalias⟩,
   ⟨"_ZSt12__miter_baseIPiET_S1_", .noalias⟩,
   ⟨"_ZSt12__niter_wrapIPiET_RKS1_S1_", .noalias⟩,
   ⟨"_ZSt23__copy_move_backward_a1ILb1EPiS0_ET1_T0_S2_S1_", .noalias⟩,
   ⟨"_ZSt23__copy_move_backward_a2ILb1EPiS0_ET1_T0_S2_S1_", .noalias⟩,
   ⟨"_ZNSt20__copy_move_backwardILb1ELb1ESt26random_access_iterator_tagE13__copy_move_bIiEEPT_PKS3_S6_S4_", .noalias⟩]

/-- The N7c admitted shapes: each new `vec_insert_sum` corpus def and
    the canonical-fragment kind it validates to (const-iterator twins
    stamp the shared `begin` / `end` / `minus` / `iter_id` canonical
    `Func`s; the five shift layers stamp the shared shift blit). -/
def vecInsertKinds : List (String × FragKind) :=
  [("_Z14vec_insert_sumv", .vecInsertSumEntry),
   ("_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEplEl", .vecPlusEl),
   ("_ZN9__gnu_cxxeqIPKiSt6vectorIiSaIiEEEEbRKNS_17__normal_iteratorIT_T0_EESB_",
    .vecIterEq),
   ("_ZN9__gnu_cxx17__normal_iteratorIPKiSt6vectorIiSaIiEEEC2IPiEERKNS0_IT_NS_11__enable_ifIXsr3std10__are_sameIS9_S8_EE7__valueES5_E6__typeEEE",
    .vecIterId),
   ("_ZN9__gnu_cxx17__normal_iteratorIPKiSt6vectorIiSaIiEEEC2ERKS2_",
    .vecIterId),
   ("_ZNK9__gnu_cxx17__normal_iteratorIPKiSt6vectorIiSaIiEEE4baseEv",
    .vecIterId),
   ("_ZSt12__miter_baseIPiET_S1_", .vecIterId),
   ("_ZSt12__niter_wrapIPiET_RKS1_S1_", .vecIterId),
   ("_ZN9__gnu_cxxmiIPKiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS9_SC_",
    .vecMinus),
   ("_ZNKSt6vectorIiSaIiEE6cbeginEv", .vecBegin),
   ("_ZNKSt6vectorIiSaIiEE4cendEv", .vecEnd),
   ("_ZSt13move_backwardIPiS0_ET0_T_S2_S1_", .vecShiftBack),
   ("_ZSt22__copy_move_backward_aILb1EPiS0_ET1_T0_S2_S1_", .vecShiftBack),
   ("_ZSt23__copy_move_backward_a1ILb1EPiS0_ET1_T0_S2_S1_", .vecShiftBack),
   ("_ZSt23__copy_move_backward_a2ILb1EPiS0_ET1_T0_S2_S1_", .vecShiftBack),
   ("_ZNSt20__copy_move_backwardILb1ELb1ESt26random_access_iterator_tagE13__copy_move_bIiEEPT_PKS3_S6_S4_",
    .vecShiftBack),
   ("_ZNSt6vectorIiSaIiEE13_M_insert_auxIiEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEOT_",
    .vecInsertAux),
   ("_ZNSt6vectorIiSaIiEE14_M_insert_rvalEN9__gnu_cxx17__normal_iteratorIPKiS1_EEOi",
    .vecInsertRval),
   ("_ZNSt6vectorIiSaIiEE6insertEN9__gnu_cxx17__normal_iteratorIPKiS1_EEOi",
    .vecInsert)]

/-- N7c gate: the 73-def `vec_insert_sum` frontier validates with no
    rejects, and every new def maps to its expected fragment kind
    (with `emitFunc` / `emitSpec` succeeding — golden byte-identity
    is pinned in N7c-iii). -/
def checkVecInsertGate : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_insert_sum.cir"
  let res := validateModule text vecInsertFacts
  if res.length != 73 then
    throw (IO.userError s!"vec-insert frontier drift: {res.length} defs, expected 73")
  let errs := res.filter (fun (_, v) => !v.isOk)
  for (name, v) in errs do
    match v with
    | .error rej => IO.println s!"vec-insert reject {name}: {rej.message}"
    | .ok _ => pure ()
  if errs.length != 0 then
    throw (IO.userError s!"vec-insert rejects drift: {errs.length} errors, expected 0 (entry admitted)")
  for (name, want) in vecInsertKinds do
    match res.find? (fun (m, _) => m == name) with
    | none =>
      throw (IO.userError s!"vec-insert admitted shape missing: {name}")
    | some (_, .error rej) =>
      throw (IO.userError s!"vec-insert admitted shape rejected: {name}: {rej.message}")
    | some (_, .ok f) =>
      if !decide (matchFrag f = some want) then
        throw (IO.userError s!"vec-insert kind mismatch for {name}")
      match emitFunc f with
      | .ok _ => pure ()
      | .error _ => throw (IO.userError s!"func emit failed for {name}")
      match emitSpec f with
      | .ok _ => pure ()
      | .error _ => throw (IO.userError s!"spec emit failed for {name}")
  IO.println "PASS gate vec_insert_sum (19 shapes pinned to fragment kinds)"
  pure vecInsertKinds.length

/-- N7c pin (`plEl` called at the wrong arity): known-leaf calls
    outside the admitted shapes reject loudly at single-func level. -/
def advPlusElStub : String :=
  "module {\n  cir.func @vple(%arg0: !cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E> {llvm.align = 8 : i64, llvm.dereferenceable = 8 : i64, llvm.nonnull, llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.call @_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEplEl(%arg0) : (!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>) -> (!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E)\n"
  ++ "    cir.return\n  }\n}"

def checkVecGrowPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_push_sum.cir"
  let res := validateModule text vecGrowFacts
  if res.length != 53 then
    throw (IO.userError s!"vec-grow frontier drift: {res.length} defs, expected 53")
  let errs := res.filter (fun (_, v) => !v.isOk)
  if errs.length != 0 then
    throw (IO.userError s!"vec-grow rejects drift: {errs.length} errors, expected 0 (entry admitted)")
  for (name, g) in vecGrowLeaves do
    match res.find? (fun (m, _) => m == name) with
    | none =>
      throw (IO.userError s!"vec-grow leaf missing from corpus: {name}")
    | some (_, .error rej) =>
      throw (IO.userError s!"vec-grow leaf unexpectedly rejected: {name}: {rej.message}")
    | some (_, .ok f) =>
      let want ← IO.FS.readFile s!"tests/golden/{g}.lean"
      let got := emitFileText (emitFunc f)
      if got != want then
        throw (IO.userError s!"golden mismatch for {g} ({name})")
  IO.println "PASS pipeline vec_push_sum (21 b1 leaves byte-identical)"
  for (name, g) in vecGrowAdmitted do
    match res.find? (fun (m, _) => m == name) with
    | none =>
      throw (IO.userError s!"vec-grow admitted composer missing: {name}")
    | some (_, .error rej) =>
      throw (IO.userError s!"vec-grow admitted composer rejected: {name}: {rej.message}")
    | some (_, .ok f) =>
      let want ← IO.FS.readFile s!"tests/golden/{g}.lean"
      let got := emitFileText (emitFunc f)
      if got != want then
        throw (IO.userError s!"golden mismatch for {g} ({name})")
      let wantSpec ← IO.FS.readFile s!"tests/golden/{g}_Spec.lean"
      let gotSpec ← match emitSpec f with
        | .ok s => pure s
        | .error _ => throw (IO.userError s!"spec emit failed for {g} ({name})")
      if gotSpec != wantSpec then
        throw (IO.userError s!"spec golden mismatch for {g} ({name})")
  IO.println "PASS pipeline vec_push_sum (4 admitted composers byte-identical)"
  pure (vecGrowLeaves.length + vecGrowAdmitted.length)

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecGrow (name text : String)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, .noalias⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecgrow: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecgrow: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecgrow: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecgrow {name} [{code}]"
    pure 1

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def checkLenEv : String :=
  "_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc"

def maxSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE8max_sizeEv"

def pushBackEv : String :=
  "_ZNSt6vectorIiSaIiEE9push_backEOi"

/-- Call to an unknown vector callee: generic call-shape rejection. -/
def advUnknownVecCallee : String :=
  "module {\n  cir.func @vcallx(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") attributes {\"nothrow\"} {\n"
  ++ "    cir.call @_ZNSt6vectorIiSaIiEEC2EvX(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> ()\n"
  ++ "    cir.return\n  }\n}"

/-- Two call sites into `max_size`: the site-count pin rejects. -/
def advDoubleMaxSize : String :=
  "module {\n  cir.func @vmax2(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @" ++ maxSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %b = cir.call @" ++ maxSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %s = cir.add %a, %b : !u64i\n    cir.return %s : !u64i\n  }\n}"

/-- `check_len` called at the wrong arity: no admitted shape takes one
    vector arg into the `check_len` leaf. -/
def advCheckLenWrongArity : String :=
  "module {\n  cir.func @vchka(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @" ++ checkLenEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    cir.return %a : !u64i\n  }\n}"

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @" ++ maxSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    cir.return %r : !u64i\n  }\n}"

/-- N7b pin (`reserve` call stub): `reserve` is no leaf — the
    single-func stub rejects with the generic call-shape message
    (only the full guarded composer body validates). -/
def advReserveStub : String :=
  "module {\n  cir.func @vrs(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") attributes {\"nothrow\"} {\n"
  ++ "    cir.call @_ZNSt6vectorIiSaIiEE7reserveEm(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> ()\n"
  ++ "    cir.return\n  }\n}"

/-- N4d-iv-b2 deferral pin (`push_back` call stub): growth composition
    rejects with the actionable composer message at single-func level. -/
def advPushBackComposer : String :=
  "module {\n  cir.func @vpb(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<!s32i> {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.call @" ++ pushBackEv ++ "(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !cir.ptr<!s32i>) -> ()\n"
  ++ "    cir.return\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecGrowPipeline
  passed := passed + c0
  let r1 ← checkRejectVecGrow "vcallx" advUnknownVecCallee
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r1
  let r2 ← checkRejectVecGrow "vmax2" advDoubleMaxSize
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r2
  let r3 ← checkRejectVecGrow "vchka" advCheckLenWrongArity
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r3
  let r4 ← checkRejectVecGrow "vbare" advBareVecPtr
    "alias-reject" "single-reference triple"
  passed := passed + r4
  let r5 ← checkRejectVecGrow "vpb" advPushBackComposer
    "out-of-subset" "N4d-iv-b2 growth composer"
  passed := passed + r5
  let c6 ← checkVecGrowReservePipeline
  passed := passed + c6
  let r6 ← checkRejectVecGrow "vrs" advReserveStub
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r6
  let c7 ← checkVecInsertGate
  passed := passed + c7
  let r7 ← checkRejectVecGrow "vple" advPlusElStub
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r7
  IO.println s!"GOLDENVECGROW-OK passed={passed}"

end GoldenVecGrow
