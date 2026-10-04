/-
Circe.Emit.VecGrow — N4d-iv-b1 `std::vector<int32_t>` growth leaves:
owned-triple constructors, destructor, allocator/max-size leaves,
`_M_check_len`, `_M_allocate`, `_M_deallocate`, `construct`,
iterators, and the relocate bulk-copy leaf.

The corpus (`tests/cpp/vec_push_sum.cpp`: default-construct, three
`push_back`, index-sum, destroy) captures 61 defs. Excluding the 8
declarations (fused, never admitted) and the 4 composers (N4d-iv-b2:
`vec_push_sum`, `push_back`, `emplace_back`, `_M_realloc_insert`),
47 defined defs admit here (plus the 2 iv-a reads, unchanged); every
b1 `Func` below is call-free (callees fused bottom-up — b1 has no
`callRet`: composition is the b2 story).

Value model: `Value.stdVecOwned (buf : Vec32) (len cap : Nat)` — the
uniquely-owned heap triple (`buf` carries the affine token, `len` /
`cap` reify `_M_finish - _M_start` / `_M_end_of_storage - _M_start`).
Iterators erase to `u64` offsets (`begin` is `0`, `end` is `len`).
A null buffer is the `len = cap = 0` triple (empty storage coincides
with null: `_M_allocate(0)` and the default ctor build the same
value, and every `if (p)` guard in the slice fires exactly when
`cap == 0` at its admitted call sites). The memory block for a
triple is the two header words plus the storage words
(`[len32, cap32] ++ buf.val`; cf. `spanVal`/`stdVecVal`).

Fusion table (defined def → canonical `Func`; the gate pins the exact
CIR text per def, see `isStdVecGrow*Shape` in `Circe.Validator`):
- default-ctor chain (`vector-C2`, `_Vector_base-C2`, `_Vector_impl-C2`,
  `_Vector_impl_data-C2` — the three null stores fuse to the empty
  triple) → `stdVecEmptyCtorFunc`.
- empty ctor/dtor leaves (`new_allocator-C2`, `allocator-C2`,
  `new_allocator-D2`, `allocator-D2`, `_Vector_impl-D2` — pure
  delegations of nothing) → `stdVecUnitFunc` (void as `i32 0`, the
  `accCtor` precedent).
- destructors (`vector-D2`, `_Vector_base-D2` — the destroy range is
  a no-op for `int`, the `cleanup` scopes fuse away, `_M_deallocate`
  inlined with its `n == 0` guard) → `stdVecDtorFunc`.
- destroy range (`_Destroy` × 2, `_Destroy_aux` — the trivial-`int`
  no-op chain) → `stdVecDestroyNoopFunc`.
- element destroy (`new_allocator::destroy`, `traits::destroy` —
  no-op for `int`) → `stdVecDestroyPtrFunc`.
- allocator projection (`_M_get_Tp_allocator` × 2 — the `_M_impl`
  member access fuses to the erased allocator) → `stdVecGetTpFunc`.
- max-size chain (`_M_max_size` — the `u64` div folds;
  `_S_max_size`/`max_size` — the `min` chain folds; all three are
  `2305843009213693951`) → `stdVecDiffMaxFunc`.
- allocator max (`new_allocator::max_size`, `traits::max_size` —
  both `4611686018427387903`) → `stdVecAllocMaxFunc`.
- `std::max` / `std::min` over `u64` (early-return-`if` form) →
  `stdVecMaxFunc` / `stdVecMinFunc`.
- `_M_check_len` (the `length_error` throw fuses to `fail`, the
  `size`/`max_size`/`max` calls inline, both `cir.ternary` map to
  `tif`/`if_`) → `stdVecCheckLenFunc`.
- allocate chain (`_M_allocate` — the `n == 0` ternary is kept, both
  branches build the same value; `traits::allocate`,
  `new_allocator::allocate` — the over-max throw pair fuses to
  `fail`, the dead `4 > 16` aligned-new skeleton drops, operator
  `new` is fresh storage like `boxNew`) → `stdVecAllocFunc`.
- deallocate chain (`traits::deallocate`, `new_allocator::deallocate`
  — unconditional consume; `_M_deallocate` — the `ptr_to_bool` guard
  is kept as the `n == 0` test, sound by the call-site invariant
  that a null `p` always pairs with `n == 0`) → `stdVecDeallocFunc` /
  `stdVecDeallocGuardFunc`.
- construct chain (`traits::construct`, `new_allocator::construct` —
  the placement store with the `&&`-arg double load fused) →
  `stdVecConstructFunc` (returns the updated triple; C++ `void`
  functionalized as triple threading so b2 can compose).
- `begin` / `end` (iterator-ctor call fused) → `stdVecBeginFunc` /
  `stdVecEndFunc`; `back` (the `end`/`miEl`/`deref` chain fused) →
  `stdVecBackFunc` (`len - 1` wrapping; empty is UB, the garbage
  offset goes `OOB` at first use).
- iterator identities (`__normal_iterator-C2`, `__niter_base`,
  `base` — the address-of-field collapses to the value,
  `operator*` — the pointer is the offset) → `stdVecIterIdFunc`.
- iterator minus (`miEl` — `cir.minus` + `ptr_stride` fuse to
  wrapping `usub`; `mi` — the double `base` + `ptr_diff` fuse to
  bit-exact `s64diff`) → `stdVecMinusElFunc` / `stdVecMinusFunc`.
- relocate chain (`_S_relocate`, `_S_do_relocate` — the
  `integral_constant` tag drops, `__relocate_a`,
  `__relocate_a_1` — the `count > 0` guard is subsumed by the
  `while_` trip count, `memmove` unrolls to the copy loop; the
  `result + count` pointer return is dropped — b2 recomputes the
  offset from `result + (last - first)`) → `stdVecRelocFunc`.
-/
import Circe.Emit.Fragment

/-! ## N4d-iv-b1: growth-leaf constants -/

/-- `_S_max_size` value: `min(diffmax, allocmax)` (`u64`). -/
def stdVecMaxDiff : Nat := 2305843009213693951

/-- `new_allocator::max_size` value: `(2^64 - 1) / 4` (`u64`). -/
def stdVecAllocMax : Nat := 4611686018427387903

def stdVecMaxDiffBV : BitVec 64 := BitVec.ofNat 64 stdVecMaxDiff
def stdVecAllocMaxBV : BitVec 64 := BitVec.ofNat 64 stdVecAllocMax

/-! ## N4d-iv-b1: default-ctor chain + empty leaves -/

/-- Mangled names fused into the empty-triple constructor. -/
def stdVecCtorName : String := "_ZNSt6vectorIiSaIiEEC2Ev"
def stdVecBaseCtorName : String := "_ZNSt12_Vector_baseIiSaIiEEC2Ev"
def stdVecImplCtorName : String :=
  "_ZNSt12_Vector_baseIiSaIiEE12_Vector_implC2Ev"
def stdVecImplDataCtorName : String :=
  "_ZNSt12_Vector_baseIiSaIiEE17_Vector_impl_dataC2Ev"

/-- Canonical CoreIR for the default-ctor chain: no params (the `this`
    chains fuse away, the `accCtor` precedent), the three null stores
    fuse to the empty triple. -/
def stdVecEmptyCtorFunc : Func :=
  ⟨stdVecCtorName, [], .vecBlock,
   .return_ (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0))))⟩

/-- Value-level forward for the default ctor: the empty triple. -/
def stdVecEmptyCtorFwd : Result Value :=
  .ok (.stdVecOwned ⟨[], false⟩ 0 0)

/-- `emit_correct` for the default ctor (any fuel). -/
theorem evalFuncFuel_stdVecEmptyCtor (F : Nat) :
    evalFuncFuel F stdVecEmptyCtorFunc [] = stdVecEmptyCtorFwd := by
  have hbind : bindArgs stdVecEmptyCtorFunc.args [] = some [] := rfl
  have hbody : stdVecEmptyCtorFunc.body =
      .return_ (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0)))) := rfl
  have h0 : (0 : Nat) < 2 ^ 64 := by decide
  have hnew : evalExpr (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0)))) [] =
      .ok (.stdVecOwned ⟨[], false⟩ 0 0) := by
    have h := evalExpr_vgrowNew_lit (BitVec.ofNat 64 0) []
    rw [ofNat64_toNat 0 h0] at h
    simpa using h
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, stdVecEmptyCtorFwd, hnew]

/-- Mangled names fused into the unit (empty-effect) leaf. -/
def stdVecNewAllocCtorName : String :=
  "_ZN9__gnu_cxx13new_allocatorIiEC2Ev"
def stdVecAllocCtorName : String := "_ZNSaIiEC2Ev"
def stdVecNewAllocDtorName : String :=
  "_ZN9__gnu_cxx13new_allocatorIiED2Ev"
def stdVecAllocDtorName : String := "_ZNSaIiED2Ev"
def stdVecImplDtorName : String :=
  "_ZNSt12_Vector_baseIiSaIiEE12_Vector_implD2Ev"

/-- Canonical CoreIR for the empty-effect leaves: no params, void as
    `i32 0` (the `accCtor` precedent). -/
def stdVecUnitFunc : Func :=
  ⟨stdVecNewAllocCtorName, [], .i 32,
   .return_ (.lit (.i32 (BitVec.ofNat 32 0)))⟩

/-- Value-level forward for the empty-effect leaves. -/
def stdVecUnitFwd : Result Value :=
  .ok (.i32 (BitVec.ofNat 32 0))

/-- `emit_correct` for the empty-effect leaves (any fuel). -/
theorem evalFuncFuel_stdVecUnit (F : Nat) :
    evalFuncFuel F stdVecUnitFunc [] = stdVecUnitFwd := by
  have hbind : bindArgs stdVecUnitFunc.args [] = some [] := rfl
  have hbody : stdVecUnitFunc.body =
      .return_ (.lit (.i32 (BitVec.ofNat 32 0))) := rfl
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, stdVecUnitFwd]

/-! ## N4d-iv-b1: destructors -/

/-- Mangled names fused into the destructor. -/
def stdVecDtorName : String := "_ZNSt6vectorIiSaIiEED2Ev"
def stdVecBaseDtorName : String := "_ZNSt12_Vector_baseIiSaIiEED2Ev"

/-- Canonical CoreIR for the destructor: the destroy range is a no-op
    for `int`, the `cleanup` scopes fuse away, `_M_deallocate` inlines
    with its null guard as the `0 < cap` test (C++ `if (p)` fires
    exactly when `cap == 0` fails, i.e. `0 < cap`, at every admitted
    call site — the null-iff-`cap == 0` convention). Returns the
    consumed triple (triple threading for b2). -/
def stdVecDtorFunc : Func :=
  ⟨stdVecDtorName,
   [{ name := "t", ty := .vecBlock, role := .owned }],
   .vecBlock,
   .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.vgrowCap "t"))
     (.seq (.vgrowFree "t") (.return_ (.var "t")))
     (.return_ (.var "t"))⟩

/-- Value-level forward for the destructor. -/
def stdVecDtorFwd (b : Vec32) (len cap : Nat) : Result Value :=
  if 0 < cap then
    match vecFree b with
    | .error e => .error e
    | .ok b' => .ok (.stdVecOwned b' len cap)
  else .ok (.stdVecOwned b len cap)

/-- Env fact for the destructor shape. -/
theorem envLookup_stdVecDtor_t (b : Vec32) (len cap : Nat) :
    envLookup [("t", .stdVecOwned b len cap)] "t" =
      some (.stdVecOwned b len cap) := by
  simp [envLookup]

/-- `emit_correct` for the destructor: live buffer consumed, empty
    triple passed through (any fuel; `cap < 2^64` keeps the capacity
    word in `ofNat` form). -/
theorem evalFuncFuel_stdVecDtor (F : Nat) (b : Vec32) (len cap : Nat)
    (hcap64 : cap < 2 ^ 64) :
    evalFuncFuel F stdVecDtorFunc [.stdVecOwned b len cap] =
      stdVecDtorFwd b len cap := by
  have hbind : bindArgs stdVecDtorFunc.args [.stdVecOwned b len cap] =
      some [("t", .stdVecOwned b len cap)] := rfl
  have hbody : stdVecDtorFunc.body =
      .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.vgrowCap "t"))
        (.seq (.vgrowFree "t") (.return_ (.var "t")))
        (.return_ (.var "t")) := rfl
  have ht := envLookup_stdVecDtor_t b len cap
  have hcond : 0 < cap →
      evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.vgrowCap "t"))
        [("t", .stdVecOwned b len cap)] = .ok (.b true) := by
    intro hlt
    simp [evalExpr, litVal, ht, BitVec.ult_eq_decide,
      ofNat64_toNat cap hcap64, hlt]
  have hcondF : ¬ 0 < cap →
      evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.vgrowCap "t"))
        [("t", .stdVecOwned b len cap)] = .ok (.b false) := by
    intro hlt
    simp [evalExpr, litVal, ht, BitVec.ult_eq_decide,
      ofNat64_toNat cap hcap64, hlt]
  by_cases hlt : 0 < cap
  · have hc := hcond hlt
    cases hfb : vecFree b with
    | error e =>
      have hdtor : stdVecDtorFwd b len cap = .error e := by
        simp [stdVecDtorFwd, hlt, hfb]
      cases F <;>
        simp only [evalFuncFuel, hbind, hbody, evalStmtFuel,
          evalStmtZero, evalStmtWith, hc, ht, hfb, hdtor]
    | ok b' =>
      have hup : envUpdate [("t", .stdVecOwned b len cap)] "t"
          (.stdVecOwned b' len cap) =
          some [("t", .stdVecOwned b' len cap)] := by
        simp [envUpdate]
      have hret : envLookup [("t", .stdVecOwned b' len cap)] "t" =
          some (.stdVecOwned b' len cap) := by
        simp [envLookup]
      have hvar : evalExpr (.var "t") [("t", .stdVecOwned b' len cap)] =
          .ok (.stdVecOwned b' len cap) := by
        simp [evalExpr, hret]
      have hdtor : stdVecDtorFwd b len cap =
          .ok (.stdVecOwned b' len cap) := by
        simp [stdVecDtorFwd, hlt, hfb]
      cases F <;>
        simp only [evalFuncFuel, hbind, hbody, evalStmtFuel,
          evalStmtZero, evalStmtWith, hc, ht, hfb, hup, hvar, hdtor]
  · have hc := hcondF hlt
    have hskip : stdVecDtorFwd b len cap =
        .ok (.stdVecOwned b len cap) := by
      simp [stdVecDtorFwd, hlt]
    have hvar0 : evalExpr (.var "t") [("t", .stdVecOwned b len cap)] =
        .ok (.stdVecOwned b len cap) := by
      simp [evalExpr, ht]
    cases F <;>
      simp only [evalFuncFuel, hbind, hbody, evalStmtFuel,
        evalStmtZero, evalStmtWith, hc, hvar0, hskip]

/-! ## N4d-iv-b1: destroy range (trivial-`int` no-op chain) -/

/-- Mangled names fused into the destroy-range no-op. -/
def stdVecDestroyName : String := "_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E"
def stdVecDestroy2Name : String := "_ZSt8_DestroyIPiEvT_S1_"
def stdVecDestroyAuxName : String :=
  "_ZNSt12_Destroy_auxILb1EE9__destroyIPiEEvT_S3_"

/-- Canonical CoreIR for the destroy range: two offsets in, void out
    (the `int` specialization destroys nothing; the delegation chain
    fuses to nothing). -/
def stdVecDestroyNoopFunc : Func :=
  ⟨stdVecDestroyName,
   [{ name := "a", ty := .u 64, role := .owned },
    { name := "b", ty := .u 64, role := .owned }],
   .i 32,
   .return_ (.lit (.i32 (BitVec.ofNat 32 0)))⟩

/-- Value-level forward for the destroy range. -/
def stdVecDestroyNoopFwd : Result Value :=
  .ok (.i32 (BitVec.ofNat 32 0))

/-- `emit_correct` for the destroy range (any fuel). -/
theorem evalFuncFuel_stdVecDestroyNoop (F : Nat) (a b : BitVec 64) :
    evalFuncFuel F stdVecDestroyNoopFunc [.u64 a, .u64 b] =
      stdVecDestroyNoopFwd := by
  have hbind : bindArgs stdVecDestroyNoopFunc.args [.u64 a, .u64 b] =
      some [("a", .u64 a), ("b", .u64 b)] := rfl
  have hbody : stdVecDestroyNoopFunc.body =
      .return_ (.lit (.i32 (BitVec.ofNat 32 0))) := rfl
  have hlit : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      [("a", .u64 a), ("b", .u64 b)] =
      .ok (.i32 (BitVec.ofNat 32 0)) := by
    simp [evalExpr, litVal]
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, stdVecDestroyNoopFwd, hlit]

/-- Mangled names fused into the single-pointer destroy no-op. -/
def stdVecNewAllocDestroyName : String :=
  "_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT_"
def stdVecTraitsDestroyName : String :=
  "_ZNSt16allocator_traitsISaIiEE7destroyIiEEvRS0_PT_"

/-- Canonical CoreIR for element destroy: one offset in, void out
    (no-op for `int`). -/
def stdVecDestroyPtrFunc : Func :=
  ⟨stdVecNewAllocDestroyName,
   [{ name := "p", ty := .u 64, role := .owned }],
   .i 32,
   .return_ (.lit (.i32 (BitVec.ofNat 32 0)))⟩

/-- Value-level forward for element destroy. -/
def stdVecDestroyPtrFwd : Result Value :=
  .ok (.i32 (BitVec.ofNat 32 0))

/-- `emit_correct` for element destroy (any fuel). -/
theorem evalFuncFuel_stdVecDestroyPtr (F : Nat) (p : BitVec 64) :
    evalFuncFuel F stdVecDestroyPtrFunc [.u64 p] =
      stdVecDestroyPtrFwd := by
  have hbind : bindArgs stdVecDestroyPtrFunc.args [.u64 p] =
      some [("p", .u64 p)] := rfl
  have hbody : stdVecDestroyPtrFunc.body =
      .return_ (.lit (.i32 (BitVec.ofNat 32 0))) := rfl
  have hlit : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      [("p", .u64 p)] = .ok (.i32 (BitVec.ofNat 32 0)) := by
    simp [evalExpr, litVal]
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, stdVecDestroyPtrFwd, hlit]

/-! ## N4d-iv-b1: allocator projection + max-size consts -/

/-- Mangled names fused into the allocator projection. -/
def stdVecGetTpName : String :=
  "_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv"
def stdVecGetTpConstName : String :=
  "_ZNKSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv"

/-- Canonical CoreIR for `_M_get_Tp_allocator`: the `_M_impl` member
    access fuses to the erased allocator (`i32 0` — the empty struct
    carries no data). -/
def stdVecGetTpFunc : Func :=
  ⟨stdVecGetTpName,
   [{ name := "t", ty := .vecBlock, role := .owned }],
   .i 32,
   .return_ (.lit (.i32 (BitVec.ofNat 32 0)))⟩

/-- Value-level forward for the allocator projection. -/
def stdVecGetTpFwd : Result Value :=
  .ok (.i32 (BitVec.ofNat 32 0))

/-- `emit_correct` for the allocator projection (any fuel). -/
theorem evalFuncFuel_stdVecGetTp (F : Nat) (b : Vec32) (len cap : Nat) :
    evalFuncFuel F stdVecGetTpFunc [.stdVecOwned b len cap] =
      stdVecGetTpFwd := by
  have hbind : bindArgs stdVecGetTpFunc.args [.stdVecOwned b len cap] =
      some [("t", .stdVecOwned b len cap)] := rfl
  have hbody : stdVecGetTpFunc.body =
      .return_ (.lit (.i32 (BitVec.ofNat 32 0))) := rfl
  have hlit : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      [("t", .stdVecOwned b len cap)] =
      .ok (.i32 (BitVec.ofNat 32 0)) := by
    simp [evalExpr, litVal]
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, stdVecGetTpFwd, hlit]

/-- Mangled names fused into the `diffmax` const
    (`2305843009213693951`). -/
def stdVecMMaxSizeName : String :=
  "_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv"
def stdVecSMaxSizeName : String :=
  "_ZNSt6vectorIiSaIiEE11_S_max_sizeERKS0_"
def stdVecMaxSizeName : String := "_ZNKSt6vectorIiSaIiEE8max_sizeEv"

/-- Canonical CoreIR for the max-size chain: the `u64` div
    (`_M_max_size`) and the `min(diffmax, allocmax)` chain
    (`_S_max_size`, `max_size`) all fold to the same const. -/
def stdVecDiffMaxFunc : Func :=
  ⟨stdVecMMaxSizeName, [], .u 64,
   .return_ (.lit (.u64 stdVecMaxDiffBV))⟩

/-- Value-level forward for the max-size chain. -/
def stdVecDiffMaxFwd : Result Value := .ok (.u64 stdVecMaxDiffBV)

/-- `emit_correct` for the max-size chain (any fuel). -/
theorem evalFuncFuel_stdVecDiffMax (F : Nat) :
    evalFuncFuel F stdVecDiffMaxFunc [] = stdVecDiffMaxFwd := by
  have hbind : bindArgs stdVecDiffMaxFunc.args [] = some [] := rfl
  have hbody : stdVecDiffMaxFunc.body =
      .return_ (.lit (.u64 stdVecMaxDiffBV)) := rfl
  have hlit : evalExpr (.lit (.u64 stdVecMaxDiffBV)) [] =
      .ok (.u64 stdVecMaxDiffBV) := by
    simp [evalExpr, litVal]
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, stdVecDiffMaxFwd, hlit]

/-- Mangled names fused into the allocator-max const
    (`4611686018427387903`). -/
def stdVecNewAllocMaxSizeName : String :=
  "_ZNK9__gnu_cxx13new_allocatorIiE8max_sizeEv"
def stdVecTraitsMaxSizeName : String :=
  "_ZNSt16allocator_traitsISaIiEE8max_sizeERKS0_"

/-- Canonical CoreIR for the allocator max: both delegations fold to
    `(2^64 - 1) / 4`. -/
def stdVecAllocMaxFunc : Func :=
  ⟨stdVecNewAllocMaxSizeName, [], .u 64,
   .return_ (.lit (.u64 stdVecAllocMaxBV))⟩

/-- Value-level forward for the allocator max. -/
def stdVecAllocMaxFwd : Result Value := .ok (.u64 stdVecAllocMaxBV)

/-- `emit_correct` for the allocator max (any fuel). -/
theorem evalFuncFuel_stdVecAllocMax (F : Nat) :
    evalFuncFuel F stdVecAllocMaxFunc [] = stdVecAllocMaxFwd := by
  have hbind : bindArgs stdVecAllocMaxFunc.args [] = some [] := rfl
  have hbody : stdVecAllocMaxFunc.body =
      .return_ (.lit (.u64 stdVecAllocMaxBV)) := rfl
  have hlit : evalExpr (.lit (.u64 stdVecAllocMaxBV)) [] =
      .ok (.u64 stdVecAllocMaxBV) := by
    simp [evalExpr, litVal]
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, stdVecAllocMaxFwd, hlit]

/-! ## N4d-iv-b1: `std::max` / `std::min` over `u64` -/

/-- Mangled name of `std::max` over `u64`. -/
def stdVecMaxName : String := "_ZSt3maxImERKT_S2_S2_"

/-- Canonical CoreIR for `max`: the early-return-`if` form
    (`if (a<b) return b; return a`). -/
def stdVecMaxFunc : Func :=
  ⟨stdVecMaxName,
   [{ name := "a", ty := .u 64, role := .owned },
    { name := "b", ty := .u 64, role := .owned }],
   .u 64,
   .if_ (.ult (.var "a") (.var "b"))
     (.return_ (.var "b"))
     (.return_ (.var "a"))⟩

/-- Value-level forward for `max`. -/
def stdVecMaxFwd (a b : BitVec 64) : Result Value :=
  .ok (.u64 (if a.ult b then b else a))

/-- Env facts for the `max` shape. -/
theorem envLookup_stdVecMax_a (a b : BitVec 64) :
    envLookup [("a", .u64 a), ("b", .u64 b)] "a" = some (.u64 a) := by
  simp [envLookup]

theorem envLookup_stdVecMax_b (a b : BitVec 64) :
    envLookup [("a", .u64 a), ("b", .u64 b)] "b" = some (.u64 b) := by
  simp [envLookup, show ("b" : String) ≠ "a" by decide]

/-- `emit_correct` for `max` (any fuel). -/
theorem evalFuncFuel_stdVecMax (F : Nat) (a b : BitVec 64) :
    evalFuncFuel F stdVecMaxFunc [.u64 a, .u64 b] = stdVecMaxFwd a b := by
  have hbind : bindArgs stdVecMaxFunc.args [.u64 a, .u64 b] =
      some [("a", .u64 a), ("b", .u64 b)] := rfl
  have hbody : stdVecMaxFunc.body =
      .if_ (.ult (.var "a") (.var "b"))
        (.return_ (.var "b"))
        (.return_ (.var "a")) := rfl
  have ha := envLookup_stdVecMax_a a b
  have hb := envLookup_stdVecMax_b a b
  have hva : evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 a) := by
    simp [evalExpr, ha]
  have hvb : evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 b) := by
    simp [evalExpr, hb]
  have hcond : evalExpr (.ult (.var "a") (.var "b"))
      [("a", .u64 a), ("b", .u64 b)] = .ok (.b (a.ult b)) := by
    simp [evalExpr, ha, hb]
  by_cases h : a.ult b
  · have hc : evalExpr (.ult (.var "a") (.var "b"))
        [("a", .u64 a), ("b", .u64 b)] = .ok (.b true) := by
      simp [hcond, h]
    have hmax : stdVecMaxFwd a b = .ok (.u64 b) := by
      simp [stdVecMaxFwd, h]
    cases F <;>
      simp only [evalFuncFuel, hbind, hbody, evalStmtFuel,
        evalStmtZero, evalStmtWith, hc, hvb, hmax]
  · have hc : evalExpr (.ult (.var "a") (.var "b"))
        [("a", .u64 a), ("b", .u64 b)] = .ok (.b false) := by
      simp [hcond, h]
    have hmax : stdVecMaxFwd a b = .ok (.u64 a) := by
      simp [stdVecMaxFwd, h]
    cases F <;>
      simp only [evalFuncFuel, hbind, hbody, evalStmtFuel,
        evalStmtZero, evalStmtWith, hc, hva, hmax]

/-- Mangled name of `std::min` over `u64`. -/
def stdVecMinName : String := "_ZSt3minImERKT_S2_S2_"

/-- Canonical CoreIR for `min`: the early-return-`if` form
    (`if (b<a) return b; return a`). -/
def stdVecMinFunc : Func :=
  ⟨stdVecMinName,
   [{ name := "a", ty := .u 64, role := .owned },
    { name := "b", ty := .u 64, role := .owned }],
   .u 64,
   .if_ (.ult (.var "b") (.var "a"))
     (.return_ (.var "b"))
     (.return_ (.var "a"))⟩

/-- Value-level forward for `min`. -/
def stdVecMinFwd (a b : BitVec 64) : Result Value :=
  .ok (.u64 (if b.ult a then b else a))

/-- `emit_correct` for `min` (any fuel). -/
theorem evalFuncFuel_stdVecMin (F : Nat) (a b : BitVec 64) :
    evalFuncFuel F stdVecMinFunc [.u64 a, .u64 b] = stdVecMinFwd a b := by
  have hbind : bindArgs stdVecMinFunc.args [.u64 a, .u64 b] =
      some [("a", .u64 a), ("b", .u64 b)] := rfl
  have hbody : stdVecMinFunc.body =
      .if_ (.ult (.var "b") (.var "a"))
        (.return_ (.var "b"))
        (.return_ (.var "a")) := rfl
  have ha := envLookup_stdVecMax_a a b
  have hb := envLookup_stdVecMax_b a b
  have hva : evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 a) := by
    simp [evalExpr, ha]
  have hvb : evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 b) := by
    simp [evalExpr, hb]
  have hcond : evalExpr (.ult (.var "b") (.var "a"))
      [("a", .u64 a), ("b", .u64 b)] = .ok (.b (b.ult a)) := by
    simp [evalExpr, ha, hb]
  by_cases h : b.ult a
  · have hc : evalExpr (.ult (.var "b") (.var "a"))
        [("a", .u64 a), ("b", .u64 b)] = .ok (.b true) := by
      simp [hcond, h]
    have hmin : stdVecMinFwd a b = .ok (.u64 b) := by
      simp [stdVecMinFwd, h]
    cases F <;>
      simp only [evalFuncFuel, hbind, hbody, evalStmtFuel,
        evalStmtZero, evalStmtWith, hc, hvb, hmin]
  · have hc : evalExpr (.ult (.var "b") (.var "a"))
        [("a", .u64 a), ("b", .u64 b)] = .ok (.b false) := by
      simp [hcond, h]
    have hmin : stdVecMinFwd a b = .ok (.u64 a) := by
      simp [stdVecMinFwd, h]
    cases F <;>
      simp only [evalFuncFuel, hbind, hbody, evalStmtFuel,
        evalStmtZero, evalStmtWith, hc, hva, hmin]

/-! ## N4d-iv-b1: `_M_check_len` -/

/-- Mangled name of `_M_check_len`. -/
def stdVecCheckLenName : String :=
  "_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc"

/-- The `newlen` core shared by the three uses: `len + max(len, n)`
    (the `__len` alloca unrolled — pure and total, so let-unrolling
    is semantics-preserving). -/
def stdVecNewLenExpr : CExpr :=
  .uadd (.vgrowLen "t")
    (.tif (.ult (.vgrowLen "t") (.var "n")) (.var "n") (.vgrowLen "t"))

/-- Canonical CoreIR for `_M_check_len`: the `length_error` throw fuses
    to `fail`, the `size`/`max_size`/`max` calls inline (the `s8`
    message param drops — unused), both `cir.ternary` map to
    `tif`/`if_`. -/
def stdVecCheckLenFunc : Func :=
  ⟨stdVecCheckLenName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "n", ty := .u 64, role := .owned }],
   .u 64,
   .if_ (.ult (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
           (.var "n"))
     .fail
     (.if_ (.ult stdVecNewLenExpr (.vgrowLen "t"))
       (.return_ (.lit (.u64 stdVecMaxDiffBV)))
       (.if_ (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
         (.return_ (.lit (.u64 stdVecMaxDiffBV)))
         (.return_ stdVecNewLenExpr)))⟩

/-- Value-level forward for `_M_check_len` (fully unrolled to mirror
    the Func: `BitVec`-level throughout, so no `toNat` bridges are
    needed for `emit_correct`). -/
def stdVecCheckLenFwd (len : Nat) (n : BitVec 64) : Result Value :=
  if (stdVecMaxDiffBV - BitVec.ofNat 64 len).ult n then
    .error .AssertFail
  else if (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len)).ult (BitVec.ofNat 64 len) then
    .ok (.u64 stdVecMaxDiffBV)
  else if stdVecMaxDiffBV.ult (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len)) then
    .ok (.u64 stdVecMaxDiffBV)
  else
    .ok (.u64 (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len)))

/-- Env facts for the `_M_check_len` shape. -/
theorem envLookup_stdVecCheckLen_t (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    envLookup [("t", .stdVecOwned b len cap), ("n", .u64 n)] "t" =
      some (.stdVecOwned b len cap) := by
  simp [envLookup]

theorem envLookup_stdVecCheckLen_n (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    envLookup [("t", .stdVecOwned b len cap), ("n", .u64 n)] "n" =
      some (.u64 n) := by
  simp [envLookup, show ("n" : String) ≠ "t" by decide]

/-- `emit_correct` for `_M_check_len` (any fuel; the `BitVec`-level
    Fwd needs no arithmetic side conditions). -/
theorem evalFuncFuel_stdVecCheckLen (F : Nat) (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    evalFuncFuel F stdVecCheckLenFunc [.stdVecOwned b len cap, .u64 n] =
      stdVecCheckLenFwd len n := by
  have hbind : bindArgs stdVecCheckLenFunc.args
      [.stdVecOwned b len cap, .u64 n] =
      some [("t", .stdVecOwned b len cap), ("n", .u64 n)] := rfl
  have hbody : stdVecCheckLenFunc.body =
      .if_ (.ult (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
              (.var "n"))
        .fail
        (.if_ (.ult stdVecNewLenExpr (.vgrowLen "t"))
          (.return_ (.lit (.u64 stdVecMaxDiffBV)))
          (.if_ (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
            (.return_ (.lit (.u64 stdVecMaxDiffBV)))
            (.return_ stdVecNewLenExpr))) := rfl
  have ht := envLookup_stdVecCheckLen_t b len cap n
  have hn := envLookup_stdVecCheckLen_n b len cap n
  have hlen : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht
  have hmaxlit : evalExpr (.lit (.u64 stdVecMaxDiffBV))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 stdVecMaxDiffBV) := by
    simp [evalExpr, litVal]
  have hnv : evalExpr (.var "n")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hsub : evalExpr
      (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 (stdVecMaxDiffBV - BitVec.ofNat 64 len)) :=
    evalExpr_usub_u64 _ _ _ _ hlen
  have hc1 : evalExpr
      (.ult (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
        (.var "n"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.b ((stdVecMaxDiffBV - BitVec.ofNat 64 len).ult n)) :=
    evalExpr_ult_u64 _ _ _ _ _ hsub hnv
  by_cases h1 : (stdVecMaxDiffBV - BitVec.ofNat 64 len).ult n
  · have hc : evalExpr
        (.ult (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
          (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .ok (.b true) := by
      simp [hc1, h1]
    have hfail : stdVecCheckLenFwd len n = .error .AssertFail := by
      simp [stdVecCheckLenFwd, h1]
    have hstmt : evalStmtFuel F stdVecCheckLenFunc.body
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .error .AssertFail := by
      rw [hbody]
      exact (evalStmtFuel_if_true _ _ _ _ _ hc).trans
        (evalStmtFuel_fail _ _)
    simp [evalFuncFuel, hbind, hstmt, hfail]
  · have hc : evalExpr
        (.ult (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
          (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .ok (.b false) := by
      simp [hc1, h1]
    have hmaxc : evalExpr (.ult (.vgrowLen "t") (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .ok (.b ((BitVec.ofNat 64 len).ult n)) :=
        evalExpr_ult_u64 _ _ _ _ _ hlen hnv
    by_cases h2 : (BitVec.ofNat 64 len).ult n
    · have hct : evalExpr (.ult (.vgrowLen "t") (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b true) := by
        simp [hmaxc, h2]
      have hm : evalExpr (.tif (.ult (.vgrowLen "t") (.var "n"))
            (.var "n") (.vgrowLen "t"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.u64 n) :=
        (evalExpr_tif_true _ _ _ _ hct).trans hnv
      have hnew : evalExpr stdVecNewLenExpr
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.u64 (BitVec.ofNat 64 len + n)) := by
        simp only [stdVecNewLenExpr]
        exact evalExpr_uadd_u64 _ _ _ _ _ hlen hm
      have hc2raw : evalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b ((BitVec.ofNat 64 len + n).ult
            (BitVec.ofNat 64 len))) :=
        evalExpr_ult_u64 _ _ _ _ _ hnew hlen
      by_cases h3 : (BitVec.ofNat 64 len + n).ult (BitVec.ofNat 64 len)
      · have hc2 : evalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b true) := by
          simp [hc2raw, h3]
        have hfwd : stdVecCheckLenFwd len n =
            .ok (.u64 stdVecMaxDiffBV) := by
          simp [stdVecCheckLenFwd, h1, h2, h3]
        have hstmt : evalStmtFuel F stdVecCheckLenFunc.body
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
              .returned (.u64 stdVecMaxDiffBV)) := by
          rw [hbody, evalStmtFuel_if_false F _ _ _ _ hc,
            evalStmtFuel_if_true F _ _ _ _ hc2]
          exact evalStmtFuel_return F _ _ _ hmaxlit
        simp [evalFuncFuel, hbind, hstmt, hfwd]
      · have hc2 : evalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b false) := by
          simp [hc2raw, h3]
        have hc3raw : evalExpr
            (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b (stdVecMaxDiffBV.ult
              (BitVec.ofNat 64 len + n))) :=
          evalExpr_ult_u64lit _ _ _ _ hnew
        by_cases h4 : stdVecMaxDiffBV.ult (BitVec.ofNat 64 len + n)
        · have hc3 : evalExpr
              (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
              [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
              .ok (.b true) := by
            simp [hc3raw, h4]
          have hfwd : stdVecCheckLenFwd len n =
              .ok (.u64 stdVecMaxDiffBV) := by
            simp [stdVecCheckLenFwd, h1, h2, h3, h4]
          have hstmt : evalStmtFuel F stdVecCheckLenFunc.body
              [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
              .ok ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
                .returned (.u64 stdVecMaxDiffBV)) := by
            rw [hbody, evalStmtFuel_if_false F _ _ _ _ hc,
              evalStmtFuel_if_false F _ _ _ _ hc2,
              evalStmtFuel_if_true F _ _ _ _ hc3]
            exact evalStmtFuel_return F _ _ _ hmaxlit
          simp [evalFuncFuel, hbind, hstmt, hfwd]
        · have hc3 : evalExpr
              (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
              [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
              .ok (.b false) := by
            simp [hc3raw, h4]
          have hfwd : stdVecCheckLenFwd len n =
              .ok (.u64 (BitVec.ofNat 64 len + n)) := by
            simp [stdVecCheckLenFwd, h1, h2, h3, h4]
          have hstmt : evalStmtFuel F stdVecCheckLenFunc.body
              [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
              .ok ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
                .returned (.u64 (BitVec.ofNat 64 len + n))) := by
            rw [hbody, evalStmtFuel_if_false F _ _ _ _ hc,
              evalStmtFuel_if_false F _ _ _ _ hc2,
              evalStmtFuel_if_false F _ _ _ _ hc3]
            exact evalStmtFuel_return F _ _ _ hnew
          simp [evalFuncFuel, hbind, hstmt, hfwd]
    · have hct : evalExpr (.ult (.vgrowLen "t") (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b false) := by
        simp [hmaxc, h2]
      have hm : evalExpr (.tif (.ult (.vgrowLen "t") (.var "n"))
            (.var "n") (.vgrowLen "t"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.u64 (BitVec.ofNat 64 len)) :=
        (evalExpr_tif_false _ _ _ _ hct).trans hlen
      have hnew : evalExpr stdVecNewLenExpr
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.u64 (BitVec.ofNat 64 len + BitVec.ofNat 64 len)) := by
        simp only [stdVecNewLenExpr]
        exact evalExpr_uadd_u64 _ _ _ _ _ hlen hm
      have hc2raw : evalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b ((BitVec.ofNat 64 len + BitVec.ofNat 64 len).ult
            (BitVec.ofNat 64 len))) :=
        evalExpr_ult_u64 _ _ _ _ _ hnew hlen
      by_cases h3 : (BitVec.ofNat 64 len + BitVec.ofNat 64 len).ult
          (BitVec.ofNat 64 len)
      · have hc2 : evalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b true) := by
          simp [hc2raw, h3]
        have hfwd : stdVecCheckLenFwd len n =
            .ok (.u64 stdVecMaxDiffBV) := by
          simp [stdVecCheckLenFwd, h1, h2, h3]
        have hstmt : evalStmtFuel F stdVecCheckLenFunc.body
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
              .returned (.u64 stdVecMaxDiffBV)) := by
          rw [hbody, evalStmtFuel_if_false F _ _ _ _ hc,
            evalStmtFuel_if_true F _ _ _ _ hc2]
          exact evalStmtFuel_return F _ _ _ hmaxlit
        simp [evalFuncFuel, hbind, hstmt, hfwd]
      · have hc2 : evalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b false) := by
          simp [hc2raw, h3]
        have hc3raw : evalExpr
            (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b (stdVecMaxDiffBV.ult
              (BitVec.ofNat 64 len + BitVec.ofNat 64 len))) :=
          evalExpr_ult_u64lit _ _ _ _ hnew
        by_cases h4 : stdVecMaxDiffBV.ult
            (BitVec.ofNat 64 len + BitVec.ofNat 64 len)
        · have hc3 : evalExpr
              (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
              [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
              .ok (.b true) := by
            simp [hc3raw, h4]
          have hfwd : stdVecCheckLenFwd len n =
              .ok (.u64 stdVecMaxDiffBV) := by
            simp [stdVecCheckLenFwd, h1, h2, h3, h4]
          have hstmt : evalStmtFuel F stdVecCheckLenFunc.body
              [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
              .ok ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
                .returned (.u64 stdVecMaxDiffBV)) := by
            rw [hbody, evalStmtFuel_if_false F _ _ _ _ hc,
              evalStmtFuel_if_false F _ _ _ _ hc2,
              evalStmtFuel_if_true F _ _ _ _ hc3]
            exact evalStmtFuel_return F _ _ _ hmaxlit
          simp [evalFuncFuel, hbind, hstmt, hfwd]
        · have hc3 : evalExpr
              (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
              [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
              .ok (.b false) := by
            simp [hc3raw, h4]
          have hfwd : stdVecCheckLenFwd len n =
              .ok (.u64 (BitVec.ofNat 64 len +
                BitVec.ofNat 64 len)) := by
            simp [stdVecCheckLenFwd, h1, h2, h3, h4]
          have hstmt : evalStmtFuel F stdVecCheckLenFunc.body
              [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
              .ok ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
                .returned (.u64 (BitVec.ofNat 64 len +
                  BitVec.ofNat 64 len))) := by
            rw [hbody, evalStmtFuel_if_false F _ _ _ _ hc,
              evalStmtFuel_if_false F _ _ _ _ hc2,
              evalStmtFuel_if_false F _ _ _ _ hc3]
            exact evalStmtFuel_return F _ _ _ hnew
          simp [evalFuncFuel, hbind, hstmt, hfwd]
