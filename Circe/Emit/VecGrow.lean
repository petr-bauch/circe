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

/-! ## N4d-iv-b1: iterators (`begin` / `end` / `back` / identities / minus) -/

/-- Mangled names fused into the iterator leaves. `begin` loads
    `_M_start` (erased offset `0`); `end` loads `_M_finish` (erased
    offset `len`); `back` fuses the `end` / `miEl` / `deref` chain
    (`len - 1` wrapping; empty is UB — the garbage offset goes `OOB`
    at first use). -/
def stdVecBeginName : String := "_ZNSt6vectorIiSaIiEE5beginEv"
def stdVecEndName : String := "_ZNSt6vectorIiSaIiEE3endEv"
def stdVecBackName : String := "_ZNSt6vectorIiSaIiEE4backEv"

/-- Mangled names fused into the iterator identity: the iterator-C2
    store, `__niter_base`, `base` (the address-of-field collapses to
    the value), and `operator*` (the pointer is the offset). -/
def stdVecIterCtorName : String :=
  "_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1_"
def stdVecNIterBaseName : String := "_ZSt12__niter_baseIPiET_S1_"
def stdVecIterBaseName : String :=
  "_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEE4baseEv"
def stdVecIterDerefName : String :=
  "_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEdeEv"

/-- Mangled names fused into iterator minus: `miEl` (`cir.minus` +
    `ptr_stride` fuse to wrapping `usub` over erased element
    indices; the `s64` step arrives as the same bits in a `u64`)
    and `mi` (the double `base` + `ptr_diff` fuse to bit-exact
    `s64diff`). -/
def stdVecMinusElName : String :=
  "_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl"
def stdVecMinusName : String :=
  "_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB_"

/-- Canonical CoreIR for `begin`: the `_M_start` load + iterator-C2
    call fuse to the `0` offset. -/
def stdVecBeginFunc : Func :=
  ⟨stdVecBeginName,
   [{ name := "t", ty := .vecBlock, role := .owned }],
   .u 64,
   .return_ (.lit (.u64 (BitVec.ofNat 64 0)))⟩

/-- Value-level forward for `begin`. -/
def stdVecBeginFwd : Result Value :=
  .ok (.u64 (BitVec.ofNat 64 0))

/-- `emit_correct` for `begin` (any fuel). -/
theorem evalFuncFuel_stdVecBegin (F : Nat) (b : Vec32) (len cap : Nat) :
    evalFuncFuel F stdVecBeginFunc [.stdVecOwned b len cap] =
      stdVecBeginFwd := by
  have hbind : bindArgs stdVecBeginFunc.args [.stdVecOwned b len cap] =
      some [("t", .stdVecOwned b len cap)] := rfl
  have hbody : stdVecBeginFunc.body =
      .return_ (.lit (.u64 (BitVec.ofNat 64 0))) := rfl
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, stdVecBeginFwd]

/-- Canonical CoreIR for `end`: the `_M_finish` load + iterator-C2
    call fuse to the `len` offset. -/
def stdVecEndFunc : Func :=
  ⟨stdVecEndName,
   [{ name := "t", ty := .vecBlock, role := .owned }],
   .u 64,
   .return_ (.vgrowLen "t")⟩

/-- Value-level forward for `end`. -/
def stdVecEndFwd (len : Nat) : Result Value :=
  .ok (.u64 (BitVec.ofNat 64 len))

/-- Env fact for the `end` shape. -/
theorem envLookup_stdVecEnd_t (b : Vec32) (len cap : Nat) :
    envLookup [("t", .stdVecOwned b len cap)] "t" =
      some (.stdVecOwned b len cap) := by
  simp [envLookup]

/-- `emit_correct` for `end` (any fuel). -/
theorem evalFuncFuel_stdVecEnd (F : Nat) (b : Vec32) (len cap : Nat) :
    evalFuncFuel F stdVecEndFunc [.stdVecOwned b len cap] =
      stdVecEndFwd len := by
  have hbind : bindArgs stdVecEndFunc.args [.stdVecOwned b len cap] =
      some [("t", .stdVecOwned b len cap)] := rfl
  have hbody : stdVecEndFunc.body = .return_ (.vgrowLen "t") := rfl
  have ht := envLookup_stdVecEnd_t b len cap
  have hlen : evalExpr (.vgrowLen "t") [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, hlen, stdVecEndFwd]

/-- Canonical CoreIR for `back`: the `end` / `miEl` / `deref` chain
    fuses to `len - 1` (wrapping `usub`; empty is UB). -/
def stdVecBackFunc : Func :=
  ⟨stdVecBackName,
   [{ name := "t", ty := .vecBlock, role := .owned }],
   .u 64,
   .return_ (.usub (.vgrowLen "t") (.lit (.u64 (BitVec.ofNat 64 1))))⟩

/-- Value-level forward for `back`. -/
def stdVecBackFwd (len : Nat) : Result Value :=
  .ok (.u64 (BitVec.ofNat 64 len - 1))

/-- Env fact for the `back` shape. -/
theorem envLookup_stdVecBack_t (b : Vec32) (len cap : Nat) :
    envLookup [("t", .stdVecOwned b len cap)] "t" =
      some (.stdVecOwned b len cap) := by
  simp [envLookup]

/-- `emit_correct` for `back` (any fuel). -/
theorem evalFuncFuel_stdVecBack (F : Nat) (b : Vec32) (len cap : Nat) :
    evalFuncFuel F stdVecBackFunc [.stdVecOwned b len cap] =
      stdVecBackFwd len := by
  have hbind : bindArgs stdVecBackFunc.args [.stdVecOwned b len cap] =
      some [("t", .stdVecOwned b len cap)] := rfl
  have hbody : stdVecBackFunc.body =
      .return_ (.usub (.vgrowLen "t") (.lit (.u64 (BitVec.ofNat 64 1)))) :=
    rfl
  have ht := envLookup_stdVecBack_t b len cap
  have hlen : evalExpr (.vgrowLen "t") [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht
  have hback : evalExpr
      (.usub (.vgrowLen "t") (.lit (.u64 (BitVec.ofNat 64 1))))
      [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 len - 1)) :=
    evalExpr_u64_usub _ _ _ _ hlen
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, hback, stdVecBackFwd]

/-- Canonical CoreIR for the iterator identities: the stored pointer
    is the offset. -/
def stdVecIterIdFunc : Func :=
  ⟨stdVecIterCtorName,
   [{ name := "p", ty := .u 64, role := .owned }],
   .u 64,
   .return_ (.var "p")⟩

/-- Value-level forward for the iterator identities. -/
def stdVecIterIdFwd (x : BitVec 64) : Result Value := .ok (.u64 x)

/-- Env fact for the iterator-identity shape. -/
theorem envLookup_stdVecIterId_p (x : BitVec 64) :
    envLookup [("p", .u64 x)] "p" = some (.u64 x) := by
  simp [envLookup]

/-- `emit_correct` for the iterator identities (any fuel). -/
theorem evalFuncFuel_stdVecIterId (F : Nat) (x : BitVec 64) :
    evalFuncFuel F stdVecIterIdFunc [.u64 x] = stdVecIterIdFwd x := by
  have hbind : bindArgs stdVecIterIdFunc.args [.u64 x] =
      some [("p", .u64 x)] := rfl
  have hbody : stdVecIterIdFunc.body = .return_ (.var "p") := rfl
  have hp := envLookup_stdVecIterId_p x
  have hvar : evalExpr (.var "p") [("p", .u64 x)] = .ok (.u64 x) := by
    simp [evalExpr, hp]
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, hvar, stdVecIterIdFwd]

/-- Canonical CoreIR for `miEl`: `cir.minus` + `ptr_stride` fuse to
    wrapping `usub` (the `s64` step arrives as the same bits). -/
def stdVecMinusElFunc : Func :=
  ⟨stdVecMinusElName,
   [{ name := "it", ty := .u 64, role := .owned },
    { name := "n", ty := .u 64, role := .owned }],
   .u 64,
   .return_ (.usub (.var "it") (.var "n"))⟩

/-- Value-level forward for `miEl`. -/
def stdVecMinusElFwd (it n : BitVec 64) : Result Value :=
  .ok (.u64 (it - n))

/-- Env facts for the `miEl` shape. -/
theorem envLookup_stdVecMinusEl_it (it n : BitVec 64) :
    envLookup [("it", .u64 it), ("n", .u64 n)] "it" =
      some (.u64 it) := by
  simp [envLookup]

theorem envLookup_stdVecMinusEl_n (it n : BitVec 64) :
    envLookup [("it", .u64 it), ("n", .u64 n)] "n" =
      some (.u64 n) := by
  simp [envLookup, show ("n" : String) ≠ "it" by decide]

/-- `emit_correct` for `miEl` (any fuel). -/
theorem evalFuncFuel_stdVecMinusEl (F : Nat) (it n : BitVec 64) :
    evalFuncFuel F stdVecMinusElFunc [.u64 it, .u64 n] =
      stdVecMinusElFwd it n := by
  have hbind : bindArgs stdVecMinusElFunc.args [.u64 it, .u64 n] =
      some [("it", .u64 it), ("n", .u64 n)] := rfl
  have hbody : stdVecMinusElFunc.body =
      .return_ (.usub (.var "it") (.var "n")) := rfl
  have hit := envLookup_stdVecMinusEl_it it n
  have hn := envLookup_stdVecMinusEl_n it n
  have hvit : evalExpr (.var "it") [("it", .u64 it), ("n", .u64 n)] =
      .ok (.u64 it) := by
    simp [evalExpr, hit]
  have hvn : evalExpr (.var "n") [("it", .u64 it), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hsub : evalExpr (.usub (.var "it") (.var "n"))
      [("it", .u64 it), ("n", .u64 n)] = .ok (.u64 (it - n)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hvit hvn
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, hsub, stdVecMinusElFwd]

/-- Canonical CoreIR for `mi`: the double `base` + `ptr_diff` fuse
    to bit-exact `s64diff`. -/
def stdVecMinusFunc : Func :=
  ⟨stdVecMinusName,
   [{ name := "a", ty := .u 64, role := .owned },
    { name := "b", ty := .u 64, role := .owned }],
   .i 64,
   .return_ (.s64diff (.var "a") (.var "b"))⟩

/-- Value-level forward for `mi`. -/
def stdVecMinusFwd (a b : BitVec 64) : Result Value :=
  .ok (.i64 (a - b))

/-- Env facts for the `mi` shape. -/
theorem envLookup_stdVecMinus_a (a b : BitVec 64) :
    envLookup [("a", .u64 a), ("b", .u64 b)] "a" =
      some (.u64 a) := by
  simp [envLookup]

theorem envLookup_stdVecMinus_b (a b : BitVec 64) :
    envLookup [("a", .u64 a), ("b", .u64 b)] "b" =
      some (.u64 b) := by
  simp [envLookup, show ("b" : String) ≠ "a" by decide]

/-- `emit_correct` for `mi` (any fuel). -/
theorem evalFuncFuel_stdVecMinus (F : Nat) (a b : BitVec 64) :
    evalFuncFuel F stdVecMinusFunc [.u64 a, .u64 b] =
      stdVecMinusFwd a b := by
  have hbind : bindArgs stdVecMinusFunc.args [.u64 a, .u64 b] =
      some [("a", .u64 a), ("b", .u64 b)] := rfl
  have hbody : stdVecMinusFunc.body =
      .return_ (.s64diff (.var "a") (.var "b")) := rfl
  have ha := envLookup_stdVecMinus_a a b
  have hb := envLookup_stdVecMinus_b a b
  have hva : evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 a) := by
    simp [evalExpr, ha]
  have hvb : evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 b) := by
    simp [evalExpr, hb]
  have hdiff : evalExpr (.s64diff (.var "a") (.var "b"))
      [("a", .u64 a), ("b", .u64 b)] = .ok (.i64 (a - b)) :=
    evalExpr_s64diff_u64u64 _ _ _ _ _ hva hvb
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, hdiff, stdVecMinusFwd]

/-! ## N4d-iv-b1: `_M_allocate` (fresh storage, `n == 0` kept) -/

/-- Mangled names fused into allocate: `_M_allocate` keeps the `n ==
    0` ternary (both branches build a `len`-`0` triple — null
    coincides with empty); `traits::allocate` / `new_allocator ::
    allocate` fuse the over-max throw pair to `fail`, drop the dead
    `4 > 16` aligned-new skeleton, and model operator `new` as fresh
    storage (`vgrowNew`, like `boxNew`). -/
def stdVecAllocateName : String :=
  "_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm"
def stdVecTraitsAllocName : String :=
  "_ZNSt16allocator_traitsISaIiEE8allocateERS0_m"
def stdVecNewAllocName : String :=
  "_ZN9__gnu_cxx13new_allocatorIiE8allocateEmPKv"

/-- Canonical CoreIR for `_M_allocate`: the `n != 0` test keeps CIR
    branch polarity (true allocates), the over-max throw pair fuses
    to `fail`. -/
def stdVecAllocFunc : Func :=
  ⟨stdVecAllocateName,
   [{ name := "n", ty := .u 64, role := .owned }],
   .vecBlock,
   .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
     (.if_ (.ult (.lit (.u64 stdVecAllocMaxBV)) (.var "n"))
       .fail
       (.return_ (.vgrowNew (.var "n"))))
     (.return_ (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0)))))⟩

/-- Value-level forward for `_M_allocate` (mirrors the Func at
    `BitVec`-bool level, so no `toNat` bridges are needed). -/
def stdVecAllocFwd (n : BitVec 64) : Result Value :=
  if (BitVec.ofNat 64 0).ult n then
    if stdVecAllocMaxBV.ult n then .error .AssertFail
    else .ok (.stdVecOwned ⟨List.replicate n.toNat 0, false⟩ 0 n.toNat)
  else .ok (.stdVecOwned
    ⟨List.replicate (BitVec.ofNat 64 0).toNat 0, false⟩ 0
    (BitVec.ofNat 64 0).toNat)

/-- Env fact for the `_M_allocate` shape. -/
theorem envLookup_stdVecAlloc_n (n : BitVec 64) :
    envLookup [("n", .u64 n)] "n" = some (.u64 n) := by
  simp [envLookup]

/-- `emit_correct` for `_M_allocate` (any fuel; compositional closes —
    the 2-deep `if_` chain would risk the `check_len` kernel blowup). -/
theorem evalFuncFuel_stdVecAlloc (F : Nat) (n : BitVec 64) :
    evalFuncFuel F stdVecAllocFunc [.u64 n] = stdVecAllocFwd n := by
  have hbind : bindArgs stdVecAllocFunc.args [.u64 n] =
      some [("n", .u64 n)] := rfl
  have hbody : stdVecAllocFunc.body =
      .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        (.if_ (.ult (.lit (.u64 stdVecAllocMaxBV)) (.var "n"))
          .fail
          (.return_ (.vgrowNew (.var "n"))))
        (.return_ (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0))))) := rfl
  have hn := envLookup_stdVecAlloc_n n
  have hnv : evalExpr (.var "n") [("n", .u64 n)] = .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hzc : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
      [("n", .u64 n)] =
      .ok (.b ((BitVec.ofNat 64 0).ult n)) :=
    evalExpr_ult_u64lit _ _ _ _ hnv
  have hom : evalExpr
      (.ult (.lit (.u64 stdVecAllocMaxBV)) (.var "n"))
      [("n", .u64 n)] =
      .ok (.b (stdVecAllocMaxBV.ult n)) :=
    evalExpr_ult_u64lit _ _ _ _ hnv
  by_cases hz : (BitVec.ofNat 64 0).ult n
  · have hc : evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        [("n", .u64 n)] = .ok (.b true) := by
      simp [hzc, hz]
    by_cases hm : stdVecAllocMaxBV.ult n
    · have hcm : evalExpr
          (.ult (.lit (.u64 stdVecAllocMaxBV)) (.var "n"))
          [("n", .u64 n)] = .ok (.b true) := by
        simp [hom, hm]
      have hfwd : stdVecAllocFwd n = .error .AssertFail := by
        simp [stdVecAllocFwd, hz, hm]
      have hstmt : evalStmtFuel F stdVecAllocFunc.body [("n", .u64 n)] =
          .error .AssertFail := by
        rw [hbody, evalStmtFuel_if_true F _ _ _ _ hc,
          evalStmtFuel_if_true F _ _ _ _ hcm]
        exact evalStmtFuel_fail F _
      simp [evalFuncFuel, hbind, hstmt, hfwd]
    · have hcm : evalExpr
          (.ult (.lit (.u64 stdVecAllocMaxBV)) (.var "n"))
          [("n", .u64 n)] = .ok (.b false) := by
        simp [hom, hm]
      have hnew : evalExpr (.vgrowNew (.var "n")) [("n", .u64 n)] =
          .ok (.stdVecOwned ⟨List.replicate n.toNat 0, false⟩ 0
            n.toNat) :=
        evalExpr_vgrowNew_u64 _ _ _ hnv
      have hfwd : stdVecAllocFwd n =
          .ok (.stdVecOwned ⟨List.replicate n.toNat 0, false⟩ 0
            n.toNat) := by
        simp [stdVecAllocFwd, hz, hm]
      have hstmt : evalStmtFuel F stdVecAllocFunc.body [("n", .u64 n)] =
          .ok ([("n", .u64 n)],
            .returned (.stdVecOwned ⟨List.replicate n.toNat 0, false⟩
              0 n.toNat)) := by
        rw [hbody, evalStmtFuel_if_true F _ _ _ _ hc,
          evalStmtFuel_if_false F _ _ _ _ hcm]
        exact evalStmtFuel_return F _ _ _ hnew
      simp [evalFuncFuel, hbind, hstmt, hfwd]
  · have hcf : evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        [("n", .u64 n)] = .ok (.b false) := by
      simp [hzc, hz]
    have hempty : evalExpr
        (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0)))) [("n", .u64 n)] =
        .ok (.stdVecOwned
          ⟨List.replicate (BitVec.ofNat 64 0).toNat 0, false⟩ 0
          (BitVec.ofNat 64 0).toNat) :=
      evalExpr_vgrowNew_lit _ _
    have hfwd : stdVecAllocFwd n =
        .ok (.stdVecOwned
          ⟨List.replicate (BitVec.ofNat 64 0).toNat 0, false⟩ 0
          (BitVec.ofNat 64 0).toNat) := by
      simp [stdVecAllocFwd, hz]
    have hstmt : evalStmtFuel F stdVecAllocFunc.body [("n", .u64 n)] =
        .ok ([("n", .u64 n)],
          .returned (.stdVecOwned
            ⟨List.replicate (BitVec.ofNat 64 0).toNat 0, false⟩ 0
            (BitVec.ofNat 64 0).toNat)) := by
      rw [hbody, evalStmtFuel_if_false F _ _ _ _ hcf]
      exact evalStmtFuel_return F _ _ _ hempty
    simp [evalFuncFuel, hbind, hstmt, hfwd]

/-! ## N4d-iv-b1: `_M_deallocate` (guarded consume) -/

/-- Mangled names fused into deallocate: `_M_deallocate` keeps the
    `ptr_to_bool` guard as the `n == 0` test (sound by the call-site
    invariant that a null `p` always pairs with `n == 0`);
    `traits::deallocate` / `new_allocator::deallocate` are the
    unconditional consume (the dead `4 > 16` skeleton drops, operator
    `delete` consumes the token). -/
def stdVecDeallocName : String :=
  "_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim"
def stdVecTraitsDeallocName : String :=
  "_ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim"
def stdVecNewDeallocName : String :=
  "_ZN9__gnu_cxx13new_allocatorIiE10deallocateEPim"

/-- Canonical CoreIR for the unconditional consume. -/
def stdVecDeallocFunc : Func :=
  ⟨stdVecTraitsDeallocName,
   [{ name := "t", ty := .vecBlock, role := .owned }],
   .vecBlock,
   .seq (.vgrowFree "t") (.return_ (.var "t"))⟩

/-- Value-level forward for the unconditional consume. -/
def stdVecDeallocFwd (b : Vec32) (len cap : Nat) : Result Value :=
  match vecFree b with
  | .error e => .error e
  | .ok b' => .ok (.stdVecOwned b' len cap)

/-- Env fact for the deallocate shape. -/
theorem envLookup_stdVecDealloc_t (b : Vec32) (len cap : Nat) :
    envLookup [("t", .stdVecOwned b len cap)] "t" =
      some (.stdVecOwned b len cap) := by
  simp [envLookup]

/-- `emit_correct` for the unconditional consume (any fuel). -/
theorem evalFuncFuel_stdVecDealloc (F : Nat) (b : Vec32) (len cap : Nat) :
    evalFuncFuel F stdVecDeallocFunc [.stdVecOwned b len cap] =
      stdVecDeallocFwd b len cap := by
  have hbind : bindArgs stdVecDeallocFunc.args [.stdVecOwned b len cap] =
      some [("t", .stdVecOwned b len cap)] := rfl
  have hbody : stdVecDeallocFunc.body =
      .seq (.vgrowFree "t") (.return_ (.var "t")) := rfl
  have ht := envLookup_stdVecDealloc_t b len cap
  cases hfb : vecFree b with
  | error e =>
    have hfwd : stdVecDeallocFwd b len cap = .error e := by
      simp [stdVecDeallocFwd, hfb]
    have herr : evalStmtFuel F (.vgrowFree "t")
        [("t", .stdVecOwned b len cap)] = .error e :=
      evalStmtFuel_vgrowFree_err F _ _ _ _ _ _ ht hfb
    have hstmt : evalStmtFuel F stdVecDeallocFunc.body
        [("t", .stdVecOwned b len cap)] = .error e := by
      rw [hbody]
      exact evalStmtFuel_seq_err F _ _ _ _ herr
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  | ok b' =>
    have hup : envUpdate [("t", .stdVecOwned b len cap)] "t"
        (.stdVecOwned b' len cap) =
        some [("t", .stdVecOwned b' len cap)] := by
      simp [envUpdate]
    have hret : envLookup [("t", .stdVecOwned b' len cap)] "t" =
        some (.stdVecOwned b' len cap) := by
      simp [envLookup]
    have hvar : evalExpr (.var "t")
        [("t", .stdVecOwned b' len cap)] =
        .ok (.stdVecOwned b' len cap) := by
      simp [evalExpr, hret]
    have hfree : evalStmtFuel F (.vgrowFree "t")
        [("t", .stdVecOwned b len cap)] =
        .ok ([("t", .stdVecOwned b' len cap)], .fellThrough) :=
      evalStmtFuel_vgrowFree F _ _ _ _ _ _ _ ht hfb hup
    have hfwd : stdVecDeallocFwd b len cap =
        .ok (.stdVecOwned b' len cap) := by
      simp [stdVecDeallocFwd, hfb]
    have hstmt : evalStmtFuel F stdVecDeallocFunc.body
        [("t", .stdVecOwned b len cap)] =
        .ok ([("t", .stdVecOwned b' len cap)],
          .returned (.stdVecOwned b' len cap)) := by
      rw [hbody]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hfree).trans
        (evalStmtFuel_return F _ _ _ hvar)
    simp [evalFuncFuel, hbind, hstmt, hfwd]

/-- Canonical CoreIR for `_M_deallocate`: the `ptr_to_bool` guard as
    the `n == 0` test around the unconditional consume. -/
def stdVecDeallocGuardFunc : Func :=
  ⟨stdVecDeallocName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "n", ty := .u 64, role := .owned }],
   .vecBlock,
   .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
     (.seq (.vgrowFree "t") (.return_ (.var "t")))
     (.return_ (.var "t"))⟩

/-- Value-level forward for `_M_deallocate`. -/
def stdVecDeallocGuardFwd (b : Vec32) (len cap : Nat)
    (n : BitVec 64) : Result Value :=
  if (BitVec.ofNat 64 0).ult n then
    match vecFree b with
    | .error e => .error e
    | .ok b' => .ok (.stdVecOwned b' len cap)
  else .ok (.stdVecOwned b len cap)

/-- Env facts for the `_M_deallocate` shape. -/
theorem envLookup_stdVecDeallocGuard_t (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    envLookup [("t", .stdVecOwned b len cap), ("n", .u64 n)] "t" =
      some (.stdVecOwned b len cap) := by
  simp [envLookup]

theorem envLookup_stdVecDeallocGuard_n (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    envLookup [("t", .stdVecOwned b len cap), ("n", .u64 n)] "n" =
      some (.u64 n) := by
  simp [envLookup, show ("n" : String) ≠ "t" by decide]

/-- `emit_correct` for `_M_deallocate` (any fuel). -/
theorem evalFuncFuel_stdVecDeallocGuard (F : Nat) (b : Vec32)
    (len cap : Nat) (n : BitVec 64) :
    evalFuncFuel F stdVecDeallocGuardFunc
      [.stdVecOwned b len cap, .u64 n] =
      stdVecDeallocGuardFwd b len cap n := by
  have hbind : bindArgs stdVecDeallocGuardFunc.args
      [.stdVecOwned b len cap, .u64 n] =
      some [("t", .stdVecOwned b len cap), ("n", .u64 n)] := rfl
  have hbody : stdVecDeallocGuardFunc.body =
      .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        (.seq (.vgrowFree "t") (.return_ (.var "t")))
        (.return_ (.var "t")) := rfl
  have ht := envLookup_stdVecDeallocGuard_t b len cap n
  have hn := envLookup_stdVecDeallocGuard_n b len cap n
  have hnv : evalExpr (.var "n")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hzc : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.b ((BitVec.ofNat 64 0).ult n)) :=
    evalExpr_ult_u64lit _ _ _ _ hnv
  by_cases hz : (BitVec.ofNat 64 0).ult n
  · have hc : evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .ok (.b true) := by
      simp [hzc, hz]
    cases hfb : vecFree b with
    | error e =>
      have hfwd : stdVecDeallocGuardFwd b len cap n = .error e := by
        simp [stdVecDeallocGuardFwd, hz, hfb]
      have herr : evalStmtFuel F (.vgrowFree "t")
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .error e :=
        evalStmtFuel_vgrowFree_err F _ _ _ _ _ _ ht hfb
      have hstmt : evalStmtFuel F stdVecDeallocGuardFunc.body
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .error e := by
        rw [hbody, evalStmtFuel_if_true F _ _ _ _ hc]
        exact evalStmtFuel_seq_err F _ _ _ _ herr
      simp [evalFuncFuel, hbind, hstmt, hfwd]
    | ok b' =>
      have hup : envUpdate [("t", .stdVecOwned b len cap),
          ("n", .u64 n)] "t" (.stdVecOwned b' len cap) =
          some [("t", .stdVecOwned b' len cap), ("n", .u64 n)] := by
        simp [envUpdate]
      have hret : envLookup [("t", .stdVecOwned b' len cap),
          ("n", .u64 n)] "t" =
          some (.stdVecOwned b' len cap) := by
        simp [envLookup]
      have hvar : evalExpr (.var "t")
          [("t", .stdVecOwned b' len cap), ("n", .u64 n)] =
          .ok (.stdVecOwned b' len cap) := by
        simp [evalExpr, hret]
      have hfree : evalStmtFuel F (.vgrowFree "t")
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok ([("t", .stdVecOwned b' len cap), ("n", .u64 n)],
            .fellThrough) :=
        evalStmtFuel_vgrowFree F _ _ _ _ _ _ _ ht hfb hup
      have hfwd : stdVecDeallocGuardFwd b len cap n =
          .ok (.stdVecOwned b' len cap) := by
        simp [stdVecDeallocGuardFwd, hz, hfb]
      have hstmt : evalStmtFuel F stdVecDeallocGuardFunc.body
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok ([("t", .stdVecOwned b' len cap), ("n", .u64 n)],
            .returned (.stdVecOwned b' len cap)) := by
        rw [hbody, evalStmtFuel_if_true F _ _ _ _ hc]
        exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hfree).trans
          (evalStmtFuel_return F _ _ _ hvar)
      simp [evalFuncFuel, hbind, hstmt, hfwd]
  · have hcf : evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .ok (.b false) := by
      simp [hzc, hz]
    have hvar0 : evalExpr (.var "t")
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .ok (.stdVecOwned b len cap) := by
      simp [evalExpr, ht]
    have hfwd : stdVecDeallocGuardFwd b len cap n =
        .ok (.stdVecOwned b len cap) := by
      simp [stdVecDeallocGuardFwd, hz]
    have hstmt : evalStmtFuel F stdVecDeallocGuardFunc.body
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .ok ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
          .returned (.stdVecOwned b len cap)) := by
      rw [hbody, evalStmtFuel_if_false F _ _ _ _ hcf]
      exact evalStmtFuel_return F _ _ _ hvar0
    simp [evalFuncFuel, hbind, hstmt, hfwd]

/-! ## N4d-iv-b1: `construct` (placement store, triple-threaded) -/

/-- Mangled names fused into construct: `traits::construct` is the
    single delegation; `new_allocator::construct` is the placement
    store with the `&&`-arg double load fused. `C++` `void` is
    functionalized as triple threading (returns the updated triple)
    so b2 can compose. -/
def stdVecTraitsConstructName : String :=
  "_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0_"
def stdVecNewConstructName : String :=
  "_ZN9__gnu_cxx13new_allocatorIiE9constructIiJiEEEvPT_DpOT0_"

/-- Canonical CoreIR for `construct`: store the `i32` word at the
    `u64` offset, return the updated triple. -/
def stdVecConstructFunc : Func :=
  ⟨stdVecTraitsConstructName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "p", ty := .u 64, role := .owned },
    { name := "v", ty := .i 32, role := .owned }],
   .vecBlock,
   .seq (.vgrowSet "t" (.var "p") (.var "v"))
     (.return_ (.var "t"))⟩

/-- Value-level forward for `construct` (use-after-free is
    `AssertFail`, offset at or past the storage words is `OOB`). -/
def stdVecConstructFwd (b : Vec32) (len cap : Nat) (p : BitVec 64)
    (x : BitVec 32) : Result Value :=
  match vecSet b p.toNat x with
  | .error e => .error e
  | .ok b' => .ok (.stdVecOwned b' len cap)

/-- Env facts for the `construct` shape. -/
theorem envLookup_stdVecConstruct_t (b : Vec32) (len cap : Nat)
    (p : BitVec 64) (x : BitVec 32) :
    envLookup [("t", .stdVecOwned b len cap), ("p", .u64 p),
      ("v", .i32 x)] "t" =
      some (.stdVecOwned b len cap) := by
  simp [envLookup]

theorem envLookup_stdVecConstruct_p (b : Vec32) (len cap : Nat)
    (p : BitVec 64) (x : BitVec 32) :
    envLookup [("t", .stdVecOwned b len cap), ("p", .u64 p),
      ("v", .i32 x)] "p" =
      some (.u64 p) := by
  simp [envLookup, show ("p" : String) ≠ "t" by decide]

theorem envLookup_stdVecConstruct_v (b : Vec32) (len cap : Nat)
    (p : BitVec 64) (x : BitVec 32) :
    envLookup [("t", .stdVecOwned b len cap), ("p", .u64 p),
      ("v", .i32 x)] "v" =
      some (.i32 x) := by
  simp [envLookup, show ("v" : String) ≠ "t" by decide,
    show ("v" : String) ≠ "p" by decide]

/-- `emit_correct` for `construct` (any fuel). -/
theorem evalFuncFuel_stdVecConstruct (F : Nat) (b : Vec32)
    (len cap : Nat) (p : BitVec 64) (x : BitVec 32) :
    evalFuncFuel F stdVecConstructFunc
      [.stdVecOwned b len cap, .u64 p, .i32 x] =
      stdVecConstructFwd b len cap p x := by
  have hbind : bindArgs stdVecConstructFunc.args
      [.stdVecOwned b len cap, .u64 p, .i32 x] =
      some [("t", .stdVecOwned b len cap), ("p", .u64 p),
        ("v", .i32 x)] := rfl
  have hbody : stdVecConstructFunc.body =
      .seq (.vgrowSet "t" (.var "p") (.var "v"))
        (.return_ (.var "t")) := rfl
  have ht := envLookup_stdVecConstruct_t b len cap p x
  have hp := envLookup_stdVecConstruct_p b len cap p x
  have hv := envLookup_stdVecConstruct_v b len cap p x
  have hpv : evalExpr (.var "p")
      [("t", .stdVecOwned b len cap), ("p", .u64 p), ("v", .i32 x)] =
      .ok (.u64 p) := by
    simp [evalExpr, hp]
  have hvv : evalExpr (.var "v")
      [("t", .stdVecOwned b len cap), ("p", .u64 p), ("v", .i32 x)] =
      .ok (.i32 x) := by
    simp [evalExpr, hv]
  cases hset : vecSet b p.toNat x with
  | error e =>
    have hfwd : stdVecConstructFwd b len cap p x = .error e := by
      simp [stdVecConstructFwd, hset]
    have hse : evalStmtFuel F (.vgrowSet "t" (.var "p") (.var "v"))
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] = .error e :=
      evalStmtFuel_vgrowSet_err F _ _ _ _ _ _ _ _ _ _ hpv hvv ht hset
    have hstmt : evalStmtFuel F stdVecConstructFunc.body
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] = .error e := by
      rw [hbody]
      exact evalStmtFuel_seq_err F _ _ _ _ hse
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  | ok b' =>
    have hup : envUpdate [("t", .stdVecOwned b len cap), ("p", .u64 p),
        ("v", .i32 x)] "t" (.stdVecOwned b' len cap) =
        some [("t", .stdVecOwned b' len cap), ("p", .u64 p),
          ("v", .i32 x)] := by
      simp [envUpdate]
    have hret : envLookup [("t", .stdVecOwned b' len cap),
        ("p", .u64 p), ("v", .i32 x)] "t" =
        some (.stdVecOwned b' len cap) := by
      simp [envLookup]
    have hvar : evalExpr (.var "t")
        [("t", .stdVecOwned b' len cap), ("p", .u64 p),
          ("v", .i32 x)] =
        .ok (.stdVecOwned b' len cap) := by
      simp [evalExpr, hret]
    have hs : evalStmtFuel F (.vgrowSet "t" (.var "p") (.var "v"))
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] =
        .ok ([("t", .stdVecOwned b' len cap), ("p", .u64 p),
          ("v", .i32 x)], .fellThrough) :=
      evalStmtFuel_vgrowSet F _ _ _ _ _ _ _ _ _ _ _ hpv hvv ht hset
        hup
    have hfwd : stdVecConstructFwd b len cap p x =
        .ok (.stdVecOwned b' len cap) := by
      simp [stdVecConstructFwd, hset]
    have hstmt : evalStmtFuel F stdVecConstructFunc.body
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] =
        .ok ([("t", .stdVecOwned b' len cap), ("p", .u64 p),
          ("v", .i32 x)],
          .returned (.stdVecOwned b' len cap)) := by
      rw [hbody]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hs).trans
        (evalStmtFuel_return F _ _ _ hvar)
    simp [evalFuncFuel, hbind, hstmt, hfwd]

/-! ## N4d-iv-b1: relocate (`memmove` fused to the copy loop) -/

/-- Mangled names fused into relocate: `_S_relocate` /
    `_S_do_relocate` (the `integral_constant` tag drops) /
    `__relocate_a` (the `__niter_base` triple fuses) /
    `__relocate_a_1` (the `count > 0` guard is subsumed by the
    `while_` trip count, `memmove` unrolls to the copy loop; the
    `result + count` pointer return is dropped — b2 recomputes the
    offset from `result + (last - first)`). -/
def stdVecRelocName : String :=
  "_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0_"
def stdVecDoRelocName : String :=
  "_ZNSt6vectorIiSaIiEE14_S_do_relocateEPiS2_S2_RS0_St17integral_constantIbLb1EE"
def stdVecRelocAName : String :=
  "_ZSt12__relocate_aIPiS0_SaIiEET0_T_S3_S2_RT1_"
def stdVecRelocA1Name : String :=
  "_ZSt14__relocate_a_1IiiENSt9enable_ifIXsr3std24__is_bitwise_relocatableIT_EE5valueEPS1_E4typeES2_S2_S2_RSaIT0_E"

/-- Loop body: `dst[result + k] = src[first + k]; k = k + 1`
    (read-then-write per step, so overlapping ranges copy like
    `memmove`). -/
def stdVecRelocBody : CStmt :=
  .seq (.vgrowSet "dst" (.uadd (.var "result") (.var "k"))
          (.vgrowAt "src" (.uadd (.var "first") (.var "k"))))
    (.assign "k" (.uadd (.var "k") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- Loop: `while (k < n)` with `n = last - first`. -/
def stdVecRelocWhile : CStmt :=
  .while_ (.ult (.var "k") (.var "n")) stdVecRelocBody

/-- Canonical CoreIR for relocate: the counter / trip-count lets
    plus the call-free copy loop, returning the updated destination
    triple (the source triple is unchanged and dropped). -/
def stdVecRelocFunc : Func :=
  ⟨stdVecRelocName,
   [{ name := "src", ty := .vecBlock, role := .owned },
    { name := "dst", ty := .vecBlock, role := .owned },
    { name := "first", ty := .u 64, role := .owned },
    { name := "last", ty := .u 64, role := .owned },
    { name := "result", ty := .u 64, role := .owned }],
   .vecBlock,
   .seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
   (.seq stdVecRelocWhile
     (.return_ (.var "dst"))))⟩

/-- Value-level forward for relocate: the `memmove`-fused bulk copy
    (`stdVecBlitFold`) into the destination buffer, lengths kept. -/
def stdVecRelocFwd (bS : Vec32) (lenS _capS : Nat) (bD : Vec32)
    (lenD capD : Nat) (first last result : BitVec 64) : Result Value :=
  match stdVecBlitFold bS.val lenS bS.freed bD result.toNat
      first.toNat (last.toNat - first.toNat) with
  | .error e => .error e
  | .ok bD' => .ok (.stdVecOwned bD' lenD capD)

/-- Loop environments: `u64` trip count `n`, counter `k`, source /
    destination triples, and the three offsets. -/
def mkStdVecRelocEnv (bS : Vec32) (lenS capS : Nat) (_bD : Vec32)
    (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) : Env :=
  [("n", .u64 n), ("k", .u64 (BitVec.ofNat 64 k)),
   ("src", .stdVecOwned bS lenS capS),
   ("dst", .stdVecOwned dst lenD capD),
   ("first", .u64 first), ("last", .u64 last),
   ("result", .u64 result)]

theorem mkStdVecRelocEnv_n (bS : Vec32) (lenS capS : Nat) (bD : Vec32)
    (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) :
    envLookup (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
      result k n dst) "n" = some (.u64 n) := by
  simp [mkStdVecRelocEnv, envLookup]

theorem mkStdVecRelocEnv_k (bS : Vec32) (lenS capS : Nat) (bD : Vec32)
    (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) :
    envLookup (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
      result k n dst) "k" = some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkStdVecRelocEnv, envLookup,
    show ("k" : String) ≠ "n" by decide]

theorem mkStdVecRelocEnv_src (bS : Vec32) (lenS capS : Nat) (bD : Vec32)
    (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) :
    envLookup (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
      result k n dst) "src" = some (.stdVecOwned bS lenS capS) := by
  simp [mkStdVecRelocEnv, envLookup,
    show ("src" : String) ≠ "n" by decide,
    show ("src" : String) ≠ "k" by decide]

theorem mkStdVecRelocEnv_dst (bS : Vec32) (lenS capS : Nat) (bD : Vec32)
    (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) :
    envLookup (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
      result k n dst) "dst" = some (.stdVecOwned dst lenD capD) := by
  simp [mkStdVecRelocEnv, envLookup,
    show ("dst" : String) ≠ "n" by decide,
    show ("dst" : String) ≠ "k" by decide,
    show ("dst" : String) ≠ "src" by decide]

theorem mkStdVecRelocEnv_first (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) :
    envLookup (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
      result k n dst) "first" = some (.u64 first) := by
  simp [mkStdVecRelocEnv, envLookup,
    show ("first" : String) ≠ "n" by decide,
    show ("first" : String) ≠ "k" by decide,
    show ("first" : String) ≠ "src" by decide,
    show ("first" : String) ≠ "dst" by decide]

theorem mkStdVecRelocEnv_last (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) :
    envLookup (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
      result k n dst) "last" = some (.u64 last) := by
  simp [mkStdVecRelocEnv, envLookup,
    show ("last" : String) ≠ "n" by decide,
    show ("last" : String) ≠ "k" by decide,
    show ("last" : String) ≠ "src" by decide,
    show ("last" : String) ≠ "dst" by decide,
    show ("last" : String) ≠ "first" by decide]

theorem mkStdVecRelocEnv_result (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) :
    envLookup (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
      result k n dst) "result" = some (.u64 result) := by
  simp [mkStdVecRelocEnv, envLookup,
    show ("result" : String) ≠ "n" by decide,
    show ("result" : String) ≠ "k" by decide,
    show ("result" : String) ≠ "src" by decide,
    show ("result" : String) ≠ "dst" by decide,
    show ("result" : String) ≠ "first" by decide,
    show ("result" : String) ≠ "last" by decide]

/-- Stepping `k` stays in the env family. -/
theorem stdVecRelocEnv_update_k (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (k k' : Nat) (n : BitVec 64) (dst : Vec32) :
    envUpdate (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
      result k n dst) "k" (.u64 (BitVec.ofNat 64 k')) =
      some (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
        result k' n dst) := by
  simp [mkStdVecRelocEnv, envUpdate,
    show ("k" : String) ≠ "n" by decide]

/-- Updating `dst` stays in the env family. -/
theorem stdVecRelocEnv_update_dst (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst dst' : Vec32) :
    envUpdate (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
      result k n dst) "dst" (.stdVecOwned dst' lenD capD) =
      some (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
        result k n dst') := by
  simp [mkStdVecRelocEnv, envUpdate,
    show ("dst" : String) ≠ "n" by decide,
    show ("dst" : String) ≠ "k" by decide,
    show ("dst" : String) ≠ "src" by decide]

/-- The loop condition reads the counter against the trip count. -/
theorem stdVecRelocCond_eval (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32)
    (hk64 : k < 2 ^ 64) :
    evalExpr (.ult (.var "k") (.var "n"))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) =
      .ok (.b (decide (k < n.toNat))) := by
  have hk := mkStdVecRelocEnv_k bS lenS capS bD lenD capD first last
    result k n dst
  have hn := mkStdVecRelocEnv_n bS lenS capS bD lenD capD first last
    result k n dst
  have hkv : evalExpr (.var "k")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) =
      .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hk]
  have hnv : evalExpr (.var "n")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have h := evalExpr_ult_u64 _ _ _ _ _ hkv hnv
  rwa [ofNat64_ult k n hk64] at h

/-- Unfolding one `memmove`-fused copy step (proved once, so the loop
    proof never unfolds the well-founded fixpoint). -/
theorem stdVecBlitFold_step (src : List (BitVec 32)) (lenS : Nat)
    (freeS : Bool) (dst : Vec32) (doff soff n : Nat) :
    stdVecBlitFold src lenS freeS dst doff soff (n + 1) =
      if freeS then .error .AssertFail
      else if soff < lenS then
        match src[soff]? with
        | none => .error .OOB
        | some x =>
          match vecSet dst doff x with
          | .error e => .error e
          | .ok dst' =>
            stdVecBlitFold src lenS freeS dst' (doff + 1) (soff + 1) n
      else .error .OOB := by
  rfl

/-- Body with a live read and a live write: copy one word and step
    (any fuel). -/
theorem stdVecRelocBody_step_ok (F : Nat) (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) (x : BitVec 32)
    (bD' : Vec32)
    (hkc : k < last.toNat - first.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hliveS : bS.freed = false)
    (hSb : last.toNat ≤ bS.val.length)
    (hDb : result.toNat + (last.toNat - first.toNat) ≤ dst.val.length)
    (hlenS : last.toNat ≤ lenS)
    (hS64 : bS.val.length < 2 ^ 64) (hD64 : dst.val.length < 2 ^ 64)
    (hget : bS.val[first.toNat + k]? = some x)
    (hset : vecSet dst (result.toNat + k) x = .ok bD') :
    evalStmtFuel F stdVecRelocBody
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) =
      .ok (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        (k + 1) n bD', .fellThrough) := by
  have hk64 : k < 2 ^ 64 := by omega
  have hkok : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hsidx : (first + BitVec.ofNat 64 k).toNat = first.toNat + k := by
    rw [BitVec.toNat_add, hkok]
    exact Nat.mod_eq_of_lt (by omega)
  have hdidx : (result + BitVec.ofNat 64 k).toNat = result.toNat + k := by
    rw [BitVec.toNat_add, hkok]
    exact Nat.mod_eq_of_lt (by omega)
  have hs := mkStdVecRelocEnv_src bS lenS capS bD lenD capD first last
    result k n dst
  have hd := mkStdVecRelocEnv_dst bS lenS capS bD lenD capD first last
    result k n dst
  have hfirstL := mkStdVecRelocEnv_first bS lenS capS bD lenD capD
    first last result k n dst
  have hresultL := mkStdVecRelocEnv_result bS lenS capS bD lenD capD
    first last result k n dst
  have hkL := mkStdVecRelocEnv_k bS lenS capS bD lenD capD first last
    result k n dst
  have hkv : evalExpr (.var "k")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hkL]
  have hfirstv : evalExpr (.var "first")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 first) := by
    simp [evalExpr, hfirstL]
  have hresultv : evalExpr (.var "result")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 result) := by
    simp [evalExpr, hresultL]
  have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 (first + BitVec.ofNat 64 k)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv
  have hdidxe : evalExpr (.uadd (.var "result") (.var "k"))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 (result + BitVec.ofNat 64 k)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hresultv hkv
  have hget' : bS.val[(first + BitVec.ofNat 64 k).toNat]? = some x := by
    rw [hsidx]; exact hget
  have hlt : (first + BitVec.ofNat 64 k).toNat < lenS := by
    rw [hsidx]; omega
  have hset' : vecSet dst (result + BitVec.ofNat 64 k).toNat x =
      .ok bD' := by
    rw [hdidx]; exact hset
  have hat : evalExpr
      (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.i32 x) :=
    evalExpr_vgrowAt_some "src" _ _ bS lenS capS _ _ hs hsidxe
      hliveS hget' hlt
  have hsetF : evalStmtFuel F
      (.vgrowSet "dst" (.uadd (.var "result") (.var "k"))
        (.vgrowAt "src" (.uadd (.var "first") (.var "k"))))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) =
      .ok (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n bD', .fellThrough) :=
    evalStmtFuel_vgrowSet F _ _ _ _ _ _ _ _ _ _ _ hdidxe hat hd hset'
      (stdVecRelocEnv_update_dst bS lenS capS bD lenD capD first last
        result k n dst bD')
  have hkv' : evalExpr (.var "k")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') = .ok (.u64 (BitVec.ofNat 64 k)) := by
    have h := mkStdVecRelocEnv_k bS lenS capS bD lenD capD first last
      result k n bD'
    simp [evalExpr, h]
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') = .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hincr : evalExpr
      (.uadd (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') = .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h := evalExpr_uadd_u64 _ _ _ _ _ hkv' hlit1
    rwa [ofNat64_add_one k] at h
  have hasg := evalStmtFuel_assign F _ _ _ _ _ hincr
    (stdVecRelocEnv_update_k bS lenS capS bD lenD capD first last
      result k (k + 1) n bD')
  exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hsetF).trans hasg

/-- Body with a failed copy: the `vgrowSet` error is loud, the index
    never advances (any fuel). -/
theorem stdVecRelocBody_step_err (F : Nat) (bS : Vec32)
    (lenS capS : Nat) (bD : Vec32) (lenD capD : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) (e : Panic)
    (herr : evalStmtFuel F
      (.vgrowSet "dst" (.uadd (.var "result") (.var "k"))
        (.vgrowAt "src" (.uadd (.var "first") (.var "k"))))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .error e) :
    evalStmtFuel F stdVecRelocBody
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .error e :=
  evalStmtFuel_seq_err F _ _ _ _ herr

/-- Loop correctness: copies the remaining suffix, exits with
    `k = last - first` (fuel-generalized; the `+1` absorbs the final
    exit iteration, so the zero-fuel case is vacuous — the S3a
    `skipWhile_correct` shape, with the `stdVecBlitFold` bulk copy
    in place of the suffix fold). -/
theorem stdVecRelocWhile_correct (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (F k : Nat) (n : BitVec 64) (dst : Vec32)
    (hk : k ≤ last.toNat - first.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hn : n = last - first)
    (hliveS : bS.freed = false) (hliveD : dst.freed = false)
    (hSb : last.toNat ≤ bS.val.length)
    (hDb : result.toNat + (last.toNat - first.toNat) ≤ dst.val.length)
    (hlenS : last.toNat ≤ lenS)
    (hS64 : bS.val.length < 2 ^ 64) (hD64 : dst.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat - k + 1 ≤ F) :
    evalStmtFuel F stdVecRelocWhile
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) =
      match stdVecBlitFold bS.val lenS bS.freed dst (result.toNat + k)
          (first.toNat + k) (last.toNat - first.toNat - k) with
      | .error e => .error e
      | .ok dst' =>
        .ok (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
          result (last.toNat - first.toNat) n dst', .fellThrough) := by
  induction F generalizing k dst with
  | zero => omega
  | succ F ih =>
    have hnt : n.toNat = last.toNat - first.toNat := by
      rw [hn]; exact u64sub_toNat_exact _ _ hfirst
    have hk64 : k < 2 ^ 64 := by omega
    have hkok : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
    have hsidx : (first + BitVec.ofNat 64 k).toNat =
        first.toNat + k := by
      rw [BitVec.toNat_add, hkok]
      exact Nat.mod_eq_of_lt (by omega)
    have hdidx : (result + BitVec.ofNat 64 k).toNat =
        result.toNat + k := by
      rw [BitVec.toNat_add, hkok]
      exact Nat.mod_eq_of_lt (by omega)
    have hs := mkStdVecRelocEnv_src bS lenS capS bD lenD capD first
      last result k n dst
    have hfirstL := mkStdVecRelocEnv_first bS lenS capS bD lenD capD
      first last result k n dst
    have hresultL := mkStdVecRelocEnv_result bS lenS capS bD lenD capD
      first last result k n dst
    have hkL := mkStdVecRelocEnv_k bS lenS capS bD lenD capD first
      last result k n dst
    have hkv : evalExpr (.var "k")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 (BitVec.ofNat 64 k)) := by
      simp [evalExpr, hkL]
    have hfirstv : evalExpr (.var "first")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 first) := by
      simp [evalExpr, hfirstL]
    have hresultv : evalExpr (.var "result")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 result) := by
      simp [evalExpr, hresultL]
    have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 (first + BitVec.ofNat 64 k)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv
    have hdidxe : evalExpr (.uadd (.var "result") (.var "k"))
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 (result + BitVec.ofNat 64 k)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hresultv hkv
    by_cases hlt : k < last.toNat - first.toNat
    · have hcond : evalExpr (.ult (.var "k") (.var "n"))
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result k n dst) = .ok (.b true) := by
        have h := stdVecRelocCond_eval bS lenS capS bD lenD capD
          first last result k n dst hk64
        rw [hnt] at h
        simpa [hlt] using h
      obtain ⟨m, hm⟩ : ∃ m, last.toNat - first.toNat - k = m + 1 :=
        ⟨last.toNat - first.toNat - k - 1, by omega⟩
      have hunfold := stdVecBlitFold_step bS.val lenS bS.freed dst
        (result.toNat + k) (first.toNat + k) m
      have hsoff : first.toNat + k < lenS := by omega
      cases hget : bS.val[first.toNat + k]? with
      | none =>
        have hget' : bS.val[(first + BitVec.ofNat 64 k).toNat]? =
            none := by
          rw [hsidx]; exact hget
        have hatE : evalExpr
            (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
            (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
              result k n dst) = .error .OOB :=
          evalExpr_vgrowAt_oob_miss "src" _ _ bS lenS capS _ hs
            hsidxe hliveS hget'
        have herr : evalStmtFuel F
            (.vgrowSet "dst" (.uadd (.var "result") (.var "k"))
              (.vgrowAt "src" (.uadd (.var "first") (.var "k"))))
            (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
              result k n dst) = .error .OOB := by
          have hd := mkStdVecRelocEnv_dst bS lenS capS bD lenD capD
            first last result k n dst
          cases F <;>
            simp [evalStmtFuel, evalStmtZero, evalStmtWith, hdidxe, hatE]
        have hbody := stdVecRelocBody_step_err F bS lenS capS bD
          lenD capD first last result k n dst .OOB herr
        have hstep : evalStmtFuel (F + 1) stdVecRelocWhile
            (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
              result k n dst) = .error .OOB := by
          simp [stdVecRelocWhile, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hbody]
        rw [hstep, hm, hunfold, hliveS]
        simp [hsoff, hget]
      | some x =>
        cases hset : vecSet dst (result.toNat + k) x with
        | error e =>
          have hget' : bS.val[(first + BitVec.ofNat 64 k).toNat]? =
              some x := by
            rw [hsidx]; exact hget
          have hltlen : (first + BitVec.ofNat 64 k).toNat < lenS := by
            rw [hsidx]; omega
          have hat : evalExpr
              (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
              (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                result k n dst) = .ok (.i32 x) :=
            evalExpr_vgrowAt_some "src" _ _ bS lenS capS _ _ hs
              hsidxe hliveS hget' hltlen
          have hset' : vecSet dst (result + BitVec.ofNat 64 k).toNat
              x = .error e := by
            rw [hdidx]; exact hset
          have herr : evalStmtFuel F
              (.vgrowSet "dst" (.uadd (.var "result") (.var "k"))
                (.vgrowAt "src" (.uadd (.var "first") (.var "k"))))
              (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                result k n dst) = .error e :=
            evalStmtFuel_vgrowSet_err F _ _ _ _ _ _ _ _ _ _ hdidxe
              hat
              (mkStdVecRelocEnv_dst bS lenS capS bD lenD capD first
                last result k n dst)
              hset'
          have hbody := stdVecRelocBody_step_err F bS lenS capS bD
            lenD capD first last result k n dst e herr
          have hstep : evalStmtFuel (F + 1) stdVecRelocWhile
              (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                result k n dst) = .error e := by
            simp [stdVecRelocWhile, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcond, hbody]
          rw [hstep, hm, hunfold, hliveS]
          simp [hsoff, hget, hset]
        | ok bD' =>
          have hbody := stdVecRelocBody_step_ok F bS lenS capS bD
            lenD capD first last result k n dst x bD' hlt hfirst
            hliveS hSb hDb hlenS hS64 hD64 hget hset
          have hstep : evalStmtFuel (F + 1) stdVecRelocWhile
              (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                result k n dst) =
              evalStmtFuel F stdVecRelocWhile
                (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                  result (k + 1) n bD') := by
            simp [stdVecRelocWhile, evalStmtFuel,
              evalStmtSuccHandler, evalStmtWith, hcond, hbody]
          have hDbk : result.toNat + k < dst.val.length := by omega
          have hbD' : bD' =
              ⟨dst.val.set (result.toNat + k) x, false⟩ := by
            have h := vecSet_ok dst _ x hliveD hDbk
            rw [hset] at h
            simpa using h
          have hlenD' : bD'.val.length = dst.val.length := by
            simp [hbD', List.length_set]
          have hfreeD' : bD'.freed = false := by rw [hbD']
          have hd1 : result.toNat + k + 1 = result.toNat + (k + 1) := by
            omega
          have hs1 : first.toNat + k + 1 = first.toNat + (k + 1) := by
            omega
          have hm1 : m = last.toNat - first.toNat - (k + 1) := by
            omega
          rw [hstep, hm, hunfold, ite_eq_right (by simp [hliveS])]
          simp only [hsoff, hget, hset, ite_true]
          rw [hd1, hs1, hm1]
          exact ih (k + 1) bD' (by omega) hfreeD'
            (by rw [hlenD']; exact hDb) (by rw [hlenD']; exact hD64)
            (by omega)
    · have hkk : k = last.toNat - first.toNat := by omega
      subst hkk
      have hk64c : last.toNat - first.toNat < 2 ^ 64 := by omega
      have hcondF : evalExpr (.ult (.var "k") (.var "n"))
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result (last.toNat - first.toNat) n dst) =
          .ok (.b false) := by
        have h := stdVecRelocCond_eval bS lenS capS bD lenD capD
          first last result (last.toNat - first.toNat) n dst hk64c
        rw [hnt] at h
        have hf : decide (last.toNat - first.toNat <
            last.toNat - first.toNat) = false := by simp
        rwa [hf] at h
      have hzero : stdVecBlitFold bS.val lenS bS.freed dst
          (result.toNat + (last.toNat - first.toNat))
          (first.toNat + (last.toNat - first.toNat))
          (last.toNat - first.toNat - (last.toNat - first.toNat)) =
          .ok dst := by
        rw [Nat.sub_self]; rfl
      have hLHS : evalStmtFuel (F + 1) stdVecRelocWhile
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result (last.toNat - first.toNat) n dst) =
          .ok (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result (last.toNat - first.toNat) n dst,
            .fellThrough) := by
        simp [stdVecRelocWhile, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcondF]
      have hRHS : (match stdVecBlitFold bS.val lenS bS.freed dst
          (result.toNat + (last.toNat - first.toNat))
          (first.toNat + (last.toNat - first.toNat))
          (last.toNat - first.toNat - (last.toNat - first.toNat)) with
        | Except.error e => Except.error e
        | Except.ok dst' =>
          Except.ok (mkStdVecRelocEnv bS lenS capS bD lenD capD first
            last result (last.toNat - first.toNat) n dst',
            Outcome.fellThrough)) =
          .ok (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result (last.toNat - first.toNat) n dst,
            Outcome.fellThrough) := by
        rw [hzero]
      exact hLHS.trans hRHS.symm

/-- `emit_correct` for relocate, fuel-generalized (the S3a
    `evalFuncFuel_skip` shape; the fuel hypothesis is the slice's
    dynamic-length side condition, alongside the address bounds that
    keep every `toNat` bridge exact and the storage bounds that keep
    every copy step live). -/
theorem evalFuncFuel_stdVecReloc (F : Nat) (bS : Vec32)
    (lenS capS : Nat) (bD : Vec32) (lenD capD : Nat)
    (first last result : BitVec 64)
    (hfirst : first.toNat ≤ last.toNat)
    (hliveS : bS.freed = false) (hliveD : bD.freed = false)
    (hSb : last.toNat ≤ bS.val.length)
    (hDb : result.toNat + (last.toNat - first.toNat) ≤ bD.val.length)
    (hlenS : last.toNat ≤ lenS)
    (hS64 : bS.val.length < 2 ^ 64) (hD64 : bD.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat + 1 ≤ F) :
    evalFuncFuel F stdVecRelocFunc
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] =
      stdVecRelocFwd bS lenS capS bD lenD capD first last result := by
  have hbind : bindArgs stdVecRelocFunc.args
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] =
      some [("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] := rfl
  have hbody : stdVecRelocFunc.body =
      .seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      (.seq stdVecRelocWhile
        (.return_ (.var "dst")))) := rfl
  have hlitk : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have e1 : evalStmtFuel F
      (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok ([("k", .u64 (BitVec.ofNat 64 0)),
        ("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)], .fellThrough) :=
    evalStmtFuel_let_ F "k" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (.u64 (BitVec.ofNat 64 0)) hlitk
  have hlastK : evalExpr (.var "last")
      [("k", .u64 (BitVec.ofNat 64 0)),
        ("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 last) := by
    simp [evalExpr, envLookup,
      show ("last" : String) ≠ "k" by decide,
      show ("last" : String) ≠ "src" by decide,
      show ("last" : String) ≠ "dst" by decide,
      show ("last" : String) ≠ "first" by decide]
  have hfirstK : evalExpr (.var "first")
      [("k", .u64 (BitVec.ofNat 64 0)),
        ("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 first) := by
    simp [evalExpr, envLookup,
      show ("first" : String) ≠ "k" by decide,
      show ("first" : String) ≠ "src" by decide,
      show ("first" : String) ≠ "dst" by decide]
  have hnEval : evalExpr (.usub (.var "last") (.var "first"))
      [("k", .u64 (BitVec.ofNat 64 0)),
        ("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (last - first)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hlastK hfirstK
  have e2 : evalStmtFuel F
      (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      [("k", .u64 (BitVec.ofNat 64 0)),
        ("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
        result 0 (last - first) bD, .fellThrough) :=
    evalStmtFuel_let_ F "n" (.u 64)
      (.usub (.var "last") (.var "first"))
      [("k", .u64 (BitVec.ofNat 64 0)),
        ("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (.u64 (last - first)) hnEval
  have hF0 : last.toNat - first.toNat - 0 + 1 ≤ F := hF
  have hloop0 := stdVecRelocWhile_correct bS lenS capS bD lenD capD
    first last result F 0 (last - first) bD (Nat.zero_le _)
    hfirst rfl hliveS hliveD hSb hDb hlenS hS64 hD64 hF0
  simp only [Nat.add_zero, Nat.sub_zero] at hloop0
  cases hblit : stdVecBlitFold bS.val lenS bS.freed bD result.toNat
      first.toNat (last.toNat - first.toNat) with
  | error e =>
    have hloopE : evalStmtFuel F stdVecRelocWhile
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          0 (last - first) bD) = .error e := by
      rw [hblit] at hloop0
      exact hloop0
    have hfwd : stdVecRelocFwd bS lenS capS bD lenD capD first last
        result = .error e := by
      simp [stdVecRelocFwd, hblit]
    have hstmt : evalStmtFuel F stdVecRelocFunc.body
        [("src", .stdVecOwned bS lenS capS),
          ("dst", .stdVecOwned bD lenD capD),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] = .error e := by
      rw [hbody]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ e1).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ e2).trans
          (evalStmtFuel_seq_err F _ _ _ _ hloopE))
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  | ok bD' =>
    have hloopO : evalStmtFuel F stdVecRelocWhile
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          0 (last - first) bD) =
        .ok (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
          result (last.toNat - first.toNat) (last - first) bD',
          .fellThrough) := by
      rw [hblit] at hloop0
      exact hloop0
    have hret : envLookup
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          (last.toNat - first.toNat) (last - first) bD') "dst" =
        some (.stdVecOwned bD' lenD capD) :=
      mkStdVecRelocEnv_dst bS lenS capS bD lenD capD first last result
        (last.toNat - first.toNat) (last - first) bD'
    have hvar : evalExpr (.var "dst")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          (last.toNat - first.toNat) (last - first) bD') =
        .ok (.stdVecOwned bD' lenD capD) := by
      simp [evalExpr, hret]
    have hfwd : stdVecRelocFwd bS lenS capS bD lenD capD first last
        result = .ok (.stdVecOwned bD' lenD capD) := by
      simp [stdVecRelocFwd, hblit]
    have hstmt : evalStmtFuel F stdVecRelocFunc.body
        [("src", .stdVecOwned bS lenS capS),
          ("dst", .stdVecOwned bD lenD capD),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] =
        .ok (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
          result (last.toNat - first.toNat) (last - first) bD',
          .returned (.stdVecOwned bD' lenD capD)) := by
      rw [hbody]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ e1).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ e2).trans
          ((evalStmtFuel_seq_fallthrough F _ _ _ _ hloopO).trans
            (evalStmtFuel_return F _ _ _ hvar)))
    simp [evalFuncFuel, hbind, hstmt, hfwd]
