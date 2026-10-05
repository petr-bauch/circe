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
- max-size chain (`_M_max_size` — the `S64_MAX / 4` div folds;
  `new_allocator::max_size` / `traits::max_size` — pure delegations
  into it; `_S_max_size` / `max_size` — the `min(diffmax, allocmax)`
  chain folds; all five are `2305843009213693951`) →
  `stdVecDiffMaxFunc` (the `(2^64 - 1) / 4` overflow comparand inside
  `new_allocator::allocate` is dead — it sits in the already-failing
  `n > maxDiff` branch — so no Func returns it; the bound is recorded
  as `stdVecAllocMax`).
- `std::max` / `std::min` over `u64` (early-return-`if` form) →
  `stdVecMaxFunc` / `stdVecMinFunc`.
- `_M_check_len` (the `length_error` throw fuses to `fail`, the
  `size`/`max_size`/`max` calls inline, both `cir.ternary` map to
  `tif`/`if_`) → `stdVecCheckLenFunc`.
- allocate chain (`_M_allocate` — the `n == 0` ternary is kept, both
  branches build the same value; `traits::allocate`,
  `new_allocator::allocate` — the deciding check is `n > maxDiff`
  (the `bad_array_new_length` / `bad_alloc` pair fuses to `fail`),
  the dead `4 > 16` aligned-new skeleton drops, operator
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
Aggregator: constants and the ctor-to-checklen leaves live in `Circe.Emit.VecGrow.A`, iterators through relocate in `Circe.Emit.VecGrow.B`.
-/
import Circe.Emit.VecGrow.A
import Circe.Emit.VecGrow.B
