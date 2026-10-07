/-
Circe.Emit.VecCompose.Base — the shared growth-composition prelude:
the `vecGrowProg` program, triple/word projectors, bind helpers, the
composer `Name`/`Func` bundle, and the realloc leaf definitions;
composers live in `Realloc` / `Emplace` / `Entry`.
-/
import Circe.Emit.Fragment
import Circe.Emit.VecGrow

/-! ## N4d-iv-b2: `_M_realloc_insert` (growth reallocation) -/

/-- Mangled name of `_M_realloc_insert<int>`. -/
def stdVecGrowReallocName : String :=
  "_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT_"

/-- Prog-level `let_` runs the call-free evaluator (the fallback arm
    of `evalProgStmt`; cf. `evalProgStmt_return` delegating to
    `evalStmtFuel_return`). -/
theorem evalProgStmt_let_fb (prog : Prog) (fuel : Nat) (x : String)
    (ty : CType) (e : CExpr) (ρ : Env) :
    evalProgStmt prog fuel (.let_ x ty e) ρ =
      evalStmtFuel fuel (.let_ x ty e) ρ := by
  simp only [evalProgStmt]

/-- Blit preserves the destination length (the copy loop only
    `vecSet`s, which preserves length — cf. `vecSet_length`). -/
theorem stdVecBlitFold_length (src : List (BitVec 32)) (lenS : Nat)
    (freeS : Bool) (dst : Vec32) (doff soff n : Nat) (dst' : Vec32)
    (h : stdVecBlitFold src lenS freeS dst doff soff n = .ok dst') :
    dst'.val.length = dst.val.length := by
  induction n generalizing dst doff soff freeS with
  | zero =>
    simp only [stdVecBlitFold] at h
    cases h
    rfl
  | succ k ih =>
    simp only [stdVecBlitFold] at h
    by_cases hfree : freeS
    · simp [hfree] at h
    · simp [hfree] at h
      by_cases hlt : soff < lenS
      · simp [hlt] at h
        cases hx : src[soff]? with
        | none =>
          simp [hx] at h
        | some x =>
          simp [hx] at h
          cases hs : vecSet dst doff x with
          | error e =>
            simp [hs] at h
          | ok dst1 =>
            simp [hs] at h
            have h1 := ih _ _ _ _ h
            have h2 := vecSet_length _ _ _ _ hs
            omega
      · simp [hlt] at h

/-- Blit over a live destination stays live (every successful
    `vecSet` yields `freed = false` — cf. `vecSet_live`; the base
    case returns the live `dst` itself). -/
theorem stdVecBlitFold_live_of_live (src : List (BitVec 32)) (lenS : Nat)
    (freeS : Bool) (dst : Vec32) (doff soff n : Nat) (dst' : Vec32)
    (hlive : dst.freed = false)
    (h : stdVecBlitFold src lenS freeS dst doff soff n = .ok dst') :
    dst'.freed = false := by
  induction n generalizing dst doff soff freeS with
  | zero =>
    simp only [stdVecBlitFold] at h
    cases h
    exact hlive
  | succ k ih =>
    simp only [stdVecBlitFold] at h
    by_cases hfree : freeS
    · simp [hfree] at h
    · simp [hfree] at h
      by_cases hlt : soff < lenS
      · simp [hlt] at h
        cases hx : src[soff]? with
        | none =>
          simp [hx] at h
        | some x =>
          simp [hx] at h
          cases hs : vecSet dst doff x with
          | error e =>
            simp [hs] at h
          | ok dst1 =>
            simp [hs] at h
            exact ih _ _ _ _ (vecSet_live _ _ _ _ hs) h
      · simp [hlt] at h

/-- Canonical CoreIR for `_M_realloc_insert`: the 8-site growth
    composition (`check_len` → `begin` → `mi` → `allocate` →
    `construct`-at-`k` → two `_S_relocate`s → the cap-counted
    `_M_deallocate` guard), returning the reallocated triple
    (`void` in CIR fuses to the threaded triple — the mutating-leaf
    precedent: `construct` / `deallocate` return their triple so b2
    can compose; cf. the `i32 0` void of the pure leaves). The
    const-folded `cir.if #true` arm is inlined (no `if_` — the guard
    is pinned in `isStdVecReallocInsertShape`); the const-folded dead
    destroy/deallocate `cir.if #false` arm is dropped (pinned, never
    executed). `lenOld` / `capOld` bind before the consuming calls;
    `k` is the `mi` difference retagged to `u64`; `kp1` / `lenNew`
    are the bumped offsets (the corpus computes them as pointer
    strides — offsets relative to the buffer base). -/
def stdVecGrowReallocFunc : Func :=
  ⟨stdVecGrowReallocName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "pos", ty := .u 64, role := .owned },
    { name := "x", ty := .i 32, role := .owned }],
   .vecBlock,
   .seq (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.let_ "zero" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq (.callRet "newlen" stdVecCheckLenName ["t", "one"])
   (.seq (.callRet "bpos" stdVecBeginName ["t"])
   (.seq (.callRet "kd" stdVecMinusName ["pos", "bpos"])
   (.seq (.let_ "k" (.u 64) (.u64ofI64 (.var "kd")))
   (.seq (.let_ "lenOld" (.u 64) (.vgrowLen "t"))
   (.seq (.let_ "capOld" (.u 64) (.vgrowCap "t"))
   (.seq (.callRet "tNew0" stdVecAllocateName ["newlen"])
   (.seq (.callRet "tNew1" stdVecTraitsConstructName
            ["tNew0", "k", "x"])
   (.seq (.callRet "tC1" stdVecRelocName
            ["t", "tNew1", "zero", "k", "zero"])
   (.seq (.let_ "kp1" (.u 64)
            (.uadd (.var "k") (.var "one")))
   (.seq (.callRet "tC2" stdVecRelocName
            ["t", "tC1", "k", "lenOld", "kp1"])
   (.seq (.let_ "lenNew" (.u 64)
            (.uadd (.var "lenOld") (.var "one")))
   (.seq (.callRet "tDead" stdVecDeallocName ["t", "capOld"])
         (.return_ (.vgrowSetLen "tC2" (.var "lenNew")))))))))))))))))⟩

/-- Project a `u64` word out of a composer call result (a wrong
    shape is a loud mismatch, never silently modeled). -/
def vecGrowU64 : Value → Result (BitVec 64)
  | .u64 w => .ok w
  | _ => .error .AssertFail

/-- Project an `i64` word out of a composer call result. -/
def vecGrowI64 : Value → Result (BitVec 64)
  | .i64 w => .ok w
  | _ => .error .AssertFail

/-- Project an owned triple out of a composer call result. -/
def vecGrowOwned : Value → Result (Vec32 × Nat × Nat)
  | .stdVecOwned b len cap => .ok (b, len, cap)
  | _ => .error .AssertFail

/-- Project an `i32` word out of a call result (index reads). -/
def vecGrowI32 : Value → Result (BitVec 32)
  | .i32 w => .ok w
  | _ => .error .AssertFail

/-- `Result` bind on success computes (composer-local twin of
    `result_bind_ok`, which lives downstream in `Circe.Tactics` and
    cannot be imported here). -/
theorem vecGrow_bind_ok {α β : Type} (v : α) (f : α → Result β) :
    (Except.ok v).bind f = f v := rfl

/-- `Result` bind on failure short-circuits (composer-local twin of
    `result_bind_err`). -/
theorem vecGrow_bind_err {α β : Type} (e : Panic) (f : α → Result β) :
    (Except.error e).bind f = .error e := rfl

/-- Value-level forward for `_M_realloc_insert`: sequential `Result`
    binds over the frozen leaf forwards (cf. `addCallerFwd`: each
    bind is one composer `callRet`, thread through the matched
    triple components — never literals — so the `evalProgFunc`
    proof rewrites both sides with the same callee equations; the
    length arithmetic stays at `BitVec` level (the final length is
    `(ofNat len + 1).toNat` on both sides), mirroring how
    `stdVecCheckLenFwd` keeps `newlen` a word, so no arithmetic side
    conditions are needed for the value proof. Unreachable mismatch
    shapes fail loudly through the `vecGrow*` projectors, cf.
    `addCallerFwd_as_calls`. The bind-chain formulation (rather than
    one 8-deep `match` nest) keeps every unfolding equation small:
    nested matches compile to simp-toxic equation lemmas. -/
def stdVecGrowReallocFwd (b : Vec32) (len cap : Nat) (pos : BitVec 64)
    (x : BitVec 32) : Result Value :=
  (stdVecCheckLenFwd len (BitVec.ofNat 64 1)).bind fun ckv =>
  (vecGrowU64 ckv).bind fun newlen =>
  (stdVecBeginFwd).bind fun bgv =>
  (vecGrowU64 bgv).bind fun bpos =>
  (stdVecMinusFwd pos bpos).bind fun miv =>
  (vecGrowI64 miv).bind fun kd =>
  (stdVecAllocFwd newlen).bind fun alv =>
  (vecGrowOwned alv).bind fun (bNew, lenA, capA) =>
  (stdVecConstructFwd bNew lenA capA kd x).bind fun conv =>
  (vecGrowOwned conv).bind fun (bC, lenC, capC) =>
  (stdVecRelocFwd b len cap bC lenC capC (BitVec.ofNat 64 0) kd
    (BitVec.ofNat 64 0)).bind fun r1v =>
  (vecGrowOwned r1v).bind fun (bR1, lenR1, capR1) =>
  (stdVecRelocFwd b len cap bR1 lenR1 capR1 kd (BitVec.ofNat 64 len)
    (kd + BitVec.ofNat 64 1)).bind fun r2v =>
  (vecGrowOwned r2v).bind fun (bR2, _, capR2) =>
  (stdVecDeallocGuardFwd b len cap (BitVec.ofNat 64 cap)).bind fun _ =>
  .ok (.stdVecOwned bR2
    ((BitVec.ofNat 64 len + BitVec.ofNat 64 1).toNat) capR2)

/-- Mangled name of `emplace_back<int>`. -/
def stdVecEmplaceBackName : String :=
  "_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT_"

/-- Canonical CoreIR for `emplace_back`: the guard (`_M_finish` /
    `_M_end_of_storage` loads + raw-pointer `cmp ne` + `cir.if`)
    fuses to `len` / `cap` lets + a `.une` dispatch (`ne` on
    `base + len*4` vs `base + cap*4` with the same base and nonzero
    scale is exactly `len ≠ cap`); the `__args` pack load fuses to
    the direct `x` param. Fast arm: the `traits::construct` call is
    a `callRet` into the frozen b1 leaf, and the
    construct-at-finish + finish-bump (`ptr_stride` + store) fuse to
    `len + 1` with a `vgrowSetLen` return. Slow arm: the `end()`
    call is a `callRet` into the frozen `end` leaf, and the
    `_M_realloc_insert` call is a `callProg` into the proved
    composer (composer-calls-composer runs under the program
    evaluator at depth `fuel - 1`). The shared tail (`back()` call
    + `__retval` store + return) fuses away: the C++ reference
    return functionalizes as triple threading (mirroring how
    `construct`'s C++ `void` functionalizes), so both arms return
    the updated triple directly. -/
def stdVecEmplaceBackFunc : Func :=
  ⟨stdVecEmplaceBackName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "x", ty := .i 32, role := .owned }],
   .vecBlock,
   .seq (.let_ "len" (.u 64) (.vgrowLen "t"))
   (.seq (.let_ "cap" (.u 64) (.vgrowCap "t"))
   (.if_ (.une (.var "len") (.var "cap"))
     (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
     (.seq (.let_ "len1" (.u 64)
              (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
           (.return_ (.vgrowSetLen "tF" (.var "len1")))))
     (.seq (.callRet "pos" stdVecEndName ["t"])
     (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
           (.return_ (.var "r"))))))⟩

/-- Mangled name of `push_back` (rvalue-ref overload). -/
def stdVecPushBackName : String :=
  "_ZNSt6vectorIiSaIiEE9push_backEOi"

/-- Canonical CoreIR for `push_back`: the `this` / `__x` spill+reload
    fuses to the direct `(t, x)` params, and the single
    `emplace_back` call (whose reference result is discarded before
    the void return) is a `callProg` into the proved composer
    (composer-calls-composer runs under the program evaluator at
    depth `fuel - 1`). The C++ `void` functionalizes as triple
    threading, so the body returns the composer's triple directly. -/
def stdVecPushBackFunc : Func :=
  ⟨stdVecPushBackName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "x", ty := .i 32, role := .owned }],
   .vecBlock,
   .seq (.callProg "r" stdVecEmplaceBackName ["t", "x"])
     (.return_ (.var "r"))⟩

/-- Mangled name of the non-const `operator[]`. -/
def stdVecGrowIndexName : String :=
  "_ZNSt6vectorIiSaIiEEixEm"

/-- Canonical CoreIR for the non-const `operator[]`: the `_M_impl`
    projection + `_M_start` load + `ptr_stride` + the `__retval`
    spill/reload fuse to the direct `vgrowAt` element read (the
    const-`operator[]` precedent, triple-based: the caller is the
    growth entry threading the owned triple, not the erased object).
    Name-pinned at the gate: the coarse const-index shape also
    matches this body, so the b2 arm precedes it. -/
def stdVecGrowIndexFunc : Func :=
  ⟨stdVecGrowIndexName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "n", ty := .u 64, role := .owned }],
   .i 32,
   .return_ (.vgrowAt "t" (.var "n"))⟩

/-- Mangled name of `reserve`. -/
def stdVecReserveName : String :=
  "_ZNSt6vectorIiSaIiEE7reserveEm"

/-- Canonical CoreIR for `reserve`: the `max_size` throw arm fuses
    to `fail`; the `capacity < n` arm threads the owned triple
    through allocate → relocate → deallocate and re-pins the length
    (`len` unchanged, capacity becomes `n`); otherwise the triple
    passes through. -/
def stdVecReserveFunc : Func :=
  ⟨stdVecReserveName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "n", ty := .u 64, role := .owned }],
   .vecBlock,
   .if_ (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
     .fail
     (.if_ (.ult (.vgrowCap "t") (.var "n"))
       (.seq (.let_ "zero" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
         (.seq (.let_ "lenOld" (.u 64) (.vgrowLen "t"))
         (.seq (.let_ "capOld" (.u 64) (.vgrowCap "t"))
         (.seq (.callRet "tA" stdVecAllocateName ["n"])
         (.seq (.callRet "tR" stdVecRelocName
                  ["t", "tA", "zero", "lenOld", "zero"])
         (.seq (.callRet "tDead" stdVecDeallocName ["t", "capOld"])
           (.return_ (.vgrowSetLen "tR" (.var "lenOld")))))))))
       (.return_ (.var "t")))⟩

/-- Mangled names fused into the backward shift: `move_backward` /
    `__copy_move_backward_a` / `_a1` / `_a2` (single-call
    forwarders through `__miter_base` / `__niter_base` /
    `__niter_wrap`) / `__copy_move_b` (the guarded `memmove`
    terminal). -/
def stdVecShiftBackName : String :=
  "_ZSt13move_backwardIPiS0_ET0_T_S2_S1_"
def stdVecShiftBackAName : String :=
  "_ZSt22__copy_move_backward_aILb1EPiS0_ET1_T0_S2_S1_"
def stdVecShiftBackA1Name : String :=
  "_ZSt23__copy_move_backward_a1ILb1EPiS0_ET1_T0_S2_S1_"
def stdVecShiftBackA2Name : String :=
  "_ZSt23__copy_move_backward_a2ILb1EPiS0_ET1_T0_S2_S1_"
def stdVecShiftBackBName : String :=
  "_ZNSt20__copy_move_backwardILb1ELb1ESt26random_access_iterator_tagE13__copy_move_bIiEEPT_PKS3_S6_S4_"

/-- Mangled name of `_M_insert_aux` (construct-last + shift + assign). -/
def stdVecInsertAuxName : String :=
  "_ZNSt6vectorIiSaIiEE13_M_insert_auxIiEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEOT_"

/-- Mangled name of `_M_insert_rval` (the 2-arm router). -/
def stdVecInsertRvalName : String :=
  "_ZNSt6vectorIiSaIiEE14_M_insert_rvalEN9__gnu_cxx17__normal_iteratorIPKiS1_EEOi"

/-- Mangled name of the `insert(const_iterator, T&&)` forwarder. -/
def stdVecInsertName : String :=
  "_ZNSt6vectorIiSaIiEE6insertEN9__gnu_cxx17__normal_iteratorIPKiS1_EEOi"

/-- Descending copy body: `k = k - 1; t[doff + k] = t[first + k]`
    (the decrement runs first so the top word moves first). -/
def stdVecShiftBackBody : CStmt :=
  .seq (.assign "k" (.usub (.var "k") (.lit (.u64 (BitVec.ofNat 64 1)))))
    (.vgrowSet "t"
      (.uadd (.var "doff") (.var "k"))
      (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))

/-- Loop: `while (0 < k)` with `k` descending from `n`. -/
def stdVecShiftBackWhile : CStmt :=
  .while_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "k"))
    stdVecShiftBackBody

/-- Canonical CoreIR for the backward shift: `k = n = last - first`,
    `doff = result - n`, descending walk, return the triple. -/
def stdVecShiftBackFunc : Func :=
  ⟨stdVecShiftBackName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "first", ty := .u 64, role := .owned },
    { name := "last", ty := .u 64, role := .owned },
    { name := "result", ty := .u 64, role := .owned }],
   .vecBlock,
   .seq (.let_ "k" (.u 64) (.usub (.var "last") (.var "first")))
   (.seq (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
   (.seq (.let_ "doff" (.u 64) (.usub (.var "result") (.var "n")))
   (.seq stdVecShiftBackWhile
     (.return_ (.var "t")))))⟩

/-- Canonical CoreIR for `_M_insert_aux`: copy the last word to the
    fresh finish slot, bump the length, shift `[pos, len)` right by
    one, write `x` at `pos` (caller guarantees `len + 1 ≤ cap`). -/
def stdVecInsertAuxFunc : Func :=
  ⟨stdVecInsertAuxName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "pos", ty := .u 64, role := .owned },
    { name := "x", ty := .i 32, role := .owned }],
   .vecBlock,
   .seq (.let_ "len" (.u 64) (.vgrowLen "t"))
   (.seq (.let_ "last" (.u 64)
           (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
   (.seq (.let_ "lw" (.i 32) (.vgrowAt "t" (.var "last")))
   (.seq (.callRet "t1" stdVecTraitsConstructName ["t", "len", "lw"])
   (.seq (.let_ "lenp1" (.u 64)
           (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
   (.seq (.let_ "t2" (.vecBlock)
           (.vgrowSetLen "t1" (.var "lenp1")))
   (.seq (.callRet "t3" stdVecShiftBackName
           ["t2", "pos", "len", "lenp1"])
   (.seq (.callRet "t4" stdVecTraitsConstructName ["t3", "pos", "x"])
     (.return_ (.var "t4")))))))))⟩

/-- Canonical CoreIR for `_M_insert_rval`: with room, construct at
    `end()` when `pos == len`, else `_M_insert_aux`; full routes to
    `_M_realloc_insert` at `pos` (the corpus passes `begin() + n`,
    never `end()`). -/
def stdVecInsertRvalFunc : Func :=
  ⟨stdVecInsertRvalName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "pos", ty := .u 64, role := .owned },
    { name := "x", ty := .i 32, role := .owned }],
   .vecBlock,
   .seq (.let_ "len" (.u 64) (.vgrowLen "t"))
   (.if_ (.ult (.var "len") (.vgrowCap "t"))
     (.if_ (.ueq (.var "pos") (.var "len"))
       (.seq (.callRet "t1" stdVecTraitsConstructName ["t", "pos", "x"])
         (.return_ (.vgrowSetLen "t1"
           (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))))
       (.seq (.callProg "t2" stdVecInsertAuxName ["t", "pos", "x"])
         (.return_ (.var "t2"))))
     (.seq (.callProg "t3" stdVecGrowReallocName ["t", "pos", "x"])
       (.return_ (.var "t3"))))⟩

/-- Canonical CoreIR for the `insert` forwarder: delegate to
    `_M_insert_rval`, return the grown triple (the iterator return
    drops — it recomputes to `pos`). -/
def stdVecInsertFunc : Func :=
  ⟨stdVecInsertName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "pos", ty := .u 64, role := .owned },
    { name := "x", ty := .i 32, role := .owned }],
   .vecBlock,
   .seq (.callProg "t1" stdVecInsertRvalName ["t", "pos", "x"])
     (.return_ (.var "t1"))⟩

/-- Mangled names fused into the forward shift: `std::move` /
    `__copy_move_a` / `_a1` / `_a2` (single-call forwarders
    through `__miter_base` / `__niter_base` / `__niter_wrap`) /
    `__copy_m` (the guarded `memmove` terminal). -/
def stdVecShiftDownName : String :=
  "_ZSt4moveIN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEES6_ET0_T_S8_S7_"
def stdVecShiftDownAName : String :=
  "_ZSt13__copy_move_aILb1EN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEES6_ET1_T0_S8_S7_"
def stdVecShiftDownA1Name : String :=
  "_ZSt14__copy_move_a1ILb1EPiS0_ET1_T0_S2_S1_"
def stdVecShiftDownA2Name : String :=
  "_ZSt14__copy_move_a2ILb1EPiS0_ET1_T0_S2_S1_"
def stdVecShiftDownBName : String :=
  "_ZNSt11__copy_moveILb1ELb1ESt26random_access_iterator_tagE8__copy_mIiEEPT_PKS3_S6_S4_"

/-- Mangled names of the iterator move-forms: `__miter_base`
    (by-value iterator identity), `__niter_base` (iterator to
    pointer through `base`), `__niter_wrap` (iterator + pointer
    to iterator through `__niter_base` + `operator+`). -/
def stdVecMIterBaseMoveName : String :=
  "_ZSt12__miter_baseIN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEEET_S7_"
def stdVecNIterBaseMoveName : String :=
  "_ZSt12__niter_baseIPiSt6vectorIiSaIiEEET_N9__gnu_cxx17__normal_iteratorIS4_T0_EE"
def stdVecNIterWrapMoveName : String :=
  "_ZSt12__niter_wrapIN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEES2_ET_S7_T0_"

/-- Mangled name of `_M_erase` (guarded shift-down + shrink). -/
def stdVecEraseCoreName : String :=
  "_ZNSt6vectorIiSaIiEE8_M_eraseEN9__gnu_cxx17__normal_iteratorIPiS1_EE"

/-- Mangled name of the `erase(const_iterator)` forwarder. -/
def stdVecEraseName : String :=
  "_ZNSt6vectorIiSaIiEE5eraseEN9__gnu_cxx17__normal_iteratorIPKiS1_EE"

/-- Ascending copy body: `t[result + k] = t[first + k]`;
    `k = k + 1` (the increment runs last so the bottom word moves
    first). -/
def stdVecShiftDownBody : CStmt :=
  .seq (.vgrowSet "t" (.uadd (.var "result") (.var "k"))
          (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
    (.assign "k" (.uadd (.var "k")
      (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- Loop: `while (k < n)` with `k` ascending from `0`. -/
def stdVecShiftDownWhile : CStmt :=
  .while_ (.ult (.var "k") (.var "n")) stdVecShiftDownBody

/-- Canonical CoreIR for the forward shift: `k = 0`, `n = last -
    first`, ascending walk `t[result + k] = t[first + k]`, return
    the triple (dual of `stdVecShiftBackFunc`). -/
def stdVecShiftDownFunc : Func :=
  ⟨stdVecShiftDownName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "first", ty := .u 64, role := .owned },
    { name := "last", ty := .u 64, role := .owned },
    { name := "result", ty := .u 64, role := .owned }],
   .vecBlock,
   .seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
   (.seq stdVecShiftDownWhile
     (.return_ (.var "t"))))⟩

/-- Canonical CoreIR for `_M_erase`: `npos = pos + 1`; when it
    differs from `len`, shift `[npos, len)` down to `pos`, then
    shrink to `len - 1` (the per-element `destroy` is trivial for
    `int`, so the shrink is the whole effect). -/
def stdVecEraseCoreFunc : Func :=
  ⟨stdVecEraseCoreName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "pos", ty := .u 64, role := .owned }],
   .vecBlock,
   .seq (.let_ "len" (.u 64) (.vgrowLen "t"))
   (.seq (.let_ "npos" (.u 64)
           (.uadd (.var "pos") (.lit (.u64 (BitVec.ofNat 64 1)))))
   (.if_ (.une (.var "npos") (.var "len"))
     (.seq (.callProg "t1" stdVecShiftDownName
             ["t", "npos", "len", "pos"])
       (.seq (.let_ "t2" (.vecBlock)
               (.vgrowSetLen "t1"
                 (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))))
         (.return_ (.var "t2"))))
     (.seq (.let_ "t3" (.vecBlock)
             (.vgrowSetLen "t"
               (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))))
       (.return_ (.var "t3")))))⟩

/-- Canonical CoreIR for the `erase` forwarder: delegate to
    `_M_erase`, return the shrunk triple (the iterator return
    drops — it recomputes to `pos`). -/
def stdVecEraseFunc : Func :=
  ⟨stdVecEraseName,
   [{ name := "t", ty := .vecBlock, role := .owned },
    { name := "pos", ty := .u 64, role := .owned }],
   .vecBlock,
   .seq (.callProg "t1" stdVecEraseCoreName ["t", "pos"])
     (.return_ (.var "t1"))⟩


/-- The shared growth program: the frozen b1 leaves the composers
    call into (name-stamped exactly as the corpus defines them, so
    `findFunc` resolves every composer `callRet`), plus the
    already-proved composers later composers call into via
    `callProg` (`_M_realloc_insert` for `emplace_back`,
    `emplace_back` for `push_back`), plus the
    frozen `end` leaf the slow arm calls. Grows as later composers
    need more callees. Listed after the composer it includes. -/
def vecGrowProg : Prog :=
  [stdVecCheckLenFunc, stdVecBeginFunc, stdVecMinusFunc,
    stdVecAllocFunc, stdVecConstructFunc, stdVecRelocFunc,
    stdVecDeallocGuardFunc, stdVecGrowReallocFunc, stdVecEndFunc,
    stdVecEmplaceBackFunc, stdVecPushBackFunc, stdVecGrowIndexFunc,
    stdVecEmptyCtorFunc, stdVecDtorFunc, stdVecReserveFunc,
    stdVecShiftBackFunc, stdVecPlusElFunc, stdVecIterEqFunc,
    stdVecInsertAuxFunc, stdVecInsertRvalFunc, stdVecInsertFunc,
    stdVecShiftDownFunc, stdVecEraseCoreFunc, stdVecEraseFunc]
