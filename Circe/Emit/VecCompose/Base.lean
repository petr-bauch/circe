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
    stdVecEmptyCtorFunc, stdVecDtorFunc, stdVecReserveFunc]
