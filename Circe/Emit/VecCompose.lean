/-
Circe.Emit.VecCompose — N4d-iv-b2 `std::vector<int32_t>` growth
composers: `_M_realloc_insert` (this slice), then `emplace_back`,
`push_back`, and the `vec_push_sum` entry. Each composer is a
`Prog`-level `Func` over the frozen b1 leaves (no inlining: every
corpus `cir.call` to a growth leaf is a `callRet` into the leaf's
canonical `Func`, resolved by name in `evalProgStmt`).

Value model: inherited from `Circe.Emit.VecGrow` (`stdVecOwned`
triples, iterators as `u64` offsets). The two composer-only pure
expression forms (`vgrowSetLen`, `u64ofI64` — see `Circe.CoreIR`)
appear only here, never in leaf bodies.
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
    stdVecEmplaceBackFunc]

/-- `check_len` success at `n = 1` delivers a `u64` word holding at
    least `len + 1` (the growth invariant both relocates' destination
    bounds need).  Needs `len ≤ max` (the `length_error` boundary):
    the error arm is then unreachable, the saturating arms deliver
    `max ≥ len + 1` (guard `¬c1` rules out `len = max`), and the
    growing arm delivers `len + inc` without wrap (guard `¬c2`). -/
theorem stdVecCheckLenFwd_ok1 (len : Nat) (v : Value)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (h : stdVecCheckLenFwd len (BitVec.ofNat 64 1) = .ok v) :
    ∃ w, v = .u64 w ∧ len + 1 ≤ w.toNat := by
  have hMlt : stdVecMaxDiff < 2 ^ 64 := by decide
  have hMrt : stdVecMaxDiffBV.toNat = stdVecMaxDiff :=
    ofNat64_toNat _ hMlt
  have hM64 : stdVecMaxDiffBV.toNat < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  have hrt : (BitVec.ofNat 64 len).toNat = len := ofNat64_toNat _ hlen64
  have h1w : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
  have hpow : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  by_cases hc1 : (stdVecMaxDiffBV - BitVec.ofNat 64 len).toNat <
      (BitVec.ofNat 64 1).toNat
  · have hc1b : (stdVecMaxDiffBV - BitVec.ofNat 64 len).ult
        (BitVec.ofNat 64 1) = true := by
      simp only [BitVec.ult_eq_decide, hc1]
      rfl
    simp only [stdVecCheckLenFwd, hc1b, ite_true] at h
    simp at h
  · have hc1b : (stdVecMaxDiffBV - BitVec.ofNat 64 len).ult
        (BitVec.ofNat 64 1) = false := by
      simp only [BitVec.ult_eq_decide, hc1]
      rfl
    have hlen1 : len + 1 ≤ stdVecMaxDiffBV.toNat := by
      have hsub : (stdVecMaxDiffBV - BitVec.ofNat 64 len).toNat =
          stdVecMaxDiffBV.toNat - len := by
        rw [BitVec.toNat_sub, hrt, hMrt]
        have h1 : 2 ^ 64 - len + stdVecMaxDiff =
            stdVecMaxDiff - len + 1 * 2 ^ 64 := by omega
        rw [h1, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega : stdVecMaxDiff - len < 2 ^ 64)]
      omega
    by_cases hc2 : (BitVec.ofNat 64 len +
          (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
            then BitVec.ofNat 64 1
            else BitVec.ofNat 64 len)).toNat <
          (BitVec.ofNat 64 len).toNat
    · have hc2b : (BitVec.ofNat 64 len +
            (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
              then BitVec.ofNat 64 1
              else BitVec.ofNat 64 len)).ult
            (BitVec.ofNat 64 len) = true := by
        rw [BitVec.ult_eq_decide]
        simp only [hc2]
        rfl
      simp only [stdVecCheckLenFwd, hc1b, hc2b, ite_true] at h
      cases h
      exact ⟨_, rfl, hlen1⟩
    · have hc2b : (BitVec.ofNat 64 len +
            (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
              then BitVec.ofNat 64 1
              else BitVec.ofNat 64 len)).ult
            (BitVec.ofNat 64 len) = false := by
        rw [BitVec.ult_eq_decide]
        simp only [hc2]
        rfl
      by_cases hc3 : stdVecMaxDiffBV.toNat <
          (BitVec.ofNat 64 len +
            (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
              then BitVec.ofNat 64 1
              else BitVec.ofNat 64 len)).toNat
      · have hc3b : stdVecMaxDiffBV.ult (BitVec.ofNat 64 len +
              (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
                then BitVec.ofNat 64 1
                else BitVec.ofNat 64 len)) = true := by
          rw [BitVec.ult_eq_decide]
          simp only [hc3]
          rfl
        simp only [stdVecCheckLenFwd, hc1b, hc2b, hc3b, ite_true] at h
        cases h
        exact ⟨_, rfl, hlen1⟩
      · have hc3b : stdVecMaxDiffBV.ult (BitVec.ofNat 64 len +
              (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
                then BitVec.ofNat 64 1
                else BitVec.ofNat 64 len)) = false := by
          rw [BitVec.ult_eq_decide]
          simp only [hc3]
          rfl
        simp only [stdVecCheckLenFwd, hc1b, hc2b, hc3b] at h
        cases h
        refine ⟨_, rfl, ?_⟩
        by_cases hc0 : (BitVec.ofNat 64 len).toNat <
            (BitVec.ofNat 64 1).toNat
        · have hc0b : (BitVec.ofNat 64 len).ult
              (BitVec.ofNat 64 1) = true := by
            simp only [BitVec.ult_eq_decide, hc0]
            rfl
          have hif : (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
                then BitVec.ofNat 64 1
                else BitVec.ofNat 64 len) =
              BitVec.ofNat 64 1 := by simp [hc0b]
          rw [hif,
            BitVec.toNat_add_of_lt (by rw [hrt, h1w]; omega),
            hrt, h1w]
          omega
        · have hc0b : (BitVec.ofNat 64 len).ult
              (BitVec.ofNat 64 1) = false := by
            simp only [BitVec.ult_eq_decide, hc0]
            rfl
          have hif : (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
                then BitVec.ofNat 64 1
                else BitVec.ofNat 64 len) =
              BitVec.ofNat 64 len := by simp [hc0b]
          have hge : 1 ≤ len := by omega
          have hmod : (BitVec.ofNat 64 len + BitVec.ofNat 64 len).toNat =
              (len + len) % 2 ^ 64 := by rw [BitVec.toNat_add, hrt]
          rw [hif] at hc2 ⊢
          rw [hpow] at hmod
          omega

/-- `allocate` success on a positive size delivers a live block of
    exactly that many slots (both arms of the zero-guard agree once
    the guard is known true; the `max` arm is unreachable noise the
    caller discharges by casing). -/
theorem stdVecAllocFwd_ok (n : BitVec 64) (v : Value)
    (hpos : (BitVec.ofNat 64 0).ult n = true)
    (h : stdVecAllocFwd n = .ok v) :
    ∃ bN, v = .stdVecOwned bN 0 n.toNat ∧ bN.freed = false ∧
      bN.val.length = n.toNat := by
  unfold stdVecAllocFwd at h
  simp only [hpos] at h
  by_cases hc : stdVecMaxDiffBV.toNat < n.toNat
  · have hcb : stdVecMaxDiffBV.ult n = true := by
      rw [BitVec.ult_eq_decide]
      simp [hc]
    simp only [hcb] at h
    simp at h
  · have hcb : stdVecMaxDiffBV.ult n = false := by
      rw [BitVec.ult_eq_decide]
      simp [hc]
    simp only [hcb] at h
    cases h
    refine ⟨_, rfl, rfl, ?_⟩
    simp

/-- `construct` success preserves the `len` / `cap` components, keeps
    the block live, and preserves the buffer length (`vecSet` only
    overwrites one slot). -/
theorem stdVecConstructFwd_ok (b : Vec32) (len cap : Nat) (p : BitVec 64)
    (x : BitVec 32) (v : Value)
    (h : stdVecConstructFwd b len cap p x = .ok v) :
    ∃ bC, v = .stdVecOwned bC len cap ∧ bC.freed = false ∧
      bC.val.length = b.val.length := by
  unfold stdVecConstructFwd at h
  cases hvs : vecSet b p.toNat x with
  | error e => simp [hvs] at h
  | ok b' =>
    simp [hvs] at h
    cases h
    exact ⟨_, rfl, vecSet_live _ _ _ _ hvs, vecSet_length _ _ _ _ hvs⟩

/-- `relocate` success preserves the destination `len` / `cap`
    components, keeps the block live, and preserves the destination
    buffer length (the blit only `vecSet`s). -/
theorem stdVecRelocFwd_ok (bS : Vec32) (lenS capS : Nat) (bD : Vec32)
    (lenD capD : Nat) (first last result : BitVec 64) (v : Value)
    (hliveD : bD.freed = false)
    (h : stdVecRelocFwd bS lenS capS bD lenD capD first last result =
      .ok v) :
    ∃ bR, v = .stdVecOwned bR lenD capD ∧ bR.freed = false ∧
      bR.val.length = bD.val.length := by
  unfold stdVecRelocFwd at h
  cases hbl : stdVecBlitFold bS.val lenS bS.freed bD result.toNat
      first.toNat (last.toNat - first.toNat) with
  | error e => simp [hbl] at h
  | ok bD' =>
    simp [hbl] at h
    cases h
    exact ⟨_, rfl, stdVecBlitFold_live_of_live _ _ _ _ _ _ _ _ hliveD hbl,
      stdVecBlitFold_length _ _ _ _ _ _ _ _ hbl⟩

set_option maxRecDepth 8192 in
/-- `emit_correct` for `_M_realloc_insert`: the program over the
    frozen b1 leaves agrees with the composer forward.  Caller-side
    preconditions: the old triple is live, `len` is below the
    `length_error` boundary, the insertion position is in bounds, the
    length fits the buffer, and fuel covers both relocates. -/
theorem evalProgFunc_stdVecGrowRealloc (F : Nat) (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hSlen : pos.toNat ≤ len)
    (hlenB : len ≤ b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hfuel1 : pos.toNat + 1 ≤ F)
    (hfuel2 : len - pos.toNat + 1 ≤ F) :
    evalProgFunc vecGrowProg F stdVecGrowReallocFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecGrowReallocFwd b len cap pos x := by
  have hbind : bindArgs stdVecGrowReallocFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      some [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] := rfl
  have hbody : stdVecGrowReallocFunc.body =
      (.seq (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
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
            (.return_ (.vgrowSetLen "tC2" (.var "lenNew")))))))))))))))))) := rfl
  have hM64 : stdVecMaxDiffBV.toNat < 2 ^ 64 := BitVec.isLt _
  have hlen64 : len < 2 ^ 64 := by omega
  have hrt : (BitVec.ofNat 64 len).toNat = len := ofNat64_toNat _ hlen64
  have h1w : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
  have hz : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by decide)
  have hkd : pos - BitVec.ofNat 64 0 = pos := BitVec.sub_zero pos
  have hpos64 : pos.toNat < 2 ^ 64 := BitVec.isLt _
  have hfindCk : findFunc vecGrowProg stdVecCheckLenName =
      some stdVecCheckLenFunc := findFunc_hit _ _
  have hfindBg : findFunc vecGrowProg stdVecBeginName =
      some stdVecBeginFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindMi : findFunc vecGrowProg stdVecMinusName =
      some stdVecMinusFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindAl : findFunc vecGrowProg stdVecAllocateName =
      some stdVecAllocFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindCon : findFunc vecGrowProg stdVecTraitsConstructName =
      some stdVecConstructFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindRe : findFunc vecGrowProg stdVecRelocName =
      some stdVecRelocFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindGd : findFunc vecGrowProg stdVecDeallocName =
      some stdVecDeallocGuardFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] = .ok (.u64 (BitVec.ofNat 64 1)) := rfl
  have hstepOne : evalProgStmt vecGrowProg F
      (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] =
      .ok (envExtend [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] "one" (.u64 (BitVec.ofNat 64 1)),
        .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hone
  have hzero : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] "one" (.u64 (BitVec.ofNat 64 1))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := rfl
  have hstepZero : evalProgStmt vecGrowProg F
      (.let_ "zero" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (envExtend [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] "one" (.u64 (BitVec.ofNat 64 1))) =
      .ok (envExtend (envExtend [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] "one"
        (.u64 (BitVec.ofNat 64 1))) "zero" (.u64 (BitVec.ofNat 64 0)),
        .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hzero
  have htCk : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) "t" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup, envExtend,
      show ("t" : String) ≠ "zero" by decide,
      show ("t" : String) ≠ "one" by decide]
  have honeCk : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) "one" =
      some (.u64 (BitVec.ofNat 64 1)) := by
    simp [envLookup, envExtend,
      show ("one" : String) ≠ "zero" by decide]
  have hargsCk : lookupArgs (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) ["t", "one"] =
      some [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 1)] := by
    simp only [lookupArgs, htCk, honeCk]
  have hcallCk : evalFuncFuel F stdVecCheckLenFunc
      [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 1)] =
      stdVecCheckLenFwd len (BitVec.ofNat 64 1) :=
    evalFuncFuel_stdVecCheckLen F b len cap (BitVec.ofNat 64 1)
  cases hck : stdVecCheckLenFwd len (BitVec.ofNat 64 1) with
  | error e =>
    have hcallCk' : evalFuncFuel F stdVecCheckLenFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 1)] =
        .error e := by rw [hcallCk, hck]
    have hstepCk := evalProgStmt_callRet_err vecGrowProg F "newlen"
      stdVecCheckLenName ["t", "one"] _ _ stdVecCheckLenFunc e
      hargsCk hfindCk hcallCk'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
      evalProgStmt_seq_err _ _ _ _ _ _ hstepCk]
    simp only [stdVecGrowReallocFwd, hck, vecGrow_bind_err]
  | ok v =>
    obtain ⟨newlen, rfl, hle1⟩ := stdVecCheckLenFwd_ok1 _ _ hmax hck
    have hcallCk' : evalFuncFuel F stdVecCheckLenFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 1)] =
        .ok (.u64 newlen) := by rw [hcallCk, hck]
    have hstepCk := evalProgStmt_callRet_ok vecGrowProg F "newlen"
      stdVecCheckLenName ["t", "one"] _ _ stdVecCheckLenFunc
      (.u64 newlen) hargsCk hfindCk hcallCk'
    have htBg : envLookup (envExtend (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "t" =
      some (.stdVecOwned b len cap) := by
      simp [envLookup, envExtend,
        show ("t" : String) ≠ "newlen" by decide,
        show ("t" : String) ≠ "zero" by decide,
        show ("t" : String) ≠ "one" by decide]
    have hargsBg : lookupArgs (envExtend (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) ["t"] =
      some [.stdVecOwned b len cap] := by
      simp only [lookupArgs, htBg]
    have hcallBg : evalFuncFuel F stdVecBeginFunc
        [.stdVecOwned b len cap] = stdVecBeginFwd :=
      evalFuncFuel_stdVecBegin F b len cap
    have hbgU : stdVecBeginFwd = .ok (.u64 (BitVec.ofNat 64 0)) := rfl
    cases hbg : stdVecBeginFwd with
    | error e =>
      have hcallBg' : evalFuncFuel F stdVecBeginFunc
          [.stdVecOwned b len cap] = .error e := by
        rw [hcallBg, hbg]
      have hstepBg := evalProgStmt_callRet_err vecGrowProg F "bpos"
        stdVecBeginName ["t"] _ _ stdVecBeginFunc e
        hargsBg hfindBg hcallBg'
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCk,
        evalProgStmt_seq_err _ _ _ _ _ _ hstepBg]
      simp only [stdVecGrowReallocFwd, hck, hbg, vecGrow_bind_ok,
        vecGrow_bind_err, vecGrowU64]
    | ok v =>
      rw [hbgU] at hbg
      cases hbg
      have hcallBg' : evalFuncFuel F stdVecBeginFunc
          [.stdVecOwned b len cap] = .ok (.u64 (BitVec.ofNat 64 0)) := by
        rw [hcallBg, hbgU]
      have hstepBg := evalProgStmt_callRet_ok vecGrowProg F "bpos"
        stdVecBeginName ["t"] _ _ stdVecBeginFunc
        (.u64 (BitVec.ofNat 64 0)) hargsBg hfindBg hcallBg'
      have hposMi : envLookup (envExtend (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
        "one" (.u64 (BitVec.ofNat 64 1))) "zero"
        (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
        (.u64 (BitVec.ofNat 64 0))) "pos" = some (.u64 pos) := by
        simp [envLookup, envExtend,
          show ("pos" : String) ≠ "bpos" by decide,
          show ("pos" : String) ≠ "newlen" by decide,
          show ("pos" : String) ≠ "zero" by decide,
          show ("pos" : String) ≠ "one" by decide]
      have hbposMi : envLookup (envExtend (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
        "one" (.u64 (BitVec.ofNat 64 1))) "zero"
        (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
        (.u64 (BitVec.ofNat 64 0))) "bpos" =
        some (.u64 (BitVec.ofNat 64 0)) :=
        envExtend_hit _ _ _
      have hargsMi : lookupArgs (envExtend (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
        "one" (.u64 (BitVec.ofNat 64 1))) "zero"
        (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
        (.u64 (BitVec.ofNat 64 0))) ["pos", "bpos"] =
        some [.u64 pos, .u64 (BitVec.ofNat 64 0)] := by
        simp only [lookupArgs, hposMi, hbposMi]
      have hcallMi : evalFuncFuel F stdVecMinusFunc
          [.u64 pos, .u64 (BitVec.ofNat 64 0)] =
          stdVecMinusFwd pos (BitVec.ofNat 64 0) :=
        evalFuncFuel_stdVecMinus F pos (BitVec.ofNat 64 0)
      have hmiU : stdVecMinusFwd pos (BitVec.ofNat 64 0) =
          .ok (.i64 (pos - BitVec.ofNat 64 0)) := rfl
      cases hmi : stdVecMinusFwd pos (BitVec.ofNat 64 0) with
      | error e =>
        have hcallMi' : evalFuncFuel F stdVecMinusFunc
            [.u64 pos, .u64 (BitVec.ofNat 64 0)] = .error e := by
          rw [hcallMi, hmi]
        have hstepMi := evalProgStmt_callRet_err vecGrowProg F "kd"
          stdVecMinusName ["pos", "bpos"] _ _ stdVecMinusFunc e
          hargsMi hfindMi hcallMi'
        simp only [evalProgFunc, hbind, hbody]
        rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCk,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepBg,
          evalProgStmt_seq_err _ _ _ _ _ _ hstepMi]
        simp only [stdVecGrowReallocFwd, hck, hbgU, hmi, vecGrow_bind_ok,
          vecGrow_bind_err, vecGrowU64]
      | ok v =>
        rw [hmiU] at hmi
        cases hmi
        have hcallMi' : evalFuncFuel F stdVecMinusFunc
            [.u64 pos, .u64 (BitVec.ofNat 64 0)] =
            .ok (.i64 (pos - BitVec.ofNat 64 0)) := by
          rw [hcallMi, hmiU]
        have hstepMi := evalProgStmt_callRet_ok vecGrowProg F "kd"
          stdVecMinusName ["pos", "bpos"] _ _ stdVecMinusFunc
          (.i64 (pos - BitVec.ofNat 64 0)) hargsMi hfindMi hcallMi'
        have hkdHit : evalExpr (.var "kd") (envExtend (envExtend (envExtend
          (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) =
          .ok (.i64 (pos - BitVec.ofNat 64 0)) :=
          evalExpr_var_hit _ _ _ (envExtend_hit _ _ _)
        have hkEval : evalExpr (.u64ofI64 (.var "kd")) (envExtend
          (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) =
          .ok (.u64 (pos - BitVec.ofNat 64 0)) :=
          evalExpr_u64ofI64_hit _ _ _ hkdHit
        have hstepK : evalProgStmt vecGrowProg F
            (.let_ "k" (.u 64) (.u64ofI64 (.var "kd"))) (envExtend
            (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) =
            .ok (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0)), .fellThrough) := by
          rw [evalProgStmt_let_fb]
          exact evalStmtFuel_let_ _ _ _ _ _ _ hkEval
        have htLen : envLookup (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "t" =
          some (.stdVecOwned b len cap) := by
          simp [envLookup, envExtend,
            show ("t" : String) ≠ "k" by decide,
            show ("t" : String) ≠ "kd" by decide,
            show ("t" : String) ≠ "bpos" by decide,
            show ("t" : String) ≠ "newlen" by decide,
            show ("t" : String) ≠ "zero" by decide,
            show ("t" : String) ≠ "one" by decide]
        have hlenOldEval : evalExpr (.vgrowLen "t") (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) =
          .ok (.u64 (BitVec.ofNat 64 len)) :=
          evalExpr_vgrowLen_some _ _ _ _ _ htLen
        have hstepLenOld : evalProgStmt vecGrowProg F
            (.let_ "lenOld" (.u 64) (.vgrowLen "t")) (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) =
            .ok (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len)), .fellThrough) := by
          rw [evalProgStmt_let_fb]
          exact evalStmtFuel_let_ _ _ _ _ _ _ hlenOldEval
        have htCap : envLookup (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
          (.u64 (BitVec.ofNat 64 len))) "t" =
          some (.stdVecOwned b len cap) := by
          simp [envLookup, envExtend,
            show ("t" : String) ≠ "lenOld" by decide,
            show ("t" : String) ≠ "k" by decide,
            show ("t" : String) ≠ "kd" by decide,
            show ("t" : String) ≠ "bpos" by decide,
            show ("t" : String) ≠ "newlen" by decide,
            show ("t" : String) ≠ "zero" by decide,
            show ("t" : String) ≠ "one" by decide]
        have hcapOldEval : evalExpr (.vgrowCap "t") (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
          (.u64 (BitVec.ofNat 64 len))) =
          .ok (.u64 (BitVec.ofNat 64 cap)) :=
          evalExpr_vgrowCap_some _ _ _ _ _ htCap
        have hstepCapOld : evalProgStmt vecGrowProg F
            (.let_ "capOld" (.u 64) (.vgrowCap "t")) (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) =
            .ok (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap)), .fellThrough) := by
          rw [evalProgStmt_let_fb]
          exact evalStmtFuel_let_ _ _ _ _ _ _ hcapOldEval
        have hnewlenAl : envLookup (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
          (.u64 (BitVec.ofNat 64 len))) "capOld"
          (.u64 (BitVec.ofNat 64 cap))) "newlen" =
          some (.u64 newlen) := by
          simp [envLookup, envExtend,
            show ("newlen" : String) ≠ "capOld" by decide,
            show ("newlen" : String) ≠ "lenOld" by decide,
            show ("newlen" : String) ≠ "k" by decide,
            show ("newlen" : String) ≠ "kd" by decide,
            show ("newlen" : String) ≠ "bpos" by decide]
        have hargsAl : lookupArgs (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
          (.u64 (BitVec.ofNat 64 len))) "capOld"
          (.u64 (BitVec.ofNat 64 cap))) ["newlen"] =
          some [.u64 newlen] := by
          simp only [lookupArgs, hnewlenAl]
        have hcallAl : evalFuncFuel F stdVecAllocFunc [.u64 newlen] =
            stdVecAllocFwd newlen :=
          evalFuncFuel_stdVecAlloc F newlen
        have hnpos : 0 < newlen.toNat := by omega
        have hnewpos : (BitVec.ofNat 64 0).ult newlen = true := by
          simp only [BitVec.ult_eq_decide, hz, hnpos]
          rfl
        cases hal : stdVecAllocFwd newlen with
        | error e =>
          have hcallAl' : evalFuncFuel F stdVecAllocFunc [.u64 newlen] =
              .error e := by rw [hcallAl, hal]
          have hstepAl := evalProgStmt_callRet_err vecGrowProg F "tNew0"
            stdVecAllocateName ["newlen"] _ _ stdVecAllocFunc e
            hargsAl hfindAl hcallAl'
          simp only [evalProgFunc, hbind, hbody]
          rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCk,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepBg,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepMi,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepK,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
            evalProgStmt_seq_err _ _ _ _ _ _ hstepAl]
          simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal,
            vecGrow_bind_ok, vecGrow_bind_err, vecGrowU64, vecGrowI64]
        | ok v =>
          obtain ⟨bNew, rfl, hNlive, hNlen⟩ :=
            stdVecAllocFwd_ok _ _ hnewpos hal
          have hcallAl' : evalFuncFuel F stdVecAllocFunc [.u64 newlen] =
              .ok (.stdVecOwned bNew 0 newlen.toNat) := by
            rw [hcallAl, hal]
          have hstepAl := evalProgStmt_callRet_ok vecGrowProg F "tNew0"
            stdVecAllocateName ["newlen"] _ _ stdVecAllocFunc
            (.stdVecOwned bNew 0 newlen.toNat) hargsAl hfindAl hcallAl'
          have htNew0Con : envLookup (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap))) "tNew0"
            (.stdVecOwned bNew 0 newlen.toNat)) "tNew0" =
            some (.stdVecOwned bNew 0 newlen.toNat) :=
            envExtend_hit _ _ _
          have hkCon : envLookup (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap))) "tNew0"
            (.stdVecOwned bNew 0 newlen.toNat)) "k" =
            some (.u64 (pos - BitVec.ofNat 64 0)) := by
            simp [envLookup, envExtend,
              show ("k" : String) ≠ "tNew0" by decide,
              show ("k" : String) ≠ "capOld" by decide,
              show ("k" : String) ≠ "lenOld" by decide]
          have hxCon : envLookup (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap))) "tNew0"
            (.stdVecOwned bNew 0 newlen.toNat)) "x" =
            some (.i32 x) := by
            simp [envLookup, envExtend,
              show ("x" : String) ≠ "tNew0" by decide,
              show ("x" : String) ≠ "capOld" by decide,
              show ("x" : String) ≠ "lenOld" by decide,
              show ("x" : String) ≠ "k" by decide,
              show ("x" : String) ≠ "kd" by decide,
              show ("x" : String) ≠ "bpos" by decide,
              show ("x" : String) ≠ "newlen" by decide,
              show ("x" : String) ≠ "zero" by decide,
              show ("x" : String) ≠ "one" by decide,
              show ("x" : String) ≠ "t" by decide,
              show ("x" : String) ≠ "pos" by decide]
          have hargsCon : lookupArgs (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap))) "tNew0"
            (.stdVecOwned bNew 0 newlen.toNat))
            ["tNew0", "k", "x"] =
            some [.stdVecOwned bNew 0 newlen.toNat,
              .u64 (pos - BitVec.ofNat 64 0), .i32 x] := by
            simp only [lookupArgs, htNew0Con, hkCon, hxCon]
          have hcallCon : evalFuncFuel F stdVecConstructFunc
              [.stdVecOwned bNew 0 newlen.toNat,
                .u64 (pos - BitVec.ofNat 64 0), .i32 x] =
              stdVecConstructFwd bNew 0 newlen.toNat
                (pos - BitVec.ofNat 64 0) x :=
            evalFuncFuel_stdVecConstruct F bNew 0 newlen.toNat
              (pos - BitVec.ofNat 64 0) x
          cases hcon : stdVecConstructFwd bNew 0 newlen.toNat
              (pos - BitVec.ofNat 64 0) x with
          | error e =>
            have hcallCon' : evalFuncFuel F stdVecConstructFunc
                [.stdVecOwned bNew 0 newlen.toNat,
                  .u64 (pos - BitVec.ofNat 64 0), .i32 x] =
                .error e := by rw [hcallCon, hcon]
            have hstepCon := evalProgStmt_callRet_err vecGrowProg F "tNew1"
              stdVecTraitsConstructName ["tNew0", "k", "x"] _ _
              stdVecConstructFunc e hargsCon hfindCon hcallCon'
            simp only [evalProgFunc, hbind, hbody]
            rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCk,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepBg,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepMi,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepK,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepAl,
              evalProgStmt_seq_err _ _ _ _ _ _ hstepCon]
            simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal, hcon,
              vecGrow_bind_ok, vecGrow_bind_err, vecGrowU64, vecGrowI64,
              vecGrowOwned]
          | ok v =>
            obtain ⟨bC, rfl, hClive, hClen⟩ :=
              stdVecConstructFwd_ok _ _ _ _ _ _ hcon
            have hcallCon' : evalFuncFuel F stdVecConstructFunc
                [.stdVecOwned bNew 0 newlen.toNat,
                  .u64 (pos - BitVec.ofNat 64 0), .i32 x] =
                .ok (.stdVecOwned bC 0 newlen.toNat) := by
              rw [hcallCon, hcon]
            have hstepCon := evalProgStmt_callRet_ok vecGrowProg F "tNew1"
              stdVecTraitsConstructName ["tNew0", "k", "x"] _ _
              stdVecConstructFunc (.stdVecOwned bC 0 newlen.toNat)
              hargsCon hfindCon hcallCon'
            have hkdT : (pos - BitVec.ofNat 64 0).toNat = pos.toNat := by
              rw [hkd]
            have htR1 : envLookup (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat)) "t" =
              some (.stdVecOwned b len cap) := by
              simp [envLookup, envExtend,
                show ("t" : String) ≠ "tNew1" by decide,
                show ("t" : String) ≠ "tNew0" by decide,
                show ("t" : String) ≠ "capOld" by decide,
                show ("t" : String) ≠ "lenOld" by decide,
                show ("t" : String) ≠ "k" by decide,
                show ("t" : String) ≠ "kd" by decide,
                show ("t" : String) ≠ "bpos" by decide,
                show ("t" : String) ≠ "newlen" by decide,
                show ("t" : String) ≠ "zero" by decide,
                show ("t" : String) ≠ "one" by decide]
            have htNew1R1 : envLookup (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat)) "tNew1" =
              some (.stdVecOwned bC 0 newlen.toNat) :=
              envExtend_hit _ _ _
            have hzeroR1 : envLookup (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat)) "zero" =
              some (.u64 (BitVec.ofNat 64 0)) := by
              simp [envLookup, envExtend,
                show ("zero" : String) ≠ "tNew1" by decide,
                show ("zero" : String) ≠ "tNew0" by decide,
                show ("zero" : String) ≠ "capOld" by decide,
                show ("zero" : String) ≠ "lenOld" by decide,
                show ("zero" : String) ≠ "k" by decide,
                show ("zero" : String) ≠ "kd" by decide,
                show ("zero" : String) ≠ "bpos" by decide,
                show ("zero" : String) ≠ "newlen" by decide]
            have hkR1 : envLookup (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat)) "k" =
              some (.u64 (pos - BitVec.ofNat 64 0)) := by
              simp [envLookup, envExtend,
                show ("k" : String) ≠ "tNew1" by decide,
                show ("k" : String) ≠ "tNew0" by decide,
                show ("k" : String) ≠ "capOld" by decide,
                show ("k" : String) ≠ "lenOld" by decide]
            have hargsR1 : lookupArgs (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat))
              ["t", "tNew1", "zero", "k", "zero"] =
              some [.stdVecOwned b len cap,
                .stdVecOwned bC 0 newlen.toNat,
                .u64 (BitVec.ofNat 64 0),
                .u64 (pos - BitVec.ofNat 64 0),
                .u64 (BitVec.ofNat 64 0)] := by
              simp only [lookupArgs, htR1, htNew1R1, hzeroR1, hkR1]
            have hcallR1 : evalFuncFuel F stdVecRelocFunc
                [.stdVecOwned b len cap,
                  .stdVecOwned bC 0 newlen.toNat,
                  .u64 (BitVec.ofNat 64 0),
                  .u64 (pos - BitVec.ofNat 64 0),
                  .u64 (BitVec.ofNat 64 0)] =
                stdVecRelocFwd b len cap bC 0 newlen.toNat
                  (BitVec.ofNat 64 0) (pos - BitVec.ofNat 64 0)
                  (BitVec.ofNat 64 0) :=
              evalFuncFuel_stdVecReloc F b len cap bC 0 newlen.toNat
                (BitVec.ofNat 64 0) (pos - BitVec.ofNat 64 0)
                (BitVec.ofNat 64 0) (by rw [hz, hkdT]; omega) hlive hClive
                (by rw [hkdT]; omega) (by rw [hz, hkdT, hClen, hNlen]; omega)
                (by rw [hkdT]; exact hSlen) h64
                (by rw [hClen, hNlen]; exact BitVec.isLt _)
                (by rw [hz, hkdT]; omega)
            cases hr1 : stdVecRelocFwd b len cap bC 0 newlen.toNat
                (BitVec.ofNat 64 0) (pos - BitVec.ofNat 64 0)
                (BitVec.ofNat 64 0) with
            | error e =>
              have hcallR1' : evalFuncFuel F stdVecRelocFunc
                  [.stdVecOwned b len cap,
                    .stdVecOwned bC 0 newlen.toNat,
                    .u64 (BitVec.ofNat 64 0),
                    .u64 (pos - BitVec.ofNat 64 0),
                    .u64 (BitVec.ofNat 64 0)] = .error e := by
                rw [hcallR1, hr1]
              have hstepR1 := evalProgStmt_callRet_err vecGrowProg F "tC1"
                stdVecRelocName ["t", "tNew1", "zero", "k", "zero"] _ _
                stdVecRelocFunc e hargsR1 hfindRe hcallR1'
              simp only [evalProgFunc, hbind, hbody]
              rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne,
                evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
                evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCk,
                evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepBg,
                evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepMi,
                evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepK,
                evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
                evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
                evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepAl,
                evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCon,
                evalProgStmt_seq_err _ _ _ _ _ _ hstepR1]
              simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal, hcon,
                hr1, vecGrow_bind_ok, vecGrow_bind_err, vecGrowU64,
                vecGrowI64, vecGrowOwned]
            | ok v =>
              obtain ⟨bR1, rfl, hR1live, hR1len⟩ :=
                stdVecRelocFwd_ok _ _ _ _ _ _ _ _ _ _ hClive hr1
              have hcallR1' : evalFuncFuel F stdVecRelocFunc
                  [.stdVecOwned b len cap,
                    .stdVecOwned bC 0 newlen.toNat,
                    .u64 (BitVec.ofNat 64 0),
                    .u64 (pos - BitVec.ofNat 64 0),
                    .u64 (BitVec.ofNat 64 0)] =
                  .ok (.stdVecOwned bR1 0 newlen.toNat) := by
                rw [hcallR1, hr1]
              have hstepR1 := evalProgStmt_callRet_ok vecGrowProg F "tC1"
                stdVecRelocName ["t", "tNew1", "zero", "k", "zero"] _ _
                stdVecRelocFunc (.stdVecOwned bR1 0 newlen.toNat)
                hargsR1 hfindRe hcallR1'
              have hkKp1 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "k" =
                some (.u64 (pos - BitVec.ofNat 64 0)) := by
                simp [envLookup, envExtend,
                  show ("k" : String) ≠ "tC1" by decide,
                  show ("k" : String) ≠ "tNew1" by decide,
                  show ("k" : String) ≠ "tNew0" by decide,
                  show ("k" : String) ≠ "capOld" by decide,
                  show ("k" : String) ≠ "lenOld" by decide]
              have honeKp1 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "one" =
                some (.u64 (BitVec.ofNat 64 1)) := by
                simp [envLookup, envExtend,
                  show ("one" : String) ≠ "tC1" by decide,
                  show ("one" : String) ≠ "tNew1" by decide,
                  show ("one" : String) ≠ "tNew0" by decide,
                  show ("one" : String) ≠ "capOld" by decide,
                  show ("one" : String) ≠ "lenOld" by decide,
                  show ("one" : String) ≠ "k" by decide,
                  show ("one" : String) ≠ "kd" by decide,
                  show ("one" : String) ≠ "bpos" by decide,
                  show ("one" : String) ≠ "newlen" by decide,
                  show ("one" : String) ≠ "zero" by decide]
              have hkp1Eval : evalExpr (.uadd (.var "k") (.var "one"))
                (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) =
                .ok (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1)) :=
                evalExpr_uadd_u64 _ _ _ _ _
                  (evalExpr_var_hit _ _ _ hkKp1)
                  (evalExpr_var_hit _ _ _ honeKp1)
              have hstepKp1 : evalProgStmt vecGrowProg F
                  (.let_ "kp1" (.u 64)
                    (.uadd (.var "k") (.var "one"))) (envExtend (envExtend
                  (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                  (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) =
                  .ok (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                  (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1)), .fellThrough) := by
                rw [evalProgStmt_let_fb]
                exact evalStmtFuel_let_ _ _ _ _ _ _ hkp1Eval
              have hpos1lt : pos.toNat + 1 < 2 ^ 64 := by omega
              have hkp1rt : (pos - BitVec.ofNat 64 0 +
                  BitVec.ofNat 64 1).toNat = pos.toNat + 1 := by
                rw [BitVec.toNat_add_of_lt (by rw [hkdT, h1w]; omega),
                  hkdT, h1w]
              have htR2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "t" =
                some (.stdVecOwned b len cap) := by
                simp [envLookup, envExtend,
                  show ("t" : String) ≠ "kp1" by decide,
                  show ("t" : String) ≠ "tC1" by decide,
                  show ("t" : String) ≠ "tNew1" by decide,
                  show ("t" : String) ≠ "tNew0" by decide,
                  show ("t" : String) ≠ "capOld" by decide,
                  show ("t" : String) ≠ "lenOld" by decide,
                  show ("t" : String) ≠ "k" by decide,
                  show ("t" : String) ≠ "kd" by decide,
                  show ("t" : String) ≠ "bpos" by decide,
                  show ("t" : String) ≠ "newlen" by decide,
                  show ("t" : String) ≠ "zero" by decide,
                  show ("t" : String) ≠ "one" by decide]
              have htC1R2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "tC1" =
                some (.stdVecOwned bR1 0 newlen.toNat) := by
                simp [envLookup, envExtend,
                  show ("tC1" : String) ≠ "kp1" by decide]
              have hkR2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "k" =
                some (.u64 (pos - BitVec.ofNat 64 0)) := by
                simp [envLookup, envExtend,
                  show ("k" : String) ≠ "kp1" by decide,
                  show ("k" : String) ≠ "tC1" by decide,
                  show ("k" : String) ≠ "tNew1" by decide,
                  show ("k" : String) ≠ "tNew0" by decide,
                  show ("k" : String) ≠ "capOld" by decide,
                  show ("k" : String) ≠ "lenOld" by decide]
              have hlenOldR2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "lenOld" =
                some (.u64 (BitVec.ofNat 64 len)) := by
                simp [envLookup, envExtend,
                  show ("lenOld" : String) ≠ "kp1" by decide,
                  show ("lenOld" : String) ≠ "tC1" by decide,
                  show ("lenOld" : String) ≠ "tNew1" by decide,
                  show ("lenOld" : String) ≠ "tNew0" by decide,
                  show ("lenOld" : String) ≠ "capOld" by decide]
              have hkp1R2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "kp1" =
                some (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1)) :=
                envExtend_hit _ _ _
              have hargsR2 : lookupArgs (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1)))
                ["t", "tC1", "k", "lenOld", "kp1"] =
                some [.stdVecOwned b len cap,
                  .stdVecOwned bR1 0 newlen.toNat,
                  .u64 (pos - BitVec.ofNat 64 0),
                  .u64 (BitVec.ofNat 64 len),
                  .u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1)] := by
                simp only [lookupArgs, htR2, htC1R2, hkR2, hlenOldR2,
                  hkp1R2]
              have hcallR2 : evalFuncFuel F stdVecRelocFunc
                  [.stdVecOwned b len cap,
                    .stdVecOwned bR1 0 newlen.toNat,
                    .u64 (pos - BitVec.ofNat 64 0),
                    .u64 (BitVec.ofNat 64 len),
                    .u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1)] =
                  stdVecRelocFwd b len cap bR1 0 newlen.toNat
                    (pos - BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
                    ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1) :=
                evalFuncFuel_stdVecReloc F b len cap bR1 0 newlen.toNat
                  (pos - BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
                  ((pos - BitVec.ofNat 64 0) + BitVec.ofNat 64 1)
                  (by rw [hkdT, hrt]; exact hSlen) hlive hR1live
                  (by rw [hrt]; exact hlenB)
                  (by rw [hkp1rt, hrt, hkdT, hR1len, hClen, hNlen]; omega)
                  (by simp [hrt]) h64
                  (by rw [hR1len, hClen, hNlen]; exact BitVec.isLt _)
                  (by rw [hrt, hkdT]; exact hfuel2)
              cases hr2 : stdVecRelocFwd b len cap bR1 0 newlen.toNat
                  (pos - BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
                  ((pos - BitVec.ofNat 64 0) + BitVec.ofNat 64 1) with
              | error e =>
                have hcallR2' : evalFuncFuel F stdVecRelocFunc
                    [.stdVecOwned b len cap,
                      .stdVecOwned bR1 0 newlen.toNat,
                      .u64 (pos - BitVec.ofNat 64 0),
                      .u64 (BitVec.ofNat 64 len),
                      .u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1)] = .error e := by
                  rw [hcallR2, hr2]
                have hstepR2 := evalProgStmt_callRet_err vecGrowProg F "tC2"
                  stdVecRelocName ["t", "tC1", "k", "lenOld", "kp1"] _ _
                  stdVecRelocFunc e hargsR2 hfindRe hcallR2'
                simp only [evalProgFunc, hbind, hbody]
                rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCk,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepBg,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepMi,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepK,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepAl,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCon,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepR1,
                  evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepKp1,
                  evalProgStmt_seq_err _ _ _ _ _ _ hstepR2]
                simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal,
                  hcon, hr1, hr2, vecGrow_bind_ok, vecGrow_bind_err,
                  vecGrowU64, vecGrowI64, vecGrowOwned]
              | ok v =>
                obtain ⟨bR2, rfl, hR2live, hR2len⟩ :=
                  stdVecRelocFwd_ok _ _ _ _ _ _ _ _ _ _ hR1live hr2
                have hcallR2' : evalFuncFuel F stdVecRelocFunc
                    [.stdVecOwned b len cap,
                      .stdVecOwned bR1 0 newlen.toNat,
                      .u64 (pos - BitVec.ofNat 64 0),
                      .u64 (BitVec.ofNat 64 len),
                      .u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1)] =
                    .ok (.stdVecOwned bR2 0 newlen.toNat) := by
                  rw [hcallR2, hr2]
                have hstepR2 := evalProgStmt_callRet_ok vecGrowProg F "tC2"
                  stdVecRelocName ["t", "tC1", "k", "lenOld", "kp1"] _ _
                  stdVecRelocFunc (.stdVecOwned bR2 0 newlen.toNat)
                  hargsR2 hfindRe hcallR2'
                have hlenOldLN : envLookup (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "lenOld" =
                  some (.u64 (BitVec.ofNat 64 len)) := by
                  simp [envLookup, envExtend,
                    show ("lenOld" : String) ≠ "tC2" by decide,
                    show ("lenOld" : String) ≠ "kp1" by decide,
                    show ("lenOld" : String) ≠ "tC1" by decide,
                    show ("lenOld" : String) ≠ "tNew1" by decide,
                    show ("lenOld" : String) ≠ "tNew0" by decide,
                    show ("lenOld" : String) ≠ "capOld" by decide]
                have honeLN : envLookup (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "one" =
                  some (.u64 (BitVec.ofNat 64 1)) := by
                  simp [envLookup, envExtend,
                    show ("one" : String) ≠ "tC2" by decide,
                    show ("one" : String) ≠ "kp1" by decide,
                    show ("one" : String) ≠ "tC1" by decide,
                    show ("one" : String) ≠ "tNew1" by decide,
                    show ("one" : String) ≠ "tNew0" by decide,
                    show ("one" : String) ≠ "capOld" by decide,
                    show ("one" : String) ≠ "lenOld" by decide,
                    show ("one" : String) ≠ "k" by decide,
                    show ("one" : String) ≠ "kd" by decide,
                    show ("one" : String) ≠ "bpos" by decide,
                    show ("one" : String) ≠ "newlen" by decide,
                    show ("one" : String) ≠ "zero" by decide]
                have hlenNewEval : evalExpr
                    (.uadd (.var "lenOld") (.var "one")) (envExtend
                    (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat)) =
                    .ok (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1)) :=
                  evalExpr_uadd_u64 _ _ _ _ _
                    (evalExpr_var_hit _ _ _ hlenOldLN)
                    (evalExpr_var_hit _ _ _ honeLN)
                have hstepLenNew : evalProgStmt vecGrowProg F
                    (.let_ "lenNew" (.u 64)
                      (.uadd (.var "lenOld") (.var "one"))) (envExtend
                    (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat)) =
                    .ok (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                    (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1)), .fellThrough) := by
                  rw [evalProgStmt_let_fb]
                  exact evalStmtFuel_let_ _ _ _ _ _ _ hlenNewEval
                have htGd : envLookup (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                  (.u64 ((BitVec.ofNat 64 len) +
                    BitVec.ofNat 64 1))) "t" =
                  some (.stdVecOwned b len cap) := by
                  simp [envLookup, envExtend,
                    show ("t" : String) ≠ "lenNew" by decide,
                    show ("t" : String) ≠ "tC2" by decide,
                    show ("t" : String) ≠ "kp1" by decide,
                    show ("t" : String) ≠ "tC1" by decide,
                    show ("t" : String) ≠ "tNew1" by decide,
                    show ("t" : String) ≠ "tNew0" by decide,
                    show ("t" : String) ≠ "capOld" by decide,
                    show ("t" : String) ≠ "lenOld" by decide,
                    show ("t" : String) ≠ "k" by decide,
                    show ("t" : String) ≠ "kd" by decide,
                    show ("t" : String) ≠ "bpos" by decide,
                    show ("t" : String) ≠ "newlen" by decide,
                    show ("t" : String) ≠ "zero" by decide,
                    show ("t" : String) ≠ "one" by decide]
                have hcapOldGd : envLookup (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                  (.u64 ((BitVec.ofNat 64 len) +
                    BitVec.ofNat 64 1))) "capOld" =
                  some (.u64 (BitVec.ofNat 64 cap)) := by
                  simp [envLookup, envExtend,
                    show ("capOld" : String) ≠ "lenNew" by decide,
                    show ("capOld" : String) ≠ "tC2" by decide,
                    show ("capOld" : String) ≠ "kp1" by decide,
                    show ("capOld" : String) ≠ "tC1" by decide,
                    show ("capOld" : String) ≠ "tNew1" by decide,
                    show ("capOld" : String) ≠ "tNew0" by decide]
                have hargsGd : lookupArgs (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                  (.u64 ((BitVec.ofNat 64 len) +
                    BitVec.ofNat 64 1))) ["t", "capOld"] =
                  some [.stdVecOwned b len cap,
                    .u64 (BitVec.ofNat 64 cap)] := by
                  simp only [lookupArgs, htGd, hcapOldGd]
                have hcallGd : evalFuncFuel F stdVecDeallocGuardFunc
                    [.stdVecOwned b len cap,
                      .u64 (BitVec.ofNat 64 cap)] =
                    stdVecDeallocGuardFwd b len cap
                      (BitVec.ofNat 64 cap) :=
                  evalFuncFuel_stdVecDeallocGuard F b len cap
                    (BitVec.ofNat 64 cap)
                cases hgd : stdVecDeallocGuardFwd b len cap
                    (BitVec.ofNat 64 cap) with
                | error e =>
                  have hcallGd' : evalFuncFuel F stdVecDeallocGuardFunc
                      [.stdVecOwned b len cap,
                        .u64 (BitVec.ofNat 64 cap)] = .error e := by
                    rw [hcallGd, hgd]
                  have hstepGd := evalProgStmt_callRet_err vecGrowProg F
                    "tDead" stdVecDeallocName ["t", "capOld"] _ _
                    stdVecDeallocGuardFunc e hargsGd hfindGd hcallGd'
                  simp only [evalProgFunc, hbind, hbody]
                  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCk,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepBg,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepMi,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepK,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepAl,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCon,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepR1,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepKp1,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepR2,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenNew,
                    evalProgStmt_seq_err _ _ _ _ _ _ hstepGd]
                  simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal,
                    hcon, hr1, hr2, hgd, vecGrow_bind_ok, vecGrow_bind_err,
                    vecGrowU64, vecGrowI64, vecGrowOwned]
                | ok v =>
                  have hcallGd' : evalFuncFuel F stdVecDeallocGuardFunc
                      [.stdVecOwned b len cap,
                        .u64 (BitVec.ofNat 64 cap)] = .ok v := by
                    rw [hcallGd, hgd]
                  have hstepGd := evalProgStmt_callRet_ok vecGrowProg F
                    "tDead" stdVecDeallocName ["t", "capOld"] _ _
                    stdVecDeallocGuardFunc v hargsGd hfindGd hcallGd'
                  have htC2 : envLookup (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                    (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1))) "tDead" v) "tC2" =
                    some (.stdVecOwned bR2 0 newlen.toNat) := by
                    simp [envLookup, envExtend,
                      show ("tC2" : String) ≠ "tDead" by decide]
                  have hlenNewHit : evalExpr (.var "lenNew") (envExtend
                    (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                    (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1))) "tDead" v) =
                    .ok (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1)) := by
                    simp [evalExpr, envLookup, envExtend,
                      show ("lenNew" : String) ≠ "tDead" by decide]
                  have hretEval : evalExpr
                      (.vgrowSetLen "tC2" (.var "lenNew")) (envExtend
                      (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend
                      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                        ("x", .i32 x)]
                      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                      "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                      (.i64 (pos - BitVec.ofNat 64 0))) "k"
                      (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                      (.u64 (BitVec.ofNat 64 len))) "capOld"
                      (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                      (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                      (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                      (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                      (.u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1))) "tC2"
                      (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                      (.u64 ((BitVec.ofNat 64 len) +
                        BitVec.ofNat 64 1))) "tDead" v) =
                      .ok (.stdVecOwned bR2
                        (((BitVec.ofNat 64 len) +
                          BitVec.ofNat 64 1).toNat) newlen.toNat) :=
                    evalExpr_vgrowSetLen_hit _ _ _ _ _ _ _ htC2 hlenNewHit
                  have hret : evalProgStmt vecGrowProg F
                      (.return_ (.vgrowSetLen "tC2" (.var "lenNew")))
                      (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend
                      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                        ("x", .i32 x)]
                      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                      "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                      (.i64 (pos - BitVec.ofNat 64 0))) "k"
                      (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                      (.u64 (BitVec.ofNat 64 len))) "capOld"
                      (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                      (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                      (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                      (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                      (.u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1))) "tC2"
                      (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                      (.u64 ((BitVec.ofNat 64 len) +
                        BitVec.ofNat 64 1))) "tDead" v) =
                      .ok (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend
                      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                        ("x", .i32 x)]
                      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                      "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                      (.i64 (pos - BitVec.ofNat 64 0))) "k"
                      (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                      (.u64 (BitVec.ofNat 64 len))) "capOld"
                      (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                      (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                      (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                      (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                      (.u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1))) "tC2"
                      (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                      (.u64 ((BitVec.ofNat 64 len) +
                        BitVec.ofNat 64 1))) "tDead" v,
                      .returned (.stdVecOwned bR2
                        (((BitVec.ofNat 64 len) +
                          BitVec.ofNat 64 1).toNat) newlen.toNat)) :=
                    evalProgStmt_return vecGrowProg F _ _ _
                      hretEval
                  simp only [evalProgFunc, hbind, hbody]
                  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCk,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepBg,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepMi,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepK,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepAl,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCon,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepR1,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepKp1,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepR2,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenNew,
                    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepGd,
                    hret]
                  simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal,
                    hcon, hr1, hr2, hgd, vecGrow_bind_ok, vecGrowU64,
                    vecGrowI64, vecGrowOwned]

/-! ## N4d-iv-b2: `emplace_back` (fast/slow growth composer) -/

/-- Value-level forward for `emplace_back`: capacity decides. Fast
    (`len ≠ cap`): the frozen construct forward at `len`, length
    `len + 1` (one equation per composer `callRet`, mirroring how
    `stdVecGrowReallocFwd` threads the leaf forwards). Slow
    (`len = cap`): the realloc forward at `pos = len` (the fused
    `end()` value). -/
def stdVecEmplaceBackFwd (b : Vec32) (len cap : Nat) (x : BitVec 32) :
    Result Value :=
  if len == cap then
    stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x
  else
    (stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x).bind fun conv =>
    (vecGrowOwned conv).bind fun (b', _, _) =>
    .ok (.stdVecOwned b' (len + 1) cap)

set_option maxRecDepth 8192 in
/-- `emit_correct` for `emplace_back`: the program over the frozen
    leaves plus the proved realloc composer agrees with the capacity
    dispatch forward. Caller-side preconditions: the old triple is
    live, `len` is below the `length_error` boundary, the element
    lands in the buffer, words fit, and fuel covers the slow path
    (one `callProg` depth plus the realloc relocates). -/
theorem evalProgFunc_stdVecEmplaceBack (F : Nat) (b : Vec32) (len cap : Nat)
    (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hlenB : len < b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 2 ≤ F) :
    evalProgFunc vecGrowProg F stdVecEmplaceBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      stdVecEmplaceBackFwd b len cap x := by
  obtain ⟨F', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : F ≠ 0)
  have hbind : bindArgs stdVecEmplaceBackFunc.args
      [.stdVecOwned b len cap, .i32 x] =
      some [("t", .stdVecOwned b len cap), ("x", .i32 x)] := rfl
  have hbody : stdVecEmplaceBackFunc.body =
      (.seq (.let_ "len" (.u 64) (.vgrowLen "t"))
      (.seq (.let_ "cap" (.u 64) (.vgrowCap "t"))
      (.if_ (.une (.var "len") (.var "cap"))
        (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
        (.seq (.let_ "len1" (.u 64)
                 (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
              (.return_ (.vgrowSetLen "tF" (.var "len1")))))
        (.seq (.callRet "pos" stdVecEndName ["t"])
        (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
              (.return_ (.var "r"))))))) := rfl
  have hlen64 : len < 2 ^ 64 := Nat.lt_trans hlenB h64
  have hrt : (BitVec.ofNat 64 len).toNat = len := ofNat64_toNat _ hlen64
  have h1w : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
  have hlen1lt : len + 1 < 2 ^ 64 := by omega
  have hlen1 : ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1)).toNat =
      len + 1 := by
    rw [BitVec.toNat_add_of_lt (by rw [hrt, h1w]; exact hlen1lt), hrt, h1w]
  have ht0 : envLookup [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "t" = some (.stdVecOwned b len cap) := by simp [envLookup]
  have hlenV : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht0
  have hstepLen : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "len" (.u 64) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap), ("x", .i32 x)] =
      .ok (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlenV
  have ht1 : envLookup (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len))) "t" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup, envExtend, show ("t" : String) ≠ "len" by decide]
  have hcapV : evalExpr (.vgrowCap "t") (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len))) =
      .ok (.u64 (BitVec.ofNat 64 cap)) :=
    evalExpr_vgrowCap_some "t" _ b len cap ht1
  have hstepCap : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "cap" (.u 64) (.vgrowCap "t"))
      (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len))) =
      .ok (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hcapV
  have hlen2 : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len)))
      "cap" (.u64 (BitVec.ofNat 64 cap))) "len" =
      some (.u64 (BitVec.ofNat 64 len)) := by
    simp [envLookup, envExtend, show ("len" : String) ≠ "cap" by decide]
  have hcap2 : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len)))
      "cap" (.u64 (BitVec.ofNat 64 cap))) "cap" =
      some (.u64 (BitVec.ofNat 64 cap)) := by
    simp [envLookup, envExtend]
  have ht2 : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len)))
      "cap" (.u64 (BitVec.ofNat 64 cap))) "t" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup, envExtend,
      show ("t" : String) ≠ "cap" by decide,
      show ("t" : String) ≠ "len" by decide]
  have hx2 : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len)))
      "cap" (.u64 (BitVec.ofNat 64 cap))) "x" =
      some (.i32 x) := by
    simp [envLookup, envExtend,
      show ("x" : String) ≠ "cap" by decide,
      show ("x" : String) ≠ "len" by decide]
  have hfindCon : findFunc vecGrowProg stdVecTraitsConstructName =
      some stdVecConstructFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindEnd : findFunc vecGrowProg stdVecEndName =
      some stdVecEndFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindR : findFunc vecGrowProg stdVecGrowReallocName =
      some stdVecGrowReallocFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  by_cases hlc : len = cap
  · -- Slow path: `len = cap`, the `end()` position feeds the
    -- realloc composer via `callProg` at depth `F'`.
    have hcond : evalExpr (.une (.var "len") (.var "cap"))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        .ok (.b false) := by
      simp [evalExpr, envLookup, envExtend,
        show ("len" : String) ≠ "cap" by decide, hlc]
    have hif : evalProgStmt vecGrowProg (F' + 1)
        (.if_ (.une (.var "len") (.var "cap"))
          (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
          (.seq (.let_ "len1" (.u 64)
                   (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
                (.return_ (.vgrowSetLen "tF" (.var "len1")))))
          (.seq (.callRet "pos" stdVecEndName ["t"])
          (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
                (.return_ (.var "r")))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        evalProgStmt vecGrowProg (F' + 1)
        (.seq (.callRet "pos" stdVecEndName ["t"])
        (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
              (.return_ (.var "r"))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) :=
      evalProgStmt_if_false vecGrowProg (F' + 1) _ _ _ _ hcond
    have hargsPos : lookupArgs (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap))) ["t"] =
        some [.stdVecOwned b len cap] := by
      simp only [lookupArgs, ht2]
    have hcallEnd : evalFuncFuel (F' + 1) stdVecEndFunc
        [.stdVecOwned b len cap] = stdVecEndFwd len :=
      evalFuncFuel_stdVecEnd _ b len cap
    have hcallEnd' : evalFuncFuel (F' + 1) stdVecEndFunc
        [.stdVecOwned b len cap] = .ok (.u64 (BitVec.ofNat 64 len)) := by
      rw [hcallEnd]; rfl
    have hstepPos := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "pos"
      stdVecEndName ["t"] _ _ stdVecEndFunc (.u64 (BitVec.ofNat 64 len))
      hargsPos hfindEnd hcallEnd'
    have ht3 : envLookup (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)))
        "pos" (.u64 (BitVec.ofNat 64 len))) "t" =
        some (.stdVecOwned b len cap) := by
      simp [envLookup, envExtend,
        show ("t" : String) ≠ "pos" by decide,
        show ("t" : String) ≠ "cap" by decide,
        show ("t" : String) ≠ "len" by decide]
    have hpos3 : envLookup (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)))
        "pos" (.u64 (BitVec.ofNat 64 len))) "pos" =
        some (.u64 (BitVec.ofNat 64 len)) := by
      simp [envLookup, envExtend]
    have hx3 : envLookup (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)))
        "pos" (.u64 (BitVec.ofNat 64 len))) "x" =
        some (.i32 x) := by
      simp [envLookup, envExtend,
        show ("x" : String) ≠ "pos" by decide,
        show ("x" : String) ≠ "cap" by decide,
        show ("x" : String) ≠ "len" by decide]
    have hargsR : lookupArgs (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)))
        "pos" (.u64 (BitVec.ofNat 64 len))) ["t", "pos", "x"] =
        some [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len),
          .i32 x] := by
      simp only [lookupArgs, ht3, hpos3, hx3]
    have hSlen : (BitVec.ofNat 64 len).toNat ≤ len := Nat.le_of_eq hrt
    have hcallR : evalProgFunc vecGrowProg F' stdVecGrowReallocFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
        stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x :=
      evalProgFunc_stdVecGrowRealloc F' b len cap (BitVec.ofNat 64 len) x
        hlive hmax hSlen (Nat.le_of_lt hlenB) h64
        (by rw [hrt]; omega) (by rw [hrt]; omega)
    have hFwdSlow : stdVecEmplaceBackFwd b len cap x =
        stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x := by
      unfold stdVecEmplaceBackFwd; simp [hlc]
    cases hR : stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x with
    | error e =>
      have hcallR' : evalProgFunc vecGrowProg F' stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .error e := by rw [hcallR, hR]
      have hstepR := evalProgStmt_callProg_err vecGrowProg F' "r"
        stdVecGrowReallocName ["t", "pos", "x"] _ _ stdVecGrowReallocFunc e
        hargsR hfindR hcallR'
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCap,
        hif, evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepPos,
        evalProgStmt_seq_err _ _ _ _ _ _ hstepR]
      simp only [hFwdSlow, hR]
    | ok v =>
      have hcallR' : evalProgFunc vecGrowProg F' stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .ok v := by rw [hcallR, hR]
      have hstepR := evalProgStmt_callProg_ok vecGrowProg F' "r"
        stdVecGrowReallocName ["t", "pos", "x"] _ _ stdVecGrowReallocFunc v
        hargsR hfindR hcallR'
      have hrE : evalExpr (.var "r") (envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v) =
          .ok v := by
        simp [evalExpr, envLookup, envExtend]
      have hret : evalProgStmt vecGrowProg (F' + 1)
          (.return_ (.var "r")) (envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v) =
          .ok ((envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v), .returned v) :=
        evalProgStmt_return vecGrowProg (F' + 1) _ _ _ hrE
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCap,
        hif, evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepPos,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepR, hret]
      simp only [hFwdSlow, hR]
  · -- Fast path: `len ≠ cap`, construct at `len`, bump to `len + 1`.
    have hne64 : BitVec.ofNat 64 len ≠ BitVec.ofNat 64 cap := by
      intro hcon
      apply hlc
      have h1 := congrArg BitVec.toNat hcon
      rw [hrt, ofNat64_toNat _ hcap64] at h1
      exact h1
    have hcond : evalExpr (.une (.var "len") (.var "cap"))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        .ok (.b true) := by
      simp [evalExpr, envLookup, envExtend,
        show ("len" : String) ≠ "cap" by decide, hne64]
    have hif : evalProgStmt vecGrowProg (F' + 1)
        (.if_ (.une (.var "len") (.var "cap"))
          (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
          (.seq (.let_ "len1" (.u 64)
                   (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
                (.return_ (.vgrowSetLen "tF" (.var "len1")))))
          (.seq (.callRet "pos" stdVecEndName ["t"])
          (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
                (.return_ (.var "r")))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        evalProgStmt vecGrowProg (F' + 1)
        (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
        (.seq (.let_ "len1" (.u 64)
                 (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
              (.return_ (.vgrowSetLen "tF" (.var "len1")))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) :=
      evalProgStmt_if_true vecGrowProg (F' + 1) _ _ _ _ hcond
    have hargsCon : lookupArgs (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap))) ["t", "len", "x"] =
        some [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len),
          .i32 x] := by
      simp only [lookupArgs, ht2, hlen2, hx2]
    have hcallCon : evalFuncFuel (F' + 1) stdVecConstructFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
        stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x :=
      evalFuncFuel_stdVecConstruct (F' + 1) b len cap
        (BitVec.ofNat 64 len) x
    have hFwdFast : stdVecEmplaceBackFwd b len cap x =
        ((stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x).bind
          fun conv =>
        (vecGrowOwned conv).bind fun (b', _, _) =>
        .ok (.stdVecOwned b' (len + 1) cap)) := by
      unfold stdVecEmplaceBackFwd; simp [hlc]
    cases hcon : stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x with
    | error e =>
      have hcallCon' : evalFuncFuel (F' + 1) stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .error e := by rw [hcallCon, hcon]
      have hstepCon := evalProgStmt_callRet_err vecGrowProg (F' + 1) "tF"
        stdVecTraitsConstructName ["t", "len", "x"] _ _
        stdVecConstructFunc e hargsCon hfindCon hcallCon'
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCap,
        hif, evalProgStmt_seq_err _ _ _ _ _ _ hstepCon]
      simp only [hFwdFast, hcon, vecGrow_bind_err]
    | ok v =>
      obtain ⟨bC, rfl, hClive, hClen⟩ :=
        stdVecConstructFwd_ok _ _ _ _ _ _ hcon
      have hcallCon' : evalFuncFuel (F' + 1) stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .ok (.stdVecOwned bC len cap) := by rw [hcallCon, hcon]
      have hstepCon := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "tF"
        stdVecTraitsConstructName ["t", "len", "x"] _ _
        stdVecConstructFunc (.stdVecOwned bC len cap)
        hargsCon hfindCon hcallCon'
      have hlenF : envLookup (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap)) "len" =
          some (.u64 (BitVec.ofNat 64 len)) := by
        simp [envLookup, envExtend,
          show ("len" : String) ≠ "tF" by decide,
          show ("len" : String) ≠ "cap" by decide]
      have hlen1Eval : evalExpr
          (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap)) =
          .ok (.u64 ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1))) :=
        evalExpr_uadd_u64 _ _ _ _ _
          (evalExpr_var_hit _ _ _ hlenF) rfl
      have hstepLen1 : evalProgStmt vecGrowProg (F' + 1)
          (.let_ "len1" (.u 64)
            (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap)) =
          .ok (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1))),
          .fellThrough) := by
        rw [evalProgStmt_let_fb]
        exact evalStmtFuel_let_ _ _ _ _ _ _ hlen1Eval
      have htFret : envLookup (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))) "tF" =
          some (.stdVecOwned bC len cap) := by
        simp [envLookup, envExtend,
          show ("tF" : String) ≠ "len1" by decide]
      have hlen1E : evalExpr (.var "len1") (envExtend (envExtend
          (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))) =
          .ok (.u64 ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1))) := by
        simp [evalExpr, envLookup, envExtend]
      have hretEval : evalExpr
          (.vgrowSetLen "tF" (.var "len1")) (envExtend (envExtend
          (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))) =
          .ok (.stdVecOwned bC (len + 1) cap) := by
        have h0 : evalExpr
            (.vgrowSetLen "tF" (.var "len1")) (envExtend (envExtend
            (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("x", .i32 x)]
            "len" (.u64 (BitVec.ofNat 64 len)))
            "cap" (.u64 (BitVec.ofNat 64 cap)))
            "tF" (.stdVecOwned bC len cap))
            "len1" (.u64 ((BitVec.ofNat 64 len) +
              (BitVec.ofNat 64 1)))) =
            .ok (.stdVecOwned bC
              (((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1)).toNat) cap) :=
          evalExpr_vgrowSetLen_hit _ _ _ _ _ _ _ htFret hlen1E
        rw [hlen1] at h0; exact h0
      have hret : evalProgStmt vecGrowProg (F' + 1)
          (.return_ (.vgrowSetLen "tF" (.var "len1"))) (envExtend
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))) =
          .ok ((envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))),
            .returned (.stdVecOwned bC (len + 1) cap)) :=
        evalProgStmt_return vecGrowProg (F' + 1) _ _ _ hretEval
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCap,
        hif, evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCon,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen1, hret]
      simp only [hFwdFast, hcon, vecGrow_bind_ok, vecGrowOwned]

/-! ## N4d-iv-b2: `push_back` (forwarder into `emplace_back`) -/

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

/-- Value-level forward for `push_back`: the `emplace_back` dispatch
    forward (the discarded reference never affects the triple). -/
def stdVecPushBackFwd (b : Vec32) (len cap : Nat) (x : BitVec 32) :
    Result Value :=
  stdVecEmplaceBackFwd b len cap x

/-- `findFunc` resolves the `emplace_back` callee in the grown
    program (standalone, reused by both the value and memory
    forwarder proofs). -/
theorem findFunc_stdVecEmplaceBack :
    findFunc vecGrowProg stdVecEmplaceBackName =
      some stdVecEmplaceBackFunc := by
  unfold vecGrowProg
  rw [findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

set_option maxRecDepth 8192 in
/-- `emit_correct` for `push_back`: the single-`callProg` forwarder
    agrees with the `emplace_back` dispatch forward. Caller-side
    preconditions mirror `emplace_back`'s; fuel covers one more
    `callProg` depth (`len + 3 ≤ F`). -/
theorem evalProgFunc_stdVecPushBack (F : Nat) (b : Vec32) (len cap : Nat)
    (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hlenB : len < b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 3 ≤ F) :
    evalProgFunc vecGrowProg F stdVecPushBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      stdVecPushBackFwd b len cap x := by
  obtain ⟨F', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : F ≠ 0)
  have hF' : len + 2 ≤ F' := by omega
  have hbind : bindArgs stdVecPushBackFunc.args
      [.stdVecOwned b len cap, .i32 x] =
      some [("t", .stdVecOwned b len cap), ("x", .i32 x)] := rfl
  have hbody : stdVecPushBackFunc.body =
      (.seq (.callProg "r" stdVecEmplaceBackName ["t", "x"])
        (.return_ (.var "r"))) := rfl
  have hFwd : stdVecPushBackFwd b len cap x =
      stdVecEmplaceBackFwd b len cap x := rfl
  have ht : envLookup [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "t" = some (.stdVecOwned b len cap) := by simp [envLookup]
  have hx : envLookup [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "x" = some (.i32 x) := by
    simp [envLookup, show ("t" : String) ≠ "x" by decide]
  have hargs : lookupArgs [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      ["t", "x"] = some [.stdVecOwned b len cap, .i32 x] := by
    simp only [lookupArgs, ht, hx]
  have hcall : evalProgFunc vecGrowProg F' stdVecEmplaceBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      stdVecEmplaceBackFwd b len cap x :=
    evalProgFunc_stdVecEmplaceBack F' b len cap x hlive hmax
      hlenB h64 hcap64 hF'
  cases hR : stdVecEmplaceBackFwd b len cap x with
  | error e =>
    have hcall' : evalProgFunc vecGrowProg F' stdVecEmplaceBackFunc
        [.stdVecOwned b len cap, .i32 x] = .error e := by rw [hcall, hR]
    have hstepCall := evalProgStmt_callProg_err vecGrowProg F' "r"
      stdVecEmplaceBackName ["t", "x"] _ _ stdVecEmplaceBackFunc e
      hargs findFunc_stdVecEmplaceBack hcall'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstepCall]
    simp only [hFwd, hR]
  | ok v =>
    have hcall' : evalProgFunc vecGrowProg F' stdVecEmplaceBackFunc
        [.stdVecOwned b len cap, .i32 x] = .ok v := by rw [hcall, hR]
    have hstepCall := evalProgStmt_callProg_ok vecGrowProg F' "r"
      stdVecEmplaceBackName ["t", "x"] _ _ stdVecEmplaceBackFunc v
      hargs findFunc_stdVecEmplaceBack hcall'
    have hrE : evalExpr (.var "r")
        (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)] "r" v) =
        .ok v := by
      simp [evalExpr, envLookup, envExtend]
    have hret : evalProgStmt vecGrowProg (F' + 1)
        (.return_ (.var "r"))
        (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)] "r" v) =
        .ok ((envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "r" v), .returned v) :=
      evalProgStmt_return vecGrowProg (F' + 1) _ _ _ hrE
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCall, hret]
    simp only [hFwd, hR]
