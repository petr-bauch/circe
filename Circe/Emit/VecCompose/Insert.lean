/-
Circe.Emit.VecCompose.Insert — N7c single-element `insert` over the
frozen N4d+N7b leaves: the backward shift leaf + the aux composer.

The corpus `insert(const_iterator, T&&)` forwarder, the
`_M_insert_rval` router, and the closed `vec_insert_sum` entry live
in `Circe.Emit.VecCompose.InsertRouter` (N8b file-size split).

The fast-path shift (`move_backward` → `__copy_move_backward_a` →
`_a1` → `_a2` → `__copy_move_b`, with `__miter_base` / `__niter_wrap`
fused) is ONE canonical `Func`: the guarded `memmove` is a
descending copy walk (`stdVecBlitBackFold` in `Circe.Base` — the
top word moves first, so overlapping right-shifts are sound).
The `__copy_move_b` `%14` guard is subsumed by the trip count;
its pointer return drops (callers recompute offsets).

Iterator leaves: `plEl` (wrapping `uadd` twin of `miEl`), `eq`
(`ueq` over erased offsets); `cbegin`/`cend` reuse the
`begin`/`end` Funcs, const-`mi` reuses `minusEl`, const-`base` /
const-ctors / `__niter_wrap` reuse the iterator identity (name
stamping is the Gate's job — `evalFuncFuel` never looks at names).
-/
import Circe.Emit.Fragment
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose.Base
import Circe.Emit.VecCompose.Realloc
import Circe.Emit.VecCompose.Entry
import Circe.Emit.VecCompose.Reserve

/-! ## N7c: backward shift leaf (shells in `VecCompose.Base`) -/

/-- Decrementing a small `u64` counter is exact. -/
theorem shiftBack_dec (K : Nat) (hK : K + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (K + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 K := by
  have h1 : (BitVec.ofNat 64 (K + 1)).toNat = K + 1 := ofNat64_toNat _ hK
  have h2 : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat _ (by decide)
  have hK' : (BitVec.ofNat 64 K).toNat = K :=
    ofNat64_toNat _ (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, h1, h2, hK']
  have harg : 2 ^ 64 - 1 + (K + 1) = 2 ^ 64 + K := by omega
  rw [harg, Nat.add_comm (2 ^ 64) K, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Value-level forward for the backward shift: the descending blit
    into the same buffer (`result - n` is the Nat destination; the
    length is kept). -/
def stdVecShiftBackFwd (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) : Result Value :=
  match stdVecBlitBackFold b len
      (result.toNat - (last.toNat - first.toNat)) first.toNat
      (last.toNat - first.toNat) with
  | .error e => .error e
  | .ok b' => .ok (.stdVecOwned b' len cap)

/-- Backward blit preserves the buffer length (only `vecSet`s). -/
theorem stdVecBlitBackFold_length (b : Vec32) (len : Nat)
    (doff soff n : Nat) (b' : Vec32)
    (h : stdVecBlitBackFold b len doff soff n = .ok b') :
    b'.val.length = b.val.length := by
  induction n generalizing b doff soff with
  | zero =>
    simp only [stdVecBlitBackFold] at h
    cases h
    rfl
  | succ k ih =>
    simp only [stdVecBlitBackFold] at h
    by_cases hfree : b.freed
    · simp [hfree] at h
    · simp [hfree] at h
      by_cases hlt : soff + k < len
      · simp [hlt] at h
        cases hx : b.val[soff + k]? with
        | none =>
          simp [hx] at h
        | some x =>
          simp [hx] at h
          cases hs : vecSet b (doff + k) x with
          | error e =>
            simp [hs] at h
          | ok b1 =>
            simp [hs] at h
            have h1 := ih _ _ _ h
            have h2 := vecSet_length _ _ _ _ hs
            omega
      · simp [hlt] at h

/-- Backward blit over a live buffer stays live. -/
theorem stdVecBlitBackFold_live_of_live (b : Vec32) (len : Nat)
    (doff soff n : Nat) (b' : Vec32)
    (hlive : b.freed = false)
    (h : stdVecBlitBackFold b len doff soff n = .ok b') :
    b'.freed = false := by
  induction n generalizing b doff soff with
  | zero =>
    simp only [stdVecBlitBackFold] at h
    cases h
    exact hlive
  | succ k ih =>
    simp only [stdVecBlitBackFold] at h
    by_cases hfree : b.freed
    · simp [hfree] at h
    · simp [hfree] at h
      by_cases hlt : soff + k < len
      · simp [hlt] at h
        cases hx : b.val[soff + k]? with
        | none =>
          simp [hx] at h
        | some x =>
          simp [hx] at h
          cases hs : vecSet b (doff + k) x with
          | error e =>
            simp [hs] at h
          | ok b1 =>
            simp [hs] at h
            exact ih _ _ _ (vecSet_live _ _ _ _ hs) h
      · simp [hlt] at h

/-- Shift success preserves the `len` / `cap` components, keeps the
    block live, and preserves the buffer length. -/
theorem stdVecShiftBackFwd_ok (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (v : Value)
    (hlive : b.freed = false)
    (h : stdVecShiftBackFwd b len cap first last result = .ok v) :
    ∃ b', v = .stdVecOwned b' len cap ∧ b'.freed = false ∧
      b'.val.length = b.val.length := by
  unfold stdVecShiftBackFwd at h
  cases hbl : stdVecBlitBackFold b len
      (result.toNat - (last.toNat - first.toNat)) first.toNat
      (last.toNat - first.toNat) with
  | error e => simp [hbl] at h
  | ok b' =>
    simp [hbl] at h
    cases h
    exact ⟨_, rfl,
      stdVecBlitBackFold_live_of_live _ _ _ _ _ _ hlive hbl,
      stdVecBlitBackFold_length _ _ _ _ _ _ hbl⟩

/-- Loop environments, in let-prepend order (`doff`, `n`, `k`,
    then the `t` / `first` / `last` / `result` params): `u64` trip
    count `n`, destination `doff`, descending counter `k`. -/
def mkStdVecShiftBackEnv (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst : Vec32) : Env :=
  [("doff", .u64 doff), ("n", .u64 n),
   ("k", .u64 (BitVec.ofNat 64 k)),
   ("t", .stdVecOwned dst len cap),
   ("first", .u64 first), ("last", .u64 last),
   ("result", .u64 result)]

theorem mkStdVecShiftBackEnv_k (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftBackEnv b len cap first last result k n
      doff dst) "k" = some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkStdVecShiftBackEnv, envLookup,
    show ("k" : String) ≠ "doff" by decide,
    show ("k" : String) ≠ "n" by decide]

theorem mkStdVecShiftBackEnv_n (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftBackEnv b len cap first last result k n
      doff dst) "n" = some (.u64 n) := by
  simp [mkStdVecShiftBackEnv, envLookup,
    show ("n" : String) ≠ "doff" by decide]

theorem mkStdVecShiftBackEnv_doff (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftBackEnv b len cap first last result k n
      doff dst) "doff" = some (.u64 doff) := by
  simp [mkStdVecShiftBackEnv, envLookup]

theorem mkStdVecShiftBackEnv_t (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftBackEnv b len cap first last result k n
      doff dst) "t" = some (.stdVecOwned dst len cap) := by
  simp [mkStdVecShiftBackEnv, envLookup,
    show ("t" : String) ≠ "doff" by decide,
    show ("t" : String) ≠ "n" by decide,
    show ("t" : String) ≠ "k" by decide]

theorem mkStdVecShiftBackEnv_first (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftBackEnv b len cap first last result k n
      doff dst) "first" = some (.u64 first) := by
  simp [mkStdVecShiftBackEnv, envLookup,
    show ("first" : String) ≠ "doff" by decide,
    show ("first" : String) ≠ "n" by decide,
    show ("first" : String) ≠ "k" by decide,
    show ("first" : String) ≠ "t" by decide]

/-- Updating `k` stays in the env family. -/
theorem stdVecShiftBackEnv_update_k (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst : Vec32) (k' : Nat) :
    envUpdate (mkStdVecShiftBackEnv b len cap first last result k n
      doff dst) "k" (.u64 (BitVec.ofNat 64 k')) =
      some (mkStdVecShiftBackEnv b len cap first last result k' n
        doff dst) := by
  simp [mkStdVecShiftBackEnv, envUpdate,
    show ("k" : String) ≠ "doff" by decide,
    show ("k" : String) ≠ "n" by decide]

/-- Updating `t` stays in the env family. -/
theorem stdVecShiftBackEnv_update_t (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst dst' : Vec32) :
    envUpdate (mkStdVecShiftBackEnv b len cap first last result k n
      doff dst) "t" (.stdVecOwned dst' len cap) =
      some (mkStdVecShiftBackEnv b len cap first last result k n
        doff dst') := by
  simp [mkStdVecShiftBackEnv, envUpdate,
    show ("t" : String) ≠ "doff" by decide,
    show ("t" : String) ≠ "n" by decide,
    show ("t" : String) ≠ "k" by decide]

/-- The loop condition reads `0 < k`. -/
theorem stdVecShiftBackCond_eval (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst : Vec32) (hk64 : k < 2 ^ 64) :
    evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "k"))
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) =
      .ok (.b (decide (0 < k))) := by
  have hk := mkStdVecShiftBackEnv_k b len cap first last result k n
    doff dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) = .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hk]
  have h := evalExpr_ult_u64lit (BitVec.ofNat 64 0) (BitVec.ofNat 64 k)
    _ _ hkv
  rw [ofNat64_ult 0 _ (by decide), ofNat64_toNat k hk64] at h
  simpa using h

/-- Unfolding one backward copy step (proved once, so the loop proof
    never unfolds the well-founded fixpoint). -/
theorem stdVecBlitBackFold_step (b : Vec32) (len doff soff n : Nat) :
    stdVecBlitBackFold b len doff soff (n + 1) =
      if b.freed then .error .AssertFail
      else if soff + n < len then
        match b.val[soff + n]? with
        | none => .error .OOB
        | some x =>
          match vecSet b (doff + n) x with
          | .error e => .error e
          | .ok b' => stdVecBlitBackFold b' len doff soff n
      else .error .OOB := by
  rfl

/-- Body with a live read and a live write: decrement, copy one word,
    stay in the env family (any fuel). -/
theorem stdVecShiftBackBody_step_ok (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (K : Nat) (n doff : BitVec 64) (dst : Vec32) (x : BitVec 32)
    (dst' : Vec32)
    (hKlt : K + 1 ≤ last.toNat - first.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hlastR : last.toNat ≤ result.toNat)
    (hn : n = last - first)
    (hdoff : doff = result - n)
    (hlive : dst.freed = false)
    (hSb : last.toNat ≤ dst.val.length)
    (hDb : result.toNat ≤ dst.val.length)
    (hlen : last.toNat ≤ len)
    (hS64 : dst.val.length < 2 ^ 64)
    (hget : dst.val[first.toNat + K]? = some x)
    (hset : vecSet dst (doff.toNat + K) x = .ok dst') :
    evalStmtFuel F stdVecShiftBackBody
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) =
      .ok (mkStdVecShiftBackEnv b len cap first last result K n
        doff dst', .fellThrough) := by
  have hK64 : K + 1 < 2 ^ 64 := by omega
  have hnt : n.toNat = last.toNat - first.toNat := by
    rw [hn]; exact u64sub_toNat_exact _ _ hfirst
  have hdofft : doff.toNat = result.toNat - n.toNat := by
    rw [hdoff]; exact u64sub_toNat_exact _ _ (by omega)
  have hdec : BitVec.ofNat 64 (K + 1) - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 K := shiftBack_dec K hK64
  have hsidx : (first + BitVec.ofNat 64 K).toNat =
      first.toNat + K := by
    rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hdidx : (doff + BitVec.ofNat 64 K).toNat =
      doff.toNat + K := by
    rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hkL := mkStdVecShiftBackEnv_k b len cap first last result
    (K + 1) n doff dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 (K + 1))) := by
    simp [evalExpr, hkL]
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hdece : evalExpr (.usub (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
    have h := evalExpr_usub_u64u64 _ _ _ _ _ hkv hlit1
    rwa [hdec] at h
  have hasg := evalStmtFuel_assign F _ _ _ _ _ hdece
    (stdVecShiftBackEnv_update_k b len cap first last result (K + 1)
      n doff dst K)
  have hfirstv : evalExpr (.var "first")
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 first) := by
    have h := mkStdVecShiftBackEnv_first b len cap first last
      result K n doff dst
    simp [evalExpr, h]
  have hdoffv : evalExpr (.var "doff")
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 doff) := by
    have h := mkStdVecShiftBackEnv_doff b len cap first last
      result K n doff dst
    simp [evalExpr, h]
  have hkv' : evalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
    have h := mkStdVecShiftBackEnv_k b len cap first last result K
      n doff dst
    simp [evalExpr, h]
  have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 (first + BitVec.ofNat 64 K)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv'
  have hdidxe : evalExpr (.uadd (.var "doff") (.var "k"))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 (doff + BitVec.ofNat 64 K)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hdoffv hkv'
  have hget' : dst.val[(first + BitVec.ofNat 64 K).toNat]? =
      some x := by
    rw [hsidx]; exact hget
  have hlt : (first + BitVec.ofNat 64 K).toNat < len := by
    rw [hsidx]; omega
  have hset' : vecSet dst (doff + BitVec.ofNat 64 K).toNat x =
      .ok dst' := by
    rw [hdidx]; exact hset
  have hd := mkStdVecShiftBackEnv_t b len cap first last result K n
    doff dst
  have hat : evalExpr
      (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.i32 x) :=
    evalExpr_vgrowAt_some "t" _ _ dst len cap _ _ hd hsidxe
      hlive hget' hlt
  have hsetF : evalStmtFuel F
      (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
        (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) =
      .ok (mkStdVecShiftBackEnv b len cap first last result K n
        doff dst', .fellThrough) :=
    evalStmtFuel_vgrowSet F _ _ _ _ _ _ _ _ _ _ _ hdidxe hat hd
      hset'
      (stdVecShiftBackEnv_update_t b len cap first last result K n
        doff dst dst')
  exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hasg).trans hsetF

/-- Body with a failed step: the decrement succeeds, the `vgrowSet`
    error is loud (any fuel). -/
theorem stdVecShiftBackBody_step_err (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (K : Nat) (n doff : BitVec 64) (dst : Vec32) (e : Panic)
    (hK64 : K + 1 < 2 ^ 64)
    (herr : evalStmtFuel F
      (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
        (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .error e) :
    evalStmtFuel F stdVecShiftBackBody
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .error e := by
  have hkL := mkStdVecShiftBackEnv_k b len cap first last result
    (K + 1) n doff dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 (K + 1))) := by
    simp [evalExpr, hkL]
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hdece : evalExpr (.usub (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
    have h := evalExpr_usub_u64u64 _ _ _ _ _ hkv hlit1
    rwa [shiftBack_dec K hK64] at h
  have hasg := evalStmtFuel_assign F _ _ _ _ _ hdece
    (stdVecShiftBackEnv_update_k b len cap first last result (K + 1)
      n doff dst K)
  have hseq : evalStmtFuel F stdVecShiftBackBody
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) =
      evalStmtFuel F
        (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
          (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
        (mkStdVecShiftBackEnv b len cap first last result K n doff
          dst) :=
    evalStmtFuel_seq_fallthrough F _ _ _ _ hasg
  exact hseq.trans herr

/-- Loop correctness: copies the remaining suffix top-down, exits
    with `k = 0` (fuel-generalized; the `+1` absorbs the final exit
    iteration). -/
theorem stdVecShiftBackWhile_correct (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64)
    (F k : Nat) (n doff : BitVec 64) (dst : Vec32)
    (hk : k ≤ last.toNat - first.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hlastR : last.toNat ≤ result.toNat)
    (hn : n = last - first)
    (hdoff : doff = result - n)
    (hlive : dst.freed = false)
    (hSb : last.toNat ≤ dst.val.length)
    (hDb : result.toNat ≤ dst.val.length)
    (hlen : last.toNat ≤ len)
    (hS64 : dst.val.length < 2 ^ 64)
    (hF : k + 1 ≤ F) :
    evalStmtFuel F stdVecShiftBackWhile
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) =
      match stdVecBlitBackFold dst len doff.toNat first.toNat k with
      | .error e => .error e
      | .ok dst' =>
        .ok (mkStdVecShiftBackEnv b len cap first last result 0 n
          doff dst', .fellThrough) := by
  induction F generalizing k dst with
  | zero => omega
  | succ F ih =>
    have hnt : n.toNat = last.toNat - first.toNat := by
      rw [hn]; exact u64sub_toNat_exact _ _ hfirst
    have hdofft : doff.toNat = result.toNat - n.toNat := by
      rw [hdoff]; exact u64sub_toNat_exact _ _ (by omega)
    have hk64 : k < 2 ^ 64 := by omega
    by_cases hlt : 0 < k
    · obtain ⟨K, hK⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
      subst hK
      have hcond : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "k"))
          (mkStdVecShiftBackEnv b len cap first last result (K + 1)
            n doff dst) = .ok (.b true) := by
        have h := stdVecShiftBackCond_eval b len cap first last
          result (K + 1) n doff dst (by omega)
        simpa using h
      have hunfold := stdVecBlitBackFold_step dst len doff.toNat
        first.toNat K
      have hsoff : first.toNat + K < len := by omega
      cases hget : dst.val[first.toNat + K]? with
      | none =>
        have hsidx : (first + BitVec.ofNat 64 K).toNat =
            first.toNat + K := by
          rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        have hdidx : (doff + BitVec.ofNat 64 K).toNat =
            doff.toNat + K := by
          rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        have hkv' : evalExpr (.var "k")
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
          have h := mkStdVecShiftBackEnv_k b len cap first last
            result K n doff dst
          simp [evalExpr, h]
        have hfirstv : evalExpr (.var "first")
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 first) := by
          have h := mkStdVecShiftBackEnv_first b len cap first last
            result K n doff dst
          simp [evalExpr, h]
        have hdoffv : evalExpr (.var "doff")
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 doff) := by
          have h := mkStdVecShiftBackEnv_doff b len cap first last
            result K n doff dst
          simp [evalExpr, h]
        have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 (first + BitVec.ofNat 64 K)) :=
          evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv'
        have hdidxe : evalExpr (.uadd (.var "doff") (.var "k"))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 (doff + BitVec.ofNat 64 K)) :=
          evalExpr_uadd_u64 _ _ _ _ _ hdoffv hkv'
        have hget' : dst.val[(first + BitVec.ofNat 64 K).toNat]? =
            none := by
          rw [hsidx]; exact hget
        have hatE : evalExpr
            (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .error .OOB := by
          have hd := mkStdVecShiftBackEnv_t b len cap first last
            result K n doff dst
          exact evalExpr_vgrowAt_oob_miss "t" _ _ dst len cap _ hd
            hsidxe hlive hget'
        have herr : evalStmtFuel F
            (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
              (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .error .OOB := by
          have hd := mkStdVecShiftBackEnv_t b len cap first last
            result K n doff dst
          cases F <;>
            simp [evalStmtFuel, evalStmtZero, evalStmtWith, hdidxe,
              hatE]
        have hbody := stdVecShiftBackBody_step_err F b len cap
          first last result K n doff dst .OOB (by omega) herr
        have hstep : evalStmtFuel (F + 1) stdVecShiftBackWhile
            (mkStdVecShiftBackEnv b len cap first last result (K + 1)
              n doff dst) = .error .OOB := by
          simp [stdVecShiftBackWhile, evalStmtFuel,
            evalStmtSuccHandler, evalStmtWith, hcond, hbody]
        rw [hstep, hunfold]
        simp [hlive, hsoff, hget]
      | some x =>
        cases hset : vecSet dst (doff.toNat + K) x with
        | error e =>
          have hsidx : (first + BitVec.ofNat 64 K).toNat =
              first.toNat + K := by
            rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          have hdidx : (doff + BitVec.ofNat 64 K).toNat =
              doff.toNat + K := by
            rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          have hkv' : evalExpr (.var "k")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
            have h := mkStdVecShiftBackEnv_k b len cap first last
              result K n doff dst
            simp [evalExpr, h]
          have hfirstv : evalExpr (.var "first")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 first) := by
            have h := mkStdVecShiftBackEnv_first b len cap first last
              result K n doff dst
            simp [evalExpr, h]
          have hdoffv : evalExpr (.var "doff")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 doff) := by
            have h := mkStdVecShiftBackEnv_doff b len cap first last
              result K n doff dst
            simp [evalExpr, h]
          have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 (first + BitVec.ofNat 64 K)) :=
            evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv'
          have hdidxe : evalExpr (.uadd (.var "doff") (.var "k"))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 (doff + BitVec.ofNat 64 K)) :=
            evalExpr_uadd_u64 _ _ _ _ _ hdoffv hkv'
          have hget' : dst.val[(first + BitVec.ofNat 64 K).toNat]? =
              some x := by
            rw [hsidx]; exact hget
          have hltlen : (first + BitVec.ofNat 64 K).toNat < len := by
            rw [hsidx]; omega
          have hd := mkStdVecShiftBackEnv_t b len cap first last
            result K n doff dst
          have hat : evalExpr
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.i32 x) :=
            evalExpr_vgrowAt_some "t" _ _ dst len cap _ _ hd hsidxe
              hlive hget' hltlen
          have hset' : vecSet dst (doff + BitVec.ofNat 64 K).toNat
              x = .error e := by
            rw [hdidx]; exact hset
          have herr : evalStmtFuel F
              (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
                (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .error e := by
            exact evalStmtFuel_vgrowSet_err F _ _ _ _ _ _ _ _ _ _
              hdidxe hat hd hset'
          have hbody := stdVecShiftBackBody_step_err F b len cap
            first last result K n doff dst e (by omega) herr
          have hstep : evalStmtFuel (F + 1) stdVecShiftBackWhile
              (mkStdVecShiftBackEnv b len cap first last result (K + 1)
                n doff dst) = .error e := by
            simp [stdVecShiftBackWhile, evalStmtFuel,
              evalStmtSuccHandler, evalStmtWith, hcond, hbody]
          rw [hstep, hunfold]
          simp [hlive, hsoff, hget, hset]
        | ok dst' =>
          have hbody := stdVecShiftBackBody_step_ok F b len cap
            first last result K n doff dst x dst' (by omega) hfirst
            hlastR hn hdoff hlive hSb hDb hlen hS64 hget hset
          have hstep : evalStmtFuel (F + 1) stdVecShiftBackWhile
              (mkStdVecShiftBackEnv b len cap first last result (K + 1)
                n doff dst) =
              evalStmtFuel F stdVecShiftBackWhile
                (mkStdVecShiftBackEnv b len cap first last result K n
                  doff dst') := by
            simp [stdVecShiftBackWhile, evalStmtFuel,
              evalStmtSuccHandler, evalStmtWith, hcond, hbody]
          have hDbK : doff.toNat + K < dst.val.length := by omega
          have hbD' : dst' =
              ⟨dst.val.set (doff.toNat + K) x, false⟩ := by
            have h := vecSet_ok dst _ x hlive hDbK
            rw [hset] at h
            simpa using h
          have hlenD' : dst'.val.length = dst.val.length := by
            simp [hbD', List.length_set]
          have hfreeD' : dst'.freed = false := by rw [hbD']
          rw [hstep, hunfold]
          simp only [hlive, hsoff, hget, hset]
          exact ih K dst' (by omega) hfreeD'
            (by rw [hlenD']; exact hSb)
            (by rw [hlenD']; exact hDb)
            (by rw [hlenD']; exact hS64) (by omega)
    · have hkk : k = 0 := by omega
      subst hkk
      have hk64c : (0 : Nat) < 2 ^ 64 := by decide
      have hcondF : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "k"))
          (mkStdVecShiftBackEnv b len cap first last result 0 n
            doff dst) = .ok (.b false) := by
        have h := stdVecShiftBackCond_eval b len cap first last
          result 0 n doff dst hk64c
        simpa using h
      have hzero : stdVecBlitBackFold dst len doff.toNat first.toNat
          0 = .ok dst := rfl
      have hLHS : evalStmtFuel (F + 1) stdVecShiftBackWhile
          (mkStdVecShiftBackEnv b len cap first last result 0 n doff
            dst) =
          .ok (mkStdVecShiftBackEnv b len cap first last result 0 n
            doff dst, .fellThrough) := by
        simp [stdVecShiftBackWhile, evalStmtFuel,
          evalStmtSuccHandler, evalStmtWith, hcondF]
      have hRHS : (match stdVecBlitBackFold dst len doff.toNat
          first.toNat 0 with
        | Except.error e => Except.error e
        | Except.ok dst' =>
          Except.ok (mkStdVecShiftBackEnv b len cap first last
            result 0 n doff dst', Outcome.fellThrough)) =
          .ok (mkStdVecShiftBackEnv b len cap first last result 0 n
            doff dst, Outcome.fellThrough) := by
        rw [hzero]
      exact hLHS.trans hRHS.symm

/-- `emit_correct` for the backward shift (fuel-generalized; the fuel
    hypothesis is the slice's dynamic-length side condition). -/
theorem evalFuncFuel_stdVecShiftBack (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (hfirst : first.toNat ≤ last.toNat)
    (hlastR : last.toNat ≤ result.toNat)
    (hlive : b.freed = false)
    (hSb : last.toNat ≤ b.val.length)
    (hDb : result.toNat ≤ b.val.length)
    (hlen : last.toNat ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat + 1 ≤ F) :
    evalFuncFuel F stdVecShiftBackFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result] =
      stdVecShiftBackFwd b len cap first last result := by
  have hX : (last - first).toNat = last.toNat - first.toNat :=
    u64sub_toNat_exact _ _ hfirst
  have hnk : last - first =
      BitVec.ofNat 64 (last.toNat - first.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [hX, ofNat64_toNat _ (by omega)]
  have hbind : bindArgs stdVecShiftBackFunc.args
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result] =
      some [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] := rfl
  have hbody : stdVecShiftBackFunc.body =
      .seq (.let_ "k" (.u 64) (.usub (.var "last") (.var "first")))
      (.seq (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      (.seq (.let_ "doff" (.u 64)
              (.usub (.var "result") (.var "n")))
      (.seq stdVecShiftBackWhile
        (.return_ (.var "t"))))) := rfl
  have hlast0 : evalExpr (.var "last")
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 last) := by
    simp [evalExpr, envLookup,
      show ("last" : String) ≠ "t" by decide,
      show ("last" : String) ≠ "first" by decide]
  have hfirst0 : evalExpr (.var "first")
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 first) := by
    simp [evalExpr, envLookup,
      show ("first" : String) ≠ "t" by decide]
  have hnEval0 : evalExpr (.usub (.var "last") (.var "first"))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (BitVec.ofNat 64 (last.toNat - first.toNat))) := by
    have h := evalExpr_usub_u64u64 _ _ _ _ _ hlast0 hfirst0
    rwa [hnk] at h
  have e1 : evalStmtFuel F
      (.let_ "k" (.u 64) (.usub (.var "last") (.var "first")))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok ([("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)], .fellThrough) :=
    evalStmtFuel_let_ F "k" (.u 64)
      (.usub (.var "last") (.var "first"))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (.u64 (BitVec.ofNat 64 (last.toNat - first.toNat))) hnEval0
  have hlast1 : evalExpr (.var "last")
      [(("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 last) := by
    simp [evalExpr, envLookup,
      show ("last" : String) ≠ "k" by decide,
      show ("last" : String) ≠ "t" by decide,
      show ("last" : String) ≠ "first" by decide]
  have hfirst1 : evalExpr (.var "first")
      [(("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 first) := by
    simp [evalExpr, envLookup,
      show ("first" : String) ≠ "k" by decide,
      show ("first" : String) ≠ "t" by decide]
  have hnEval1 : evalExpr (.usub (.var "last") (.var "first"))
      [(("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (last - first)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hlast1 hfirst1
  have e2 : evalStmtFuel F
      (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      [(("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok ([(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)], .fellThrough) :=
    evalStmtFuel_let_ F "n" (.u 64)
      (.usub (.var "last") (.var "first"))
      [(("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (.u64 (last - first)) hnEval1
  have hres : evalExpr (.var "result")
      [(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 result) := by
    simp [evalExpr, envLookup,
      show ("result" : String) ≠ "n" by decide,
      show ("result" : String) ≠ "k" by decide,
      show ("result" : String) ≠ "t" by decide,
      show ("result" : String) ≠ "first" by decide,
      show ("result" : String) ≠ "last" by decide]
  have hnV : evalExpr (.var "n")
      [(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (last - first)) := by
    simp [evalExpr, envLookup]
  have hdoffEval : evalExpr (.usub (.var "result") (.var "n"))
      [(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (result - (last - first))) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hres hnV
  have e3 : evalStmtFuel F
      (.let_ "doff" (.u 64) (.usub (.var "result") (.var "n")))
      [(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (mkStdVecShiftBackEnv b len cap first last result
        (last.toNat - first.toNat) (last - first)
        (result - (last - first)) b, .fellThrough) :=
    evalStmtFuel_let_ F "doff" (.u 64)
      (.usub (.var "result") (.var "n"))
      [(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (.u64 (result - (last - first))) hdoffEval
  have hF0 : last.toNat - first.toNat + 1 ≤ F := hF
  have hdofft0 : result.toNat - (last.toNat - first.toNat) =
      (result - (last - first)).toNat := by
    rw [u64sub_toNat_exact _ _ (by omega), hX]
  have hloop0 := stdVecShiftBackWhile_correct b len cap
    first last result F (last.toNat - first.toNat) (last - first)
    (result - (last - first)) b (Nat.le_refl _) hfirst hlastR rfl
    rfl hlive hSb hDb hlen hS64 hF0
  cases hblit : stdVecBlitBackFold b len
      ((result - (last - first)).toNat) first.toNat
      (last.toNat - first.toNat) with
  | error e =>
    have hloopE : evalStmtFuel F stdVecShiftBackWhile
        (mkStdVecShiftBackEnv b len cap first last result
          (last.toNat - first.toNat) (last - first)
          (result - (last - first)) b) = .error e := by
      rw [hblit] at hloop0
      exact hloop0
    have hfwd : stdVecShiftBackFwd b len cap first last result =
        .error e := by
      simp only [stdVecShiftBackFwd, hdofft0, hblit]
    have hstmt : evalStmtFuel F stdVecShiftBackFunc.body
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] = .error e := by
      rw [hbody]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ e1).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ e2).trans
          ((evalStmtFuel_seq_fallthrough F _ _ _ _ e3).trans
            (evalStmtFuel_seq_err F _ _ _ _ hloopE)))
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  | ok b' =>
    have hloopO : evalStmtFuel F stdVecShiftBackWhile
        (mkStdVecShiftBackEnv b len cap first last result
          (last.toNat - first.toNat) (last - first)
          (result - (last - first)) b) =
        .ok (mkStdVecShiftBackEnv b len cap first last result 0
          (last - first) (result - (last - first)) b',
          .fellThrough) := by
      rw [hblit] at hloop0
      exact hloop0
    have hret : envLookup
        (mkStdVecShiftBackEnv b len cap first last result 0
          (last - first) (result - (last - first)) b') "t" =
        some (.stdVecOwned b' len cap) :=
      mkStdVecShiftBackEnv_t b len cap first last result 0
        (last - first) (result - (last - first)) b'
    have hvar : evalExpr (.var "t")
        (mkStdVecShiftBackEnv b len cap first last result 0
          (last - first) (result - (last - first)) b') =
        .ok (.stdVecOwned b' len cap) := by
      simp [evalExpr, hret]
    have hfwd : stdVecShiftBackFwd b len cap first last result =
        .ok (.stdVecOwned b' len cap) := by
      simp only [stdVecShiftBackFwd, hdofft0, hblit]
    have hstmt : evalStmtFuel F stdVecShiftBackFunc.body
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] =
        .ok (mkStdVecShiftBackEnv b len cap first last result 0
          (last - first) (result - (last - first)) b',
          .returned (.stdVecOwned b' len cap)) := by
      rw [hbody]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ e1).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ e2).trans
          ((evalStmtFuel_seq_fallthrough F _ _ _ _ e3).trans
            ((evalStmtFuel_seq_fallthrough F _ _ _ _ hloopO).trans
              (evalStmtFuel_return F _ _ _ hvar))))
    simp [evalFuncFuel, hbind, hstmt, hfwd]

/-! ## N7c: `insert` composers -/

/-- `ofNat` survives decrementing a positive small `u64`. -/
theorem ofNat_sub_one (m : Nat) (h64 : m < 2 ^ 64) (h1 : 1 ≤ m) :
    BitVec.ofNat 64 m - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (m - 1) := by
  have h1' : (BitVec.ofNat 64 m).toNat = m := ofNat64_toNat _ h64
  have h2 : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat _ (by decide)
  have hm : (BitVec.ofNat 64 (m - 1)).toNat = m - 1 :=
    ofNat64_toNat _ (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, h1', h2, hm]
  have harg : 2 ^ 64 - 1 + m = 2 ^ 64 + (m - 1) := by omega
  rw [harg, Nat.add_comm (2 ^ 64) (m - 1), Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Value-level forward for `_M_insert_aux`: sequential `Result`
    binds over the frozen leaf forwards (each bind is one composer
    `callRet`). -/
def stdVecInsertAuxFwd (b : Vec32) (len cap : Nat) (pos : BitVec 64)
    (x : BitVec 32) : Result Value :=
  (stdVecGrowIndexFwd b len (BitVec.ofNat 64 (len - 1))).bind fun lwv =>
  (vecGrowI32 lwv).bind fun lw =>
  (stdVecConstructFwd b len cap (BitVec.ofNat 64 len) lw).bind fun c1v =>
  (vecGrowOwned c1v).bind fun (b1, _, _) =>
  (stdVecShiftBackFwd b1 (len + 1) cap pos (BitVec.ofNat 64 len)
    (BitVec.ofNat 64 (len + 1))).bind fun s3v =>
  (vecGrowOwned s3v).bind fun (b3, _, _) =>
  stdVecConstructFwd b3 (len + 1) cap pos x

/-- `emit_correct` for `_M_insert_aux`: the program over the frozen
    leaves agrees with the composer forward. Caller-side
    preconditions: the triple is live with room for one more word,
    the position is in range, and fuel covers the shift. -/
theorem evalProgFunc_stdVecInsertAux (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hbuf : len + 1 ≤ b.val.length)
    (hpos : pos.toNat ≤ len)
    (hlen1 : 1 ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : len + 1 ≤ F) :
    evalProgFunc vecGrowProg F stdVecInsertAuxFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecInsertAuxFwd b len cap pos x := by
  have hlen64 : len < 2 ^ 64 := by omega
  have hlen1p64 : len + 1 < 2 ^ 64 := by omega
  have hlenT : (BitVec.ofNat 64 len).toNat = len :=
    ofNat64_toNat _ hlen64
  have hlenp1T : (BitVec.ofNat 64 (len + 1)).toNat = len + 1 :=
    ofNat64_toNat _ hlen1p64
  have hbind : bindArgs stdVecInsertAuxFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      some [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] := rfl
  have hbody : stdVecInsertAuxFunc.body =
      (.seq (.let_ "len" (.u 64) (.vgrowLen "t"))
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
        (.return_ (.var "t4")))))))))) := rfl
  have hfindC : findFunc vecGrowProg stdVecTraitsConstructName =
      some stdVecConstructFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindS : findFunc vecGrowProg stdVecShiftBackName =
      some stdVecShiftBackFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have ht0 : envLookup [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos), ("x", .i32 x)] "t" =
      some (.stdVecOwned b len cap) := by simp [envLookup]
  have hlenE : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht0
  have elen : evalProgStmt vecGrowProg F
      (.let_ "len" (.u 64) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok ([("len", .u64 (BitVec.ofNat 64 len)),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)], .fellThrough) :=
    (evalProgStmt_let_fb _ _ _ _ _ _).trans
      (evalStmtFuel_let_ F "len" (.u 64) (.vgrowLen "t")
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (.u64 (BitVec.ofNat 64 len)) hlenE)
  have hlenV : evalExpr (.var "len")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    simp [evalExpr, envLookup]
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hlastE : evalExpr
      (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len - BitVec.ofNat 64 1)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hlenV hlit1
  have hlastB : BitVec.ofNat 64 len - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (len - 1) :=
    ofNat_sub_one len hlen64 hlen1
  have hlastT : (BitVec.ofNat 64 (len - 1)).toNat = len - 1 :=
    ofNat64_toNat _ (by omega)
  have elast : evalProgStmt vecGrowProg F
      (.let_ "last" (.u 64)
        (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok ([(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
        (("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)], .fellThrough) := by
    rw [evalProgStmt_let_fb, ← hlastB]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlastE
  cases hget0 : b.val[len - 1]? with
  | none =>
    have hget' : b.val[(BitVec.ofNat 64 (len - 1)).toNat]? = none := by
      rw [hlastT]; exact hget0
    have htL : envLookup
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] "t" =
        some (.stdVecOwned b len cap) := by
      simp [envLookup,
        show ("t" : String) ≠ "last" by decide,
        show ("t" : String) ≠ "len" by decide]
    have hlastV : evalExpr (.var "last")
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] =
        .ok (.u64 (BitVec.ofNat 64 (len - 1))) := by
      simp [evalExpr, envLookup]
    have hlwE : evalExpr (.vgrowAt "t" (.var "last"))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] = .error .OOB :=
      evalExpr_vgrowAt_oob_miss "t" _ _ b len cap _ htL hlastV
        hlive hget'
    have elw : evalProgStmt vecGrowProg F
        (.let_ "lw" (.i 32) (.vgrowAt "t" (.var "last")))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] = .error .OOB :=
      (evalProgStmt_let_fb _ _ _ _ _ _).trans
        (evalStmtFuel_let_err F _ _ _ _ _ hlwE)
    have hidxE : stdVecGrowIndexFwd b len
        (BitVec.ofNat 64 (len - 1)) = .error .OOB := by
      have hnt : (BitVec.ofNat 64 (len - 1)).toNat = len - 1 :=
        hlastT
      simp [stdVecGrowIndexFwd, hlive, hnt, hget0]
    have hfwd : stdVecInsertAuxFwd b len cap pos x = .error .OOB := by
      simp only [stdVecInsertAuxFwd, hidxE, vecGrow_bind_err]
    have hstmt : evalProgStmt vecGrowProg F
        stdVecInsertAuxFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] = .error .OOB := by
      rw [hbody]
      exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
        ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elast).trans
          (evalProgStmt_seq_err _ _ _ _ _ _ elw))
    simp only [evalProgFunc, hbind, hstmt, hfwd]
  | some w =>
    have hget' : b.val[(BitVec.ofNat 64 (len - 1)).toNat]? = some w := by
      rw [hlastT]; exact hget0
    have hlt : (BitVec.ofNat 64 (len - 1)).toNat < len := by
      rw [hlastT]; omega
    have htL : envLookup
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] "t" =
        some (.stdVecOwned b len cap) := by
      simp [envLookup,
        show ("t" : String) ≠ "last" by decide,
        show ("t" : String) ≠ "len" by decide]
    have hlastV : evalExpr (.var "last")
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] =
        .ok (.u64 (BitVec.ofNat 64 (len - 1))) := by
      simp [evalExpr, envLookup]
    have hlw : evalExpr (.vgrowAt "t" (.var "last"))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] = .ok (.i32 w) :=
      evalExpr_vgrowAt_some "t" _ _ b len cap _ _ htL hlastV hlive
        hget' hlt
    have elw : evalProgStmt vecGrowProg F
        (.let_ "lw" (.i 32) (.vgrowAt "t" (.var "last")))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] =
        .ok ([(("lw", .i32 w)),
          (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)], .fellThrough) :=
      (evalProgStmt_let_fb _ _ _ _ _ _).trans
        (evalStmtFuel_let_ F "lw" (.i 32) (.vgrowAt "t" (.var "last"))
          [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (.i32 w) hlw)
    have hlt' : len - 1 < len := by omega
    have hidx : stdVecGrowIndexFwd b len
        (BitVec.ofNat 64 (len - 1)) = .ok (.i32 w) := by
      simp [stdVecGrowIndexFwd, hlive, hlastT, hget0, hlt']
    have hargsT1 : lookupArgs
        [(("lw", .i32 w)),
          (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        ["t", "len", "lw"] =
        some [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len),
          .i32 w] := by
      simp [lookupArgs, envLookup,
        show ("t" : String) ≠ "lw" by decide,
        show ("t" : String) ≠ "last" by decide,
        show ("t" : String) ≠ "len" by decide,
        show ("len" : String) ≠ "lw" by decide,
        show ("len" : String) ≠ "last" by decide]
    have hcallC1 : evalFuncFuel F stdVecConstructFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 w] =
        stdVecConstructFwd b len cap (BitVec.ofNat 64 len) w :=
      evalFuncFuel_stdVecConstruct F b len cap
        (BitVec.ofNat 64 len) w
    cases hc1 : stdVecConstructFwd b len cap
        (BitVec.ofNat 64 len) w with
    | error e =>
      have hcallC1' : evalFuncFuel F stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len),
            .i32 w] = .error e := by
        rw [hcallC1, hc1]
      have hstepT1 := evalProgStmt_callRet_err vecGrowProg F "t1"
        stdVecTraitsConstructName ["t", "len", "lw"] _ _
        stdVecConstructFunc e hargsT1 hfindC hcallC1'
      have hfwd : stdVecInsertAuxFwd b len cap pos x = .error e := by
        simp only [stdVecInsertAuxFwd, hidx, vecGrow_bind_ok,
          vecGrowI32, hc1, vecGrow_bind_err]
      have hstmt : evalProgStmt vecGrowProg F
          stdVecInsertAuxFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] = .error e := by
        rw [hbody]
        exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
          ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elast).trans
            ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elw).trans
              (evalProgStmt_seq_err _ _ _ _ _ _ hstepT1)))
      simp only [evalProgFunc, hbind, hstmt, hfwd]
    | ok c1v =>
      obtain ⟨b1, hbc1, hlive1, hlenB1⟩ :=
        stdVecConstructFwd_ok b len cap (BitVec.ofNat 64 len) w
          c1v hc1
      have hstepT1 := evalProgStmt_callRet_ok vecGrowProg F "t1"
        stdVecTraitsConstructName ["t", "len", "lw"] _ _
        stdVecConstructFunc c1v hargsT1 hfindC
        (by rw [hcallC1, hc1])
      have hlenV1 : evalExpr (.var "len")
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.u64 (BitVec.ofNat 64 len)) := by
        simp [evalExpr, envLookup,
          show ("len" : String) ≠ "t1" by decide,
          show ("len" : String) ≠ "lw" by decide,
          show ("len" : String) ≠ "last" by decide]
      have hlit1' : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.u64 (BitVec.ofNat 64 1)) := by
        simp [evalExpr, litVal]
      have hlenp1E : evalExpr
          (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.u64 (BitVec.ofNat 64 (len + 1))) := by
        have h := evalExpr_uadd_u64 _ _ _ _ _ hlenV1 hlit1'
        rwa [ofNat64_add_one len] at h
      have elenp1 : evalProgStmt vecGrowProg F
          (.let_ "lenp1" (.u 64)
            (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok ([(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)], .fellThrough) :=
        (evalProgStmt_let_fb _ _ _ _ _ _).trans
          (evalStmtFuel_let_ F "lenp1" (.u 64)
            (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
            [(("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (.u64 (BitVec.ofNat 64 (len + 1))) hlenp1E)
      have ht1V : evalExpr (.var "t1")
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] = .ok c1v := by
        simp [evalExpr, envLookup,
          show ("t1" : String) ≠ "lenp1" by decide]
      have hlenp1V : evalExpr (.var "lenp1")
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.u64 (BitVec.ofNat 64 (len + 1))) := by
        simp [evalExpr, envLookup]
      have ht2E : evalExpr (.vgrowSetLen "t1" (.var "lenp1"))
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.stdVecOwned b1 (len + 1) cap) := by
        have ht1L : envLookup
            [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
              (("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] "t1" = some c1v := by
          simp [envLookup,
            show ("t1" : String) ≠ "lenp1" by decide]
        have ht1L' : envLookup
            [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
              (("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] "t1" =
            some (.stdVecOwned b1 len cap) := by
          rw [← hbc1]; exact ht1L
        have h := evalExpr_vgrowSetLen_hit "t1" _ _ b1 len cap
          (BitVec.ofNat 64 (len + 1)) ht1L' hlenp1V
        rwa [hlenp1T] at h
      have et2 : evalProgStmt vecGrowProg F
          (.let_ "t2" (.vecBlock)
            (.vgrowSetLen "t1" (.var "lenp1")))
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok ([(("t2", .stdVecOwned b1 (len + 1) cap)),
            (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)], .fellThrough) :=
        (evalProgStmt_let_fb _ _ _ _ _ _).trans
          (evalStmtFuel_let_ F "t2" (.vecBlock)
            (.vgrowSetLen "t1" (.var "lenp1"))
            [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
              (("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (.stdVecOwned b1 (len + 1) cap) ht2E)
      have hargsT3 : lookupArgs
          [(("t2", .stdVecOwned b1 (len + 1) cap)),
            (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          ["t2", "pos", "len", "lenp1"] =
          some [.stdVecOwned b1 (len + 1) cap, .u64 pos,
            .u64 (BitVec.ofNat 64 len),
            .u64 (BitVec.ofNat 64 (len + 1))] := by
        simp [lookupArgs, envLookup,
          show ("pos" : String) ≠ "t2" by decide,
          show ("pos" : String) ≠ "lenp1" by decide,
          show ("pos" : String) ≠ "t1" by decide,
          show ("pos" : String) ≠ "lw" by decide,
          show ("pos" : String) ≠ "last" by decide,
          show ("pos" : String) ≠ "len" by decide,
          show ("pos" : String) ≠ "t" by decide,
          show ("len" : String) ≠ "t2" by decide,
          show ("len" : String) ≠ "lenp1" by decide,
          show ("len" : String) ≠ "t1" by decide,
          show ("len" : String) ≠ "lw" by decide,
          show ("len" : String) ≠ "last" by decide,
          show ("lenp1" : String) ≠ "t2" by decide]
      have hcallS : evalFuncFuel F stdVecShiftBackFunc
          [.stdVecOwned b1 (len + 1) cap, .u64 pos,
            .u64 (BitVec.ofNat 64 len),
            .u64 (BitVec.ofNat 64 (len + 1))] =
          stdVecShiftBackFwd b1 (len + 1) cap pos
            (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len + 1)) :=
        evalFuncFuel_stdVecShiftBack F b1 (len + 1) cap pos
          (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len + 1))
          (by rw [hlenT]; exact hpos)
          (by rw [hlenT, hlenp1T]; omega)
          hlive1
          (by rw [hlenT]; omega)
          (by rw [hlenp1T]; omega)
          (by rw [hlenT]; omega)
          (by rw [hlenB1]; exact hS64)
          (by rw [hlenT]; omega)
      cases hs3 : stdVecShiftBackFwd b1 (len + 1) cap pos
          (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len + 1)) with
      | error e =>
        have hcallS' : evalFuncFuel F stdVecShiftBackFunc
            [.stdVecOwned b1 (len + 1) cap, .u64 pos,
              .u64 (BitVec.ofNat 64 len),
              .u64 (BitVec.ofNat 64 (len + 1))] = .error e := by
          rw [hcallS, hs3]
        have hstepT3 := evalProgStmt_callRet_err vecGrowProg F "t3"
          stdVecShiftBackName ["t2", "pos", "len", "lenp1"] _ _
          stdVecShiftBackFunc e hargsT3 hfindS hcallS'
        have hfwd : stdVecInsertAuxFwd b len cap pos x = .error e := by
          simp only [stdVecInsertAuxFwd, hidx, vecGrow_bind_ok,
            vecGrowI32, hc1, vecGrowOwned, hbc1, hs3,
            vecGrow_bind_err]
        have hstmt : evalProgStmt vecGrowProg F
            stdVecInsertAuxFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] = .error e := by
          rw [hbody]
          exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
            ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elast).trans
              ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elw).trans
                ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT1).trans
                  ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elenp1).trans
                    ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ et2).trans
                      (evalProgStmt_seq_err _ _ _ _ _ _ hstepT3))))))
        simp only [evalProgFunc, hbind, hstmt, hfwd]
      | ok s3v =>
        obtain ⟨b3, hbc3, hlive3, hlenB3⟩ :=
          stdVecShiftBackFwd_ok b1 (len + 1) cap pos
            (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len + 1)) s3v
            hlive1 hs3
        have hstepT3 := evalProgStmt_callRet_ok vecGrowProg F "t3"
          stdVecShiftBackName ["t2", "pos", "len", "lenp1"] _ _
          stdVecShiftBackFunc s3v hargsT3 hfindS
          (by rw [hcallS, hs3])
        have hargsT4 : lookupArgs
            [(("t3", s3v)),
              (("t2", .stdVecOwned b1 (len + 1) cap)),
              (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
              (("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            ["t3", "pos", "x"] =
            some [s3v, .u64 pos, .i32 x] := by
          simp [lookupArgs, envLookup,
            show ("pos" : String) ≠ "t3" by decide,
            show ("pos" : String) ≠ "t2" by decide,
            show ("pos" : String) ≠ "lenp1" by decide,
            show ("pos" : String) ≠ "t1" by decide,
            show ("pos" : String) ≠ "lw" by decide,
            show ("pos" : String) ≠ "last" by decide,
            show ("pos" : String) ≠ "len" by decide,
            show ("pos" : String) ≠ "t" by decide]
        have hcallC2 : evalFuncFuel F stdVecConstructFunc
            [s3v, .u64 pos, .i32 x] =
            stdVecConstructFwd b3 (len + 1) cap pos x := by
          rw [hbc3]
          exact evalFuncFuel_stdVecConstruct F b3 (len + 1) cap pos x
        cases hc4 : stdVecConstructFwd b3 (len + 1) cap pos x with
        | error e =>
          have hcallC2' : evalFuncFuel F stdVecConstructFunc
              [s3v, .u64 pos, .i32 x] = .error e := by
            rw [hcallC2, hc4]
          have hstepT4 := evalProgStmt_callRet_err vecGrowProg F "t4"
            stdVecTraitsConstructName ["t3", "pos", "x"] _ _
            stdVecConstructFunc e hargsT4 hfindC hcallC2'
          have hfwd : stdVecInsertAuxFwd b len cap pos x = .error e := by
            simp only [stdVecInsertAuxFwd, hidx, vecGrow_bind_ok,
              vecGrowI32, hc1, vecGrowOwned, hbc1, hs3, hbc3, hc4]
          have hstmt : evalProgStmt vecGrowProg F
              stdVecInsertAuxFunc.body
              [("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)] = .error e := by
            rw [hbody]
            exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
              ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elast).trans
                ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elw).trans
                  ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT1).trans
                    ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elenp1).trans
                      ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ et2).trans
                        ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT3).trans
                          (evalProgStmt_seq_err _ _ _ _ _ _ hstepT4)))))))
          simp only [evalProgFunc, hbind, hstmt, hfwd]
        | ok c4v =>
          obtain ⟨b4, hbc4, _, _⟩ :=
            stdVecConstructFwd_ok b3 (len + 1) cap pos x c4v hc4
          have hstepT4 := evalProgStmt_callRet_ok vecGrowProg F "t4"
            stdVecTraitsConstructName ["t3", "pos", "x"] _ _
            stdVecConstructFunc c4v hargsT4 hfindC
            (by rw [hcallC2, hc4])
          have hvar : evalExpr (.var "t4")
              [(("t4", c4v)),
                (("t3", s3v)),
                (("t2", .stdVecOwned b1 (len + 1) cap)),
                (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
                (("t1", c1v)),
                (("lw", .i32 w)),
                (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)] = .ok c4v := by
            simp [evalExpr, envLookup]
          have hret : evalProgStmt vecGrowProg F
              (.return_ (.var "t4"))
              [(("t4", c4v)),
                (("t3", s3v)),
                (("t2", .stdVecOwned b1 (len + 1) cap)),
                (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
                (("t1", c1v)),
                (("lw", .i32 w)),
                (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)] =
              .ok ([(("t4", c4v)),
                (("t3", s3v)),
                (("t2", .stdVecOwned b1 (len + 1) cap)),
                (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
                (("t1", c1v)),
                (("lw", .i32 w)),
                (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)],
                .returned c4v) :=
            evalProgStmt_return vecGrowProg F _ _ _ hvar
          have hfwd : stdVecInsertAuxFwd b len cap pos x = .ok c4v := by
            simp only [stdVecInsertAuxFwd, hidx, vecGrow_bind_ok,
              vecGrowI32, hc1, vecGrowOwned, hbc1, hs3, hbc3, hc4]
          have hstmt : evalProgStmt vecGrowProg F
              stdVecInsertAuxFunc.body
              [("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)] =
              .ok ([(("t4", c4v)),
                (("t3", s3v)),
                (("t2", .stdVecOwned b1 (len + 1) cap)),
                (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
                (("t1", c1v)),
                (("lw", .i32 w)),
                (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)],
                .returned c4v) := by
            rw [hbody]
            exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
              ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elast).trans
                ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elw).trans
                  ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT1).trans
                    ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ elenp1).trans
                      ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ et2).trans
                        ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT3).trans
                          ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT4).trans
                            hret)))))))
          simp only [evalProgFunc, hbind, hstmt, hfwd, hbc4]