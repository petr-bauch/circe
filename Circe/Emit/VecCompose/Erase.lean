/-
Circe.Emit.VecCompose.Erase — N7d single-element `erase` over the
frozen N4d+N7b leaves (ii-a: value forwards; proofs land in the
ii-b/c/d slices).

The corpus `erase(const_iterator)` forwarder converts to an erased
`u64` position and delegates into `_M_erase`; the core is a 2-arm
composer over erased positions:
- last (`pos + 1 == len`): no shift, shrink to `len - 1`;
- else: shift `[pos + 1, len)` down to `pos`, shrink to `len - 1`
  (the per-element `destroy` is trivial for `int`, so the shrink is
  the whole effect).

The shift (`std::move` → `__copy_move_a` → `_a1` → `_a2` →
`__copy_m`, with `__miter_base` / `__niter_base` / `__niter_wrap`
fused) is ONE canonical `Func`: the guarded `memmove` is an
ascending copy walk (`stdVecBlitFwdFold` in `Circe.Base` — the
bottom word moves first, so overlapping left-shifts are sound).
The `__copy_m` `if (_Num)` guard is subsumed by the trip count;
its pointer return drops (callers recompute offsets).

Iterator leaf: `ne` (`une` over erased offsets).
-/
import Circe.Emit.Fragment
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose.Base
import Circe.Emit.VecCompose.Emplace
import Circe.Emit.VecCompose.Reserve

/-- Value-level forward for the ascending shift. -/
def stdVecShiftDownFwd (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) : Result Value :=
  match stdVecBlitFwdFold b len result.toNat first.toNat
      (last.toNat - first.toNat) with
  | .error e => .error e
  | .ok b' => .ok (.stdVecOwned b' len cap)

/-- Value-level forward for iterator inequality. -/
def stdVecIterNeFwd (a b : BitVec 64) : Result Value :=
  .ok (.b (a != b))

/-- Value-level forward for `_M_erase`. -/
def stdVecEraseCoreFwd (b : Vec32) (len cap : Nat) (pos : BitVec 64) :
    Result Value :=
  if pos.toNat + 1 == len then .ok (.stdVecOwned b (len - 1) cap)
  else
    (stdVecShiftDownFwd b len cap (pos + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 len) pos).bind fun s =>
    vecGrowOwned s |>.bind fun (b', _, _) =>
      .ok (.stdVecOwned b' (len - 1) cap)

/-- Value-level forward for the `erase` forwarder (delegates to the
    core; the iterator return drops). -/
def stdVecEraseFwd (b : Vec32) (len cap : Nat) (pos : BitVec 64) :
    Result Value :=
  stdVecEraseCoreFwd b len cap pos

/-! ## N7d-ii-b: forward shift leaf proofs (shells in `VecCompose.Base`) -/

/-- Unfolding one forward copy step (proved once, so the loop proof
    never unfolds the well-founded fixpoint). -/
theorem stdVecBlitFwdFold_step (b : Vec32) (len doff soff n : Nat) :
    stdVecBlitFwdFold b len doff soff (n + 1) =
      if b.freed then .error .AssertFail
      else if soff < len then
        match b.val[soff]? with
        | none => .error .OOB
        | some x =>
          match vecSet b doff x with
          | .error e => .error e
          | .ok b' => stdVecBlitFwdFold b' len (doff + 1) (soff + 1) n
      else .error .OOB := by
  rfl

/-- Forward blit preserves the buffer length (only `vecSet`s). -/
theorem stdVecBlitFwdFold_length (b : Vec32) (len : Nat)
    (doff soff n : Nat) (b' : Vec32)
    (h : stdVecBlitFwdFold b len doff soff n = .ok b') :
    b'.val.length = b.val.length := by
  induction n generalizing b doff soff with
  | zero => simp only [stdVecBlitFwdFold] at h; cases h; rfl
  | succ k ih =>
    simp only [stdVecBlitFwdFold] at h
    by_cases hfree : b.freed
    · simp [hfree] at h
    · simp [hfree] at h
      by_cases hlt : soff < len
      · simp [hlt] at h
        cases hx : b.val[soff]? with
        | none => simp [hx] at h
        | some x =>
          simp [hx] at h
          cases hs : vecSet b doff x with
          | error e => simp [hs] at h
          | ok b1 =>
            simp [hs] at h
            have h1 := ih _ _ _ h
            have h2 := vecSet_length b doff x b1 hs
            omega
      · simp [hlt] at h

/-- Forward blit preserves liveness. -/
theorem stdVecBlitFwdFold_live_of_live (b : Vec32) (len : Nat)
    (doff soff n : Nat) (b' : Vec32)
    (hlive : b.freed = false)
    (h : stdVecBlitFwdFold b len doff soff n = .ok b') :
    b'.freed = false := by
  induction n generalizing b doff soff with
  | zero => simp only [stdVecBlitFwdFold] at h; cases h; exact hlive
  | succ k ih =>
    simp only [stdVecBlitFwdFold, hlive] at h
    by_cases hlt : soff < len
    · simp [hlt] at h
      cases hx : b.val[soff]? with
      | none => simp [hx] at h
      | some x =>
        simp [hx] at h
        cases hs : vecSet b doff x with
        | error e => simp [hs] at h
        | ok b1 =>
          simp [hs] at h
          exact ih _ _ _ (vecSet_live b doff x b1 hs) h
    · simp [hlt] at h

/-- Loop environments, in let-prepend order (`n`, `k`, then the `t`
    / `first` / `last` / `result` params): `u64` trip count `n`,
    ascending counter `k`. -/
def mkStdVecShiftDownEnv (_b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) : Env :=
  [("n", .u64 n),
   ("k", .u64 (BitVec.ofNat 64 k)),
   ("t", .stdVecOwned dst len cap),
   ("first", .u64 first), ("last", .u64 last),
   ("result", .u64 result)]

theorem mkStdVecShiftDownEnv_k (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftDownEnv b len cap first last result k n
      dst) "k" = some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkStdVecShiftDownEnv, envLookup,
    show ("k" : String) ≠ "n" by decide]

theorem mkStdVecShiftDownEnv_n (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftDownEnv b len cap first last result k n
      dst) "n" = some (.u64 n) := by
  simp [mkStdVecShiftDownEnv, envLookup]

theorem mkStdVecShiftDownEnv_t (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftDownEnv b len cap first last result k n
      dst) "t" = some (.stdVecOwned dst len cap) := by
  simp [mkStdVecShiftDownEnv, envLookup,
    show ("t" : String) ≠ "n" by decide,
    show ("t" : String) ≠ "k" by decide]

theorem mkStdVecShiftDownEnv_first (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftDownEnv b len cap first last result k n
      dst) "first" = some (.u64 first) := by
  simp [mkStdVecShiftDownEnv, envLookup,
    show ("first" : String) ≠ "n" by decide,
    show ("first" : String) ≠ "k" by decide,
    show ("first" : String) ≠ "t" by decide]

theorem mkStdVecShiftDownEnv_result (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) :
    envLookup (mkStdVecShiftDownEnv b len cap first last result k n
      dst) "result" = some (.u64 result) := by
  simp [mkStdVecShiftDownEnv, envLookup,
    show ("result" : String) ≠ "n" by decide,
    show ("result" : String) ≠ "k" by decide,
    show ("result" : String) ≠ "t" by decide,
    show ("result" : String) ≠ "first" by decide,
    show ("result" : String) ≠ "last" by decide]

/-- Updating `k` stays in the env family. -/
theorem stdVecShiftDownEnv_update_k (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) (k' : Nat) :
    envUpdate (mkStdVecShiftDownEnv b len cap first last result k n
      dst) "k" (.u64 (BitVec.ofNat 64 k')) =
      some (mkStdVecShiftDownEnv b len cap first last result k' n
        dst) := by
  simp [mkStdVecShiftDownEnv, envUpdate,
    show ("k" : String) ≠ "n" by decide]

/-- Updating `t` stays in the env family. -/
theorem stdVecShiftDownEnv_update_t (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst dst' : Vec32) :
    envUpdate (mkStdVecShiftDownEnv b len cap first last result k n
      dst) "t" (.stdVecOwned dst' len cap) =
      some (mkStdVecShiftDownEnv b len cap first last result k n
        dst') := by
  simp [mkStdVecShiftDownEnv, envUpdate,
    show ("t" : String) ≠ "n" by decide,
    show ("t" : String) ≠ "k" by decide]

/-- The loop condition reads `k < n`. -/
theorem stdVecShiftDownCond_eval (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) (hk64 : k < 2 ^ 64) (_hn64 : n.toNat < 2 ^ 64) :
    evalExpr (.ult (.var "k") (.var "n"))
      (mkStdVecShiftDownEnv b len cap first last result k n
        dst) =
      .ok (.b (decide (k < n.toNat))) := by
  have hk := mkStdVecShiftDownEnv_k b len cap first last result k n
    dst
  have hn := mkStdVecShiftDownEnv_n b len cap first last result k n
    dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftDownEnv b len cap first last result k n dst) =
      .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hk]
  have hnv : evalExpr (.var "n")
      (mkStdVecShiftDownEnv b len cap first last result k n dst) =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have h := evalExpr_ult_u64 _ _ _ _ _ hkv hnv
  rw [ofNat64_ult k n hk64] at h
  exact h

/-- Body with a live read and a live write: copy one word down, bump
    the counter, stay in the env family (any fuel). The `vgrowSet`
    runs before the increment (bottom word moves first). -/
theorem stdVecShiftDownBody_step_ok (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (K : Nat) (n : BitVec 64) (dst : Vec32) (x : BitVec 32)
    (dst' : Vec32)
    (hKlt : K < n.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hres : result.toNat ≤ first.toNat)
    (hn : n = last - first)
    (hlive : dst.freed = false)
    (hlen : last.toNat ≤ len)
    (_hbuf : last.toNat ≤ dst.val.length)
    (_hS64 : dst.val.length < 2 ^ 64)
    (hget : dst.val[first.toNat + K]? = some x)
    (hset : vecSet dst (result.toNat + K) x = .ok dst') :
    evalStmtFuel F stdVecShiftDownBody
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (mkStdVecShiftDownEnv b len cap first last result (K + 1) n
        dst', .fellThrough) := by
  have hnt : n.toNat = last.toNat - first.toNat := by
    rw [hn]; exact u64sub_toNat_exact _ _ hfirst
  have hsidx : (first + BitVec.ofNat 64 K).toNat =
      first.toNat + K := by
    rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hdidx : (result + BitVec.ofNat 64 K).toNat =
      result.toNat + K := by
    rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hkL := mkStdVecShiftDownEnv_k b len cap first last result K n
    dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 (BitVec.ofNat 64 K)) := by
    simp [evalExpr, hkL]
  have hfirstv : evalExpr (.var "first")
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 first) := by
    have h := mkStdVecShiftDownEnv_first b len cap first last
      result K n dst
    simp [evalExpr, h]
  have hresv : evalExpr (.var "result")
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 result) := by
    have h := mkStdVecShiftDownEnv_result b len cap first last
      result K n dst
    simp [evalExpr, h]
  have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 (first + BitVec.ofNat 64 K)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv
  have hdidxe : evalExpr (.uadd (.var "result") (.var "k"))
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 (result + BitVec.ofNat 64 K)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hresv hkv
  have hget' : dst.val[(first + BitVec.ofNat 64 K).toNat]? =
      some x := by
    rw [hsidx]; exact hget
  have hlt : (first + BitVec.ofNat 64 K).toNat < len := by
    rw [hsidx]; omega
  have hset' : vecSet dst (result + BitVec.ofNat 64 K).toNat x =
      .ok dst' := by
    rw [hdidx]; exact hset
  have hd := mkStdVecShiftDownEnv_t b len cap first last result K n
    dst
  have hat : evalExpr
      (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.i32 x) :=
    evalExpr_vgrowAt_some "t" _ _ dst len cap _ _ hd hsidxe
      hlive hget' hlt
  have hsetF : evalStmtFuel F
      (.vgrowSet "t" (.uadd (.var "result") (.var "k"))
        (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (mkStdVecShiftDownEnv b len cap first last result K n
        dst', .fellThrough) :=
    evalStmtFuel_vgrowSet F _ _ _ _ _ _ _ _ _ _ _ hdidxe hat hd
      hset'
      (stdVecShiftDownEnv_update_t b len cap first last result K n
        dst dst')
  have hkv' : evalExpr (.var "k")
      (mkStdVecShiftDownEnv b len cap first last result K n dst') =
      .ok (.u64 (BitVec.ofNat 64 K)) := by
    have h := mkStdVecShiftDownEnv_k b len cap first last result K n
      dst'
    simp [evalExpr, h]
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecShiftDownEnv b len cap first last result K n dst') =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hince : evalExpr
      (.uadd (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkStdVecShiftDownEnv b len cap first last result K n dst') =
      .ok (.u64 (BitVec.ofNat 64 (K + 1))) := by
    have h := evalExpr_uadd_u64 _ _ _ _ _ hkv' hlit1
    rwa [ofNat64_add_one] at h
  have hasg := evalStmtFuel_assign F _ _ _ _ _ hince
    (stdVecShiftDownEnv_update_k b len cap first last result K n
      dst' (K + 1))
  exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hsetF).trans hasg

/-- Body with a failed copy: the `vgrowSet` error is loud (any fuel;
    the increment never runs). -/
theorem stdVecShiftDownBody_step_err (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (K : Nat) (n : BitVec 64) (dst : Vec32) (e : Panic)
    (herr : evalStmtFuel F
      (.vgrowSet "t" (.uadd (.var "result") (.var "k"))
        (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .error e) :
    evalStmtFuel F stdVecShiftDownBody
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .error e :=
  evalStmtFuel_seq_err F _ _ _ _ herr

/-- Loop correctness: copies the remaining suffix bottom-up, exits
    with `k = n` (fuel-generalized; the `+1` absorbs the final exit
    iteration). Offsets thread through the fold: at counter `k` the
    remaining `n - k` words sit at `result + k` / `first + k`. -/
theorem stdVecShiftDownWhile_correct (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64)
    (F k : Nat) (n : BitVec 64) (dst : Vec32)
    (hk : k ≤ n.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hres : result.toNat ≤ first.toNat)
    (hn : n = last - first)
    (hn64 : n.toNat < 2 ^ 64)
    (hlive : dst.freed = false)
    (hlen : last.toNat ≤ len)
    (hbuf : last.toNat ≤ dst.val.length)
    (hDb : result.toNat ≤ dst.val.length)
    (hS64 : dst.val.length < 2 ^ 64)
    (hF : n.toNat - k + 1 ≤ F) :
    evalStmtFuel F stdVecShiftDownWhile
      (mkStdVecShiftDownEnv b len cap first last result k n dst) =
      match stdVecBlitFwdFold dst len (result.toNat + k)
        (first.toNat + k) (n.toNat - k) with
      | .error e => .error e
      | .ok dst' =>
        .ok (mkStdVecShiftDownEnv b len cap first last result n.toNat
          n dst', .fellThrough) := by
  induction F generalizing k dst with
  | zero => omega
  | succ F ih =>
    have hnt : n.toNat = last.toNat - first.toNat := by
      rw [hn]; exact u64sub_toNat_exact _ _ hfirst
    have hk64 : k < 2 ^ 64 := by omega
    by_cases hlt : k < n.toNat
    · obtain ⟨R, hR⟩ : ∃ R, n.toNat - k = R + 1 :=
        ⟨n.toNat - k - 1, by omega⟩
      have hcond : evalExpr (.ult (.var "k") (.var "n"))
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) = .ok (.b true) := by
        have h := stdVecShiftDownCond_eval b len cap first last
          result k n dst hk64 hn64
        simpa [hlt] using h
      have hunfold := stdVecBlitFwdFold_step dst len
        (result.toNat + k) (first.toNat + k) R
      have hsoff : first.toNat + k < len := by omega
      have hsidx : (first + BitVec.ofNat 64 k).toNat =
          first.toNat + k := by
        rw [BitVec.toNat_add, ofNat64_toNat k (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      have hdidx : (result + BitVec.ofNat 64 k).toNat =
          result.toNat + k := by
        rw [BitVec.toNat_add, ofNat64_toNat k (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      have hkL := mkStdVecShiftDownEnv_k b len cap first last
        result k n dst
      have hkv' : evalExpr (.var "k")
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) = .ok (.u64 (BitVec.ofNat 64 k)) := by
        simp [evalExpr, hkL]
      have hfirstv : evalExpr (.var "first")
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) = .ok (.u64 first) := by
        have h := mkStdVecShiftDownEnv_first b len cap first last
          result k n dst
        simp [evalExpr, h]
      have hresv : evalExpr (.var "result")
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) = .ok (.u64 result) := by
        have h := mkStdVecShiftDownEnv_result b len cap first last
          result k n dst
        simp [evalExpr, h]
      have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) = .ok (.u64 (first + BitVec.ofNat 64 k)) :=
        evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv'
      have hdidxe : evalExpr (.uadd (.var "result") (.var "k"))
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) = .ok (.u64 (result + BitVec.ofNat 64 k)) :=
        evalExpr_uadd_u64 _ _ _ _ _ hresv hkv'
      have hget' : dst.val[(first + BitVec.ofNat 64 k).toNat]? =
          dst.val[first.toNat + k]? := by
        rw [hsidx]
      cases hget : dst.val[first.toNat + k]? with
      | none =>
        have hatE : evalExpr
            (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
            (mkStdVecShiftDownEnv b len cap first last result k n
              dst) = .error .OOB := by
          have hd := mkStdVecShiftDownEnv_t b len cap first last
            result k n dst
          rw [← hget'] at hget
          exact evalExpr_vgrowAt_oob_miss "t" _ _ dst len cap _ hd
            hsidxe hlive hget
        have herr : evalStmtFuel F
            (.vgrowSet "t" (.uadd (.var "result") (.var "k"))
              (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
            (mkStdVecShiftDownEnv b len cap first last result k n
              dst) = .error .OOB := by
          cases F <;>
            simp [evalStmtFuel, evalStmtZero, evalStmtWith, hdidxe,
              hatE]
        have hbody := stdVecShiftDownBody_step_err F b len cap
          first last result k n dst .OOB herr
        have hstep : evalStmtFuel (F + 1) stdVecShiftDownWhile
            (mkStdVecShiftDownEnv b len cap first last result k n
              dst) = .error .OOB := by
          simp [stdVecShiftDownWhile, evalStmtFuel,
            evalStmtSuccHandler, evalStmtWith, hcond, hbody]
        rw [hstep, hR, hunfold]
        simp [hlive, hsoff, hget]
      | some x =>
        have hd := mkStdVecShiftDownEnv_t b len cap first last
          result k n dst
        cases hset : vecSet dst (result.toNat + k) x with
        | error e =>
          have hltlen : (first + BitVec.ofNat 64 k).toNat < len := by
            rw [hsidx]; omega
          have hgetx : dst.val[(first + BitVec.ofNat 64 k).toNat]? =
              some x := by
            rw [hsidx]; exact hget
          have hat : evalExpr
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              (mkStdVecShiftDownEnv b len cap first last result k n
                dst) = .ok (.i32 x) :=
            evalExpr_vgrowAt_some "t" _ _ dst len cap _ _ hd hsidxe
              hlive hgetx hltlen
          have hset' : vecSet dst (result + BitVec.ofNat 64 k).toNat
              x = .error e := by
            rw [hdidx]; exact hset
          have herr : evalStmtFuel F
              (.vgrowSet "t" (.uadd (.var "result") (.var "k"))
                (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
              (mkStdVecShiftDownEnv b len cap first last result k n
                dst) = .error e :=
            evalStmtFuel_vgrowSet_err F _ _ _ _ _ _ _ _ _ _ hdidxe
              hat hd hset'
          have hbody := stdVecShiftDownBody_step_err F b len cap
            first last result k n dst e herr
          have hstep : evalStmtFuel (F + 1) stdVecShiftDownWhile
              (mkStdVecShiftDownEnv b len cap first last result k n
                dst) = .error e := by
            simp [stdVecShiftDownWhile, evalStmtFuel,
              evalStmtSuccHandler, evalStmtWith, hcond, hbody]
          rw [hstep, hR, hunfold]
          simp [hlive, hsoff, hget, hset]
        | ok dst' =>
          have hbody := stdVecShiftDownBody_step_ok F b len cap
            first last result k n dst x dst' hlt hfirst hres hn
            hlive hlen hbuf hS64 hget hset
          have hstep : evalStmtFuel (F + 1) stdVecShiftDownWhile
              (mkStdVecShiftDownEnv b len cap first last result k n
                dst) =
              evalStmtFuel F stdVecShiftDownWhile
                (mkStdVecShiftDownEnv b len cap first last
                  result (k + 1) n dst') := by
            simp [stdVecShiftDownWhile, evalStmtFuel,
              evalStmtSuccHandler, evalStmtWith, hcond, hbody]
          have hlenD' : dst'.val.length = dst.val.length :=
            vecSet_length dst _ x dst' hset
          have hfreeD' : dst'.freed = false :=
            vecSet_live dst _ x dst' hset
          rw [hstep, hR, hunfold]
          simp only [hlive, hsoff, hget, hset]
          have e1 : result.toNat + k + 1 = result.toNat + (k + 1) :=
            by omega
          have e2 : first.toNat + k + 1 = first.toNat + (k + 1) :=
            by omega
          have e3 : R = n.toNat - (k + 1) := by omega
          rw [e1, e2, e3]
          exact ih (k + 1) dst' (by omega) hfreeD'
            (by rw [hlenD']; exact hbuf)
            (by rw [hlenD']; exact hDb)
            (by rw [hlenD']; exact hS64) (by omega)
    · have hkk : k = n.toNat := by omega
      subst hkk
      have hcondF : evalExpr (.ult (.var "k") (.var "n"))
          (mkStdVecShiftDownEnv b len cap first last result n.toNat
            n dst) = .ok (.b false) := by
        have h := stdVecShiftDownCond_eval b len cap first last
          result n.toNat n dst hn64 hn64
        simpa [hlt] using h
      have hzero : stdVecBlitFwdFold dst len
          (result.toNat + n.toNat) (first.toNat + n.toNat)
          (n.toNat - n.toNat) = .ok dst := by
        have h0 : n.toNat - n.toNat = 0 := by omega
        rw [h0]; rfl
      have hLHS : evalStmtFuel (F + 1) stdVecShiftDownWhile
          (mkStdVecShiftDownEnv b len cap first last result n.toNat
            n dst) =
          .ok (mkStdVecShiftDownEnv b len cap first last result
            n.toNat n dst, .fellThrough) := by
        simp [stdVecShiftDownWhile, evalStmtFuel,
          evalStmtSuccHandler, evalStmtWith, hcondF]
      have hRHS : (match stdVecBlitFwdFold dst len
          (result.toNat + n.toNat) (first.toNat + n.toNat)
          (n.toNat - n.toNat) with
        | Except.error e => Except.error e
        | Except.ok dst' =>
          Except.ok (mkStdVecShiftDownEnv b len cap first last
            result n.toNat n dst', Outcome.fellThrough)) =
          .ok (mkStdVecShiftDownEnv b len cap first last result
            n.toNat n dst, Outcome.fellThrough) := by
        rw [hzero]
      exact hLHS.trans hRHS.symm

/-- `emit_correct` for the forward shift (fuel-generalized; the fuel
    hypothesis is the slice's dynamic-length side condition). -/
theorem evalFuncFuel_stdVecShiftDown (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (hfirst : first.toNat ≤ last.toNat)
    (hres : result.toNat ≤ first.toNat)
    (hlive : b.freed = false)
    (hlen : last.toNat ≤ len)
    (hbuf : last.toNat ≤ b.val.length)
    (hDb : result.toNat ≤ b.val.length)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat + 1 ≤ F) :
    evalFuncFuel F stdVecShiftDownFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result] =
      stdVecShiftDownFwd b len cap first last result := by
  have hX : (last - first).toNat = last.toNat - first.toNat :=
    u64sub_toNat_exact _ _ hfirst
  have hbind : bindArgs stdVecShiftDownFunc.args
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result] =
      some [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] := rfl
  have hbody : stdVecShiftDownFunc.body =
      .seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      (.seq stdVecShiftDownWhile
        (.return_ (.var "t")))) := rfl
  have hlit0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have e1 : evalStmtFuel F
      (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok ([("k", .u64 (BitVec.ofNat 64 0)),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)], .fellThrough) :=
    evalStmtFuel_let_ F "k" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (.u64 (BitVec.ofNat 64 0)) hlit0
  have hlast1 : evalExpr (.var "last")
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 last) := by
    simp [evalExpr, envLookup,
      show ("last" : String) ≠ "k" by decide,
      show ("last" : String) ≠ "t" by decide,
      show ("last" : String) ≠ "first" by decide]
  have hfirst1 : evalExpr (.var "first")
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 first) := by
    simp [evalExpr, envLookup,
      show ("first" : String) ≠ "k" by decide,
      show ("first" : String) ≠ "t" by decide]
  have hnEval1 : evalExpr (.usub (.var "last") (.var "first"))
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (last - first)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hlast1 hfirst1
  have e2 : evalStmtFuel F
      (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (mkStdVecShiftDownEnv b len cap first last result 0
        (last - first) b, .fellThrough) :=
    evalStmtFuel_let_ F "n" (.u 64)
      (.usub (.var "last") (.var "first"))
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (.u64 (last - first)) hnEval1
  have hF0 : (last - first).toNat - 0 + 1 ≤ F := by omega
  have hloop0 := stdVecShiftDownWhile_correct b len cap
    first last result F 0 (last - first) b (Nat.zero_le _)
    hfirst hres rfl (by omega) hlive hlen hbuf hDb hS64 hF0
  have hcanon : stdVecBlitFwdFold b len result.toNat first.toNat
      (last.toNat - first.toNat) =
      stdVecBlitFwdFold b len (result.toNat + 0) (first.toNat + 0)
        ((last - first).toNat - 0) := by
    simp only [Nat.add_zero, Nat.sub_zero, hX]
  cases hblit : stdVecBlitFwdFold b len (result.toNat + 0)
      (first.toNat + 0) ((last - first).toNat - 0) with
  | error e =>
    have hloopE : evalStmtFuel F stdVecShiftDownWhile
        (mkStdVecShiftDownEnv b len cap first last result 0
          (last - first) b) = .error e := by
      rw [hblit] at hloop0
      exact hloop0
    have hfwd : stdVecShiftDownFwd b len cap first last result =
        .error e := by
      simp only [stdVecShiftDownFwd, hcanon, hblit]
    have hstmt : evalStmtFuel F stdVecShiftDownFunc.body
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] = .error e := by
      rw [hbody]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ e1).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ e2).trans
          (evalStmtFuel_seq_err F _ _ _ _ hloopE))
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  | ok b' =>
    have hloopO : evalStmtFuel F stdVecShiftDownWhile
        (mkStdVecShiftDownEnv b len cap first last result 0
          (last - first) b) =
        .ok (mkStdVecShiftDownEnv b len cap first last result
          (last - first).toNat (last - first) b', .fellThrough) := by
      rw [hblit] at hloop0
      exact hloop0
    have hret : envLookup
        (mkStdVecShiftDownEnv b len cap first last result
          (last - first).toNat (last - first) b') "t" =
        some (.stdVecOwned b' len cap) :=
      mkStdVecShiftDownEnv_t b len cap first last result
        (last - first).toNat (last - first) b'
    have hvar : evalExpr (.var "t")
        (mkStdVecShiftDownEnv b len cap first last result
          (last - first).toNat (last - first) b') =
        .ok (.stdVecOwned b' len cap) := by
      simp only [evalExpr]
      rw [hret]
    have hfwd : stdVecShiftDownFwd b len cap first last result =
        .ok (.stdVecOwned b' len cap) := by
      simp only [stdVecShiftDownFwd, hcanon, hblit]
    have hstmt : evalStmtFuel F stdVecShiftDownFunc.body
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] =
        .ok (mkStdVecShiftDownEnv b len cap first last result
          (last - first).toNat (last - first) b',
          .returned (.stdVecOwned b' len cap)) := by
      rw [hbody]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ e1).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ e2).trans
          ((evalStmtFuel_seq_fallthrough F _ _ _ _ hloopO).trans
            (evalStmtFuel_return F _ _ _ hvar)))
    simp [evalFuncFuel, hbind, hstmt, hfwd]

/-! ## N7d-ii-b: `_M_erase` / `erase` composer eval -/

/-- `findFunc` resolves the forward shift in the grown program. -/
theorem findFunc_stdVecShiftDown :
    findFunc vecGrowProg stdVecShiftDownName =
      some stdVecShiftDownFunc := by
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
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves `_M_erase` in the grown program. -/
theorem findFunc_stdVecEraseCore :
    findFunc vecGrowProg stdVecEraseCoreName =
      some stdVecEraseCoreFunc := by
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
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the `erase` forwarder in the grown program. -/
theorem findFunc_stdVecErase :
    findFunc vecGrowProg stdVecEraseName =
      some stdVecEraseFunc := by
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

/-- Shift success preserves the `len` / `cap` components, keeps the
    block live, and preserves the buffer length. -/
theorem stdVecShiftDownFwd_ok (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (v : Value)
    (hlive : b.freed = false)
    (h : stdVecShiftDownFwd b len cap first last result = .ok v) :
    ∃ b', v = .stdVecOwned b' len cap ∧ b'.freed = false ∧
      b'.val.length = b.val.length := by
  unfold stdVecShiftDownFwd at h
  cases hbl : stdVecBlitFwdFold b len result.toNat first.toNat
      (last.toNat - first.toNat) with
  | error e => simp [hbl] at h
  | ok b' =>
    simp [hbl] at h
    cases h
    exact ⟨_, rfl,
      stdVecBlitFwdFold_live_of_live _ _ _ _ _ _ hlive hbl,
      stdVecBlitFwdFold_length _ _ _ _ _ _ hbl⟩

/-- The call-free shift body evaluates identically under the program
    evaluator (every statement hits the `evalStmtFuel` fallback arm,
    so `callProg` into the leaf agrees with `evalFuncFuel`). -/
theorem evalProgStmt_stdVecShiftDownBody (F' : Nat) (ρ : Env) :
    evalProgStmt vecGrowProg F' stdVecShiftDownFunc.body ρ =
      evalStmtFuel F' stdVecShiftDownFunc.body ρ := by
  have hbody : stdVecShiftDownFunc.body =
      .seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.let_ "n" (.u 64)
        (.usub (.var "last") (.var "first")))
      (.seq stdVecShiftDownWhile
        (.return_ (.var "t")))) := rfl
  rw [hbody]
  cases F' with
  | zero =>
    simp only [evalProgStmt, stdVecShiftDownWhile, evalStmtFuel,
      evalStmtZero, evalStmtWith]
  | succ n =>
    simp only [evalProgStmt, stdVecShiftDownWhile, evalStmtFuel,
      evalStmtWith]

/-- `ofNat` survives decrementing a positive small length
    (composer-local twin of `ofNat_sub_one` in `Insert.lean`, kept
    local so `Erase` does not import the whole insert slice). -/
theorem ofNat_erase_sub_one (m : Nat) (h64 : m < 2 ^ 64) (h1 : 1 ≤ m) :
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

/-- `emit_correct` for `_M_erase`: the program over the grown program
    agrees with the core forward. Caller-side preconditions: the
    triple is live, the position is a valid index, and fuel covers one
    `callProg` depth plus the shift (`len + 1 ≤ F`). -/
theorem evalProgFunc_stdVecEraseCore (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64)
    (hlive : b.freed = false)
    (hbuf : len ≤ b.val.length)
    (hpos : pos.toNat < len)
    (hlen1 : 1 ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : len + 1 ≤ F) :
    evalProgFunc vecGrowProg F stdVecEraseCoreFunc
      [.stdVecOwned b len cap, .u64 pos] =
      stdVecEraseCoreFwd b len cap pos := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down len hF
  have hlen64 : len < 2 ^ 64 := by omega
  have hlenT : (BitVec.ofNat 64 len).toNat = len :=
    ofNat64_toNat _ hlen64
  have hnposT : (pos + BitVec.ofNat 64 1).toNat = pos.toNat + 1 := by
    rw [BitVec.toNat_add, ofNat64_toNat 1 (by decide)]
    exact Nat.mod_eq_of_lt (by omega)
  have hbind : bindArgs stdVecEraseCoreFunc.args
      [.stdVecOwned b len cap, .u64 pos] =
      some [("t", .stdVecOwned b len cap), ("pos", .u64 pos)] := rfl
  have hbody : stdVecEraseCoreFunc.body =
      (.seq (.let_ "len" (.u 64) (.vgrowLen "t"))
      (.seq (.let_ "npos" (.u 64)
              (.uadd (.var "pos") (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.if_ (.une (.var "npos") (.var "len"))
        (.seq (.callProg "t1" stdVecShiftDownName
                ["t", "npos", "len", "pos"])
          (.seq (.let_ "t2" (.vecBlock)
                  (.vgrowSetLen "t1"
                    (.usub (.var "len")
                      (.lit (.u64 (BitVec.ofNat 64 1))))))
            (.return_ (.var "t2"))))
        (.seq (.let_ "t3" (.vecBlock)
                (.vgrowSetLen "t"
                  (.usub (.var "len")
                    (.lit (.u64 (BitVec.ofNat 64 1))))))
          (.return_ (.var "t3")))))) := rfl
  have ht0 : envLookup [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos)] "t" =
      some (.stdVecOwned b len cap) := by simp [envLookup]
  have hlenE : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht0
  have elen : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "len" (.u 64) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok ([("len", .u64 (BitVec.ofNat 64 len)),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)], .fellThrough) :=
    (evalProgStmt_let_fb _ _ _ _ _ _).trans
      (evalStmtFuel_let_ _ "len" (.u 64) (.vgrowLen "t")
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (.u64 (BitVec.ofNat 64 len)) hlenE)
  have hposV : evalExpr (.var "pos")
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] = .ok (.u64 pos) := by
    simp [evalExpr, envLookup,
      show ("pos" : String) ≠ "len" by decide]
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hnposE : evalExpr
      (.uadd (.var "pos") (.lit (.u64 (BitVec.ofNat 64 1))))
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (pos + BitVec.ofNat 64 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hposV hlit1
  have enpos : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "npos" (.u 64)
        (.uadd (.var "pos") (.lit (.u64 (BitVec.ofNat 64 1)))))
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok ([(("npos", .u64 (pos + BitVec.ofNat 64 1))),
        (("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)], .fellThrough) :=
    (evalProgStmt_let_fb _ _ _ _ _ _).trans
      (evalStmtFuel_let_ _ "npos" (.u 64)
        (.uadd (.var "pos") (.lit (.u64 (BitVec.ofNat 64 1))))
        [((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (.u64 (pos + BitVec.ofNat 64 1)) hnposE)
  have hnposV : evalExpr (.var "npos")
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (pos + BitVec.ofNat 64 1)) := by
    simp [evalExpr, envLookup]
  have hlenV : evalExpr (.var "len")
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    simp [evalExpr, envLookup,
      show ("len" : String) ≠ "npos" by decide]
  have hneE : evalExpr (.une (.var "npos") (.var "len"))
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.b ((pos + BitVec.ofNat 64 1) !=
        BitVec.ofNat 64 len)) := by
    simp [evalExpr, envLookup,
      show ("len" : String) ≠ "npos" by decide]
  have hargsT1 : lookupArgs
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      ["t", "npos", "len", "pos"] =
      some [.stdVecOwned b len cap,
        .u64 (pos + BitVec.ofNat 64 1),
        .u64 (BitVec.ofNat 64 len), .u64 pos] := by
    simp [lookupArgs, envLookup,
      show ("t" : String) ≠ "npos" by decide,
      show ("t" : String) ≠ "len" by decide,
      show ("len" : String) ≠ "npos" by decide,
      show ("pos" : String) ≠ "npos" by decide,
      show ("pos" : String) ≠ "len" by decide,
      show ("pos" : String) ≠ "t" by decide]
  have hcall : evalProgFunc vecGrowProg F' stdVecShiftDownFunc
      [.stdVecOwned b len cap, .u64 (pos + BitVec.ofNat 64 1),
        .u64 (BitVec.ofNat 64 len), .u64 pos] =
      stdVecShiftDownFwd b len cap (pos + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 len) pos := by
    have hbindS : bindArgs stdVecShiftDownFunc.args
        [.stdVecOwned b len cap, .u64 (pos + BitVec.ofNat 64 1),
          .u64 (BitVec.ofNat 64 len), .u64 pos] =
        some [("t", .stdVecOwned b len cap),
          ("first", .u64 (pos + BitVec.ofNat 64 1)),
          ("last", .u64 (BitVec.ofNat 64 len)),
          ("result", .u64 pos)] := rfl
    have hfuel := evalFuncFuel_stdVecShiftDown F' b len cap
      (pos + BitVec.ofNat 64 1) (BitVec.ofNat 64 len) pos
      (by rw [hnposT, hlenT]; omega)
      (by rw [hnposT]; omega)
      hlive
      (by omega)
      (by rw [hlenT]; exact hbuf)
      (by omega)
      hS64
      (by rw [hlenT, hnposT]; omega)
    simp only [evalProgFunc, hbindS]
    rw [evalProgStmt_stdVecShiftDownBody]
    simpa only [evalFuncFuel, hbindS] using hfuel
  cases heqB : ((pos + BitVec.ofNat 64 1) ==
      BitVec.ofNat 64 len) with
  | true =>
    have hBV : pos + BitVec.ofNat 64 1 = BitVec.ofNat 64 len :=
      beq_iff_eq.mp heqB
    have hcond : evalExpr (.une (.var "npos") (.var "len"))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] = .ok (.b false) := by
      have hbne : ((pos + BitVec.ofNat 64 1) !=
          BitVec.ofNat 64 len) = false := by
        simp [hBV]
      rw [hneE, hbne]
    have hNat : (pos.toNat + 1 == len) = true := by
      have heq : pos.toNat + 1 = len := by
        have hconT : (pos + BitVec.ofNat 64 1).toNat =
            (BitVec.ofNat 64 len).toNat := by
          rw [hBV]
        rw [hnposT, hlenT] at hconT
        exact hconT
      simp [heq]
    have ht : envLookup
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] "t" =
        some (.stdVecOwned b len cap) := by
      simp [envLookup,
        show ("t" : String) ≠ "npos" by decide,
        show ("t" : String) ≠ "len" by decide]
    have hlenV1 : evalExpr (.var "len")
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.u64 (BitVec.ofNat 64 len)) := hlenV
    have hlit1' : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.u64 (BitVec.ofNat 64 1)) := by
      simp [evalExpr, litVal]
    have hsubE : evalExpr
        (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.u64 (BitVec.ofNat 64 len - BitVec.ofNat 64 1)) :=
      evalExpr_usub_u64u64 _ _ _ _ _ hlenV1 hlit1'
    have hsub1 : BitVec.ofNat 64 len - BitVec.ofNat 64 1 =
        BitVec.ofNat 64 (len - 1) :=
      ofNat_erase_sub_one len hlen64 hlen1
    have hsetE : evalExpr
        (.vgrowSetLen "t"
          (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.stdVecOwned b (len - 1) cap) := by
      have h := evalExpr_vgrowSetLen_hit "t" _ _
        b len cap (BitVec.ofNat 64 len - BitVec.ofNat 64 1)
        ht hsubE
      rwa [hsub1, ofNat64_toNat _ (by omega)] at h
    have et3 : evalProgStmt vecGrowProg (F' + 1)
        (.let_ "t3" (.vecBlock)
          (.vgrowSetLen "t"
            (.usub (.var "len")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok ([((("t3", .stdVecOwned b (len - 1) cap))),
          ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)], .fellThrough) :=
      (evalProgStmt_let_fb _ _ _ _ _ _).trans
        (evalStmtFuel_let_ _ "t3" (.vecBlock)
          (.vgrowSetLen "t"
            (.usub (.var "len")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
          [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (.stdVecOwned b (len - 1) cap) hsetE)
    have hvar : evalExpr (.var "t3")
        [((("t3", .stdVecOwned b (len - 1) cap))),
          ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.stdVecOwned b (len - 1) cap) := by
      simp [evalExpr, envLookup]
    have hret : evalProgStmt vecGrowProg (F' + 1)
        (.return_ (.var "t3"))
        [((("t3", .stdVecOwned b (len - 1) cap))),
          ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok ([((("t3", .stdVecOwned b (len - 1) cap))),
          ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)],
          .returned (.stdVecOwned b (len - 1) cap)) :=
      evalProgStmt_return _ _ _ _ _ hvar
    have helse : evalProgStmt vecGrowProg (F' + 1)
        (.seq (.let_ "t3" (.vecBlock)
                (.vgrowSetLen "t"
                  (.usub (.var "len")
                    (.lit (.u64 (BitVec.ofNat 64 1))))))
          (.return_ (.var "t3")))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok ([((("t3", .stdVecOwned b (len - 1) cap))),
          ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)],
          .returned (.stdVecOwned b (len - 1) cap)) := by
      exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ et3).trans hret
    have hfwd : stdVecEraseCoreFwd b len cap pos =
        .ok (.stdVecOwned b (len - 1) cap) := by
      simp [stdVecEraseCoreFwd, hNat]
    have hstmt : evalProgStmt vecGrowProg (F' + 1)
        stdVecEraseCoreFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok ([((("t3", .stdVecOwned b (len - 1) cap))),
          ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)],
          .returned (.stdVecOwned b (len - 1) cap)) := by
      rw [hbody]
      exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
        ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ enpos).trans
          ((evalProgStmt_if_false _ _ _ _ _ _ hcond).trans helse))
    simp only [evalProgFunc, hbind, hstmt, hfwd]

  | false =>
    have hBV : pos + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 len := by
      intro hcon
      simp [hcon] at heqB
    have hcond : evalExpr (.une (.var "npos") (.var "len"))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] = .ok (.b true) := by
      have hbne : ((pos + BitVec.ofNat 64 1) !=
          BitVec.ofNat 64 len) = true :=
        bne_iff_ne.mpr hBV
      rw [hneE, hbne]
    have hNat : (pos.toNat + 1 == len) = false := by
      have hcon : pos.toNat + 1 ≠ len := by
        intro hcon
        have hconT : (pos + BitVec.ofNat 64 1).toNat =
            (BitVec.ofNat 64 len).toNat := by
          rw [hnposT, hcon, hlenT]
        have := BitVec.eq_of_toNat_eq hconT
        simp [this] at heqB
      simp [hcon]
    cases hs : stdVecShiftDownFwd b len cap
        (pos + BitVec.ofNat 64 1) (BitVec.ofNat 64 len) pos with
    | error e =>
      have hcall' : evalProgFunc vecGrowProg F'
          stdVecShiftDownFunc
          [.stdVecOwned b len cap,
            .u64 (pos + BitVec.ofNat 64 1),
            .u64 (BitVec.ofNat 64 len), .u64 pos] = .error e := by
        rw [hcall, hs]
      have hstepT1 := evalProgStmt_callProg_err vecGrowProg F'
          "t1" stdVecShiftDownName ["t", "npos", "len", "pos"] _ _
          stdVecShiftDownFunc e hargsT1 findFunc_stdVecShiftDown
          hcall'
      have hfwd : stdVecEraseCoreFwd b len cap pos = .error e := by
        simp [stdVecEraseCoreFwd, hNat, hs, vecGrow_bind_err]
      have hstmt : evalProgStmt vecGrowProg (F' + 1)
          stdVecEraseCoreFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] = .error e := by
        rw [hbody]
        exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
          ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ enpos).trans
            ((evalProgStmt_if_true _ _ _ _ _ _ hcond).trans
              (evalProgStmt_seq_err _ _ _ _ _ _ hstepT1)))
      simp only [evalProgFunc, hbind, hstmt, hfwd]
    | ok s =>
      obtain ⟨b', hbc, hlive', hlenB'⟩ :=
        stdVecShiftDownFwd_ok b len cap (pos + BitVec.ofNat 64 1)
          (BitVec.ofNat 64 len) pos s hlive hs
      have hcall' : evalProgFunc vecGrowProg F'
          stdVecShiftDownFunc
          [.stdVecOwned b len cap,
            .u64 (pos + BitVec.ofNat 64 1),
            .u64 (BitVec.ofNat 64 len), .u64 pos] = .ok s := by
        rw [hcall, hs]
      have hstepT1 := evalProgStmt_callProg_ok vecGrowProg F'
          "t1" stdVecShiftDownName ["t", "npos", "len", "pos"] _ _
          stdVecShiftDownFunc s hargsT1 findFunc_stdVecShiftDown
          hcall'
      have ht1 : envLookup
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] "t1" =
          some (.stdVecOwned b' len cap) := by
        rw [hbc]; simp [envLookup]
      have hlenV1 : evalExpr (.var "len")
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.u64 (BitVec.ofNat 64 len)) := by
        simp [evalExpr, envLookup,
          show ("len" : String) ≠ "t1" by decide,
          show ("len" : String) ≠ "npos" by decide]
      have hlit1' : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.u64 (BitVec.ofNat 64 1)) := by
        simp [evalExpr, litVal]
      have hsubE : evalExpr
          (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.u64 (BitVec.ofNat 64 len - BitVec.ofNat 64 1)) :=
        evalExpr_usub_u64u64 _ _ _ _ _ hlenV1 hlit1'
      have hsub1 : BitVec.ofNat 64 len - BitVec.ofNat 64 1 =
          BitVec.ofNat 64 (len - 1) :=
        ofNat_erase_sub_one len hlen64 hlen1
      have hsetE : evalExpr
          (.vgrowSetLen "t1"
            (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.stdVecOwned b' (len - 1) cap) := by
        have h := evalExpr_vgrowSetLen_hit "t1" _ _
          b' len cap (BitVec.ofNat 64 len - BitVec.ofNat 64 1)
          ht1 hsubE
        rwa [hsub1, ofNat64_toNat _ (by omega)] at h
      have et2 : evalProgStmt vecGrowProg (F' + 1)
          (.let_ "t2" (.vecBlock)
            (.vgrowSetLen "t1"
              (.usub (.var "len")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok ([((("t2", .stdVecOwned b' (len - 1) cap))),
            ((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)], .fellThrough) :=
        (evalProgStmt_let_fb _ _ _ _ _ _).trans
          (evalStmtFuel_let_ _ "t2" (.vecBlock)
            (.vgrowSetLen "t1"
              (.usub (.var "len")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
            [((("t1", s))),
              ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
              ((("len", .u64 (BitVec.ofNat 64 len)))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos)]
            (.stdVecOwned b' (len - 1) cap) hsetE)
      have hvar : evalExpr (.var "t2")
          [((("t2", .stdVecOwned b' (len - 1) cap))),
            ((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.stdVecOwned b' (len - 1) cap) := by
        simp [evalExpr, envLookup]
      have hret : evalProgStmt vecGrowProg (F' + 1)
          (.return_ (.var "t2"))
          [((("t2", .stdVecOwned b' (len - 1) cap))),
            ((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok ([((("t2", .stdVecOwned b' (len - 1) cap))),
            ((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)],
            .returned (.stdVecOwned b' (len - 1) cap)) :=
        evalProgStmt_return _ _ _ _ _ hvar
      have hthen : evalProgStmt vecGrowProg (F' + 1)
          (.seq (.callProg "t1" stdVecShiftDownName
                  ["t", "npos", "len", "pos"])
            (.seq (.let_ "t2" (.vecBlock)
                    (.vgrowSetLen "t1"
                      (.usub (.var "len")
                        (.lit (.u64 (BitVec.ofNat 64 1))))))
              (.return_ (.var "t2"))))
          [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok ([((("t2", .stdVecOwned b' (len - 1) cap))),
            ((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)],
            .returned (.stdVecOwned b' (len - 1) cap)) := by
        exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT1).trans
          ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ et2).trans hret)
      have hfwd : stdVecEraseCoreFwd b len cap pos =
          .ok (.stdVecOwned b' (len - 1) cap) := by
        simp only [stdVecEraseCoreFwd, hNat, hs, vecGrow_bind_ok]
        rw [hbc]
        simp [vecGrowOwned, vecGrow_bind_ok]
      have hstmt : evalProgStmt vecGrowProg (F' + 1)
          stdVecEraseCoreFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok ([((("t2", .stdVecOwned b' (len - 1) cap))),
            ((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)],
            .returned (.stdVecOwned b' (len - 1) cap)) := by
        rw [hbody]
        exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
          ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ enpos).trans
            ((evalProgStmt_if_true _ _ _ _ _ _ hcond).trans hthen))
      simp only [evalProgFunc, hbind, hstmt, hfwd]
/-- `emit_correct` for the `erase` forwarder: delegation into
    `_M_erase` agrees with the erase forward (the iterator return
    drops). Fuel covers one `callProg` depth plus the core
    (`len + 2 ≤ F`). -/
theorem evalProgFunc_stdVecErase (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64)
    (hlive : b.freed = false)
    (hbuf : len ≤ b.val.length)
    (hpos : pos.toNat < len)
    (hlen1 : 1 ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : len + 2 ≤ F) :
    evalProgFunc vecGrowProg F stdVecEraseFunc
      [.stdVecOwned b len cap, .u64 pos] =
      stdVecEraseFwd b len cap pos := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down (len + 1) hF
  have hbind : bindArgs stdVecEraseFunc.args
      [.stdVecOwned b len cap, .u64 pos] =
      some [("t", .stdVecOwned b len cap), ("pos", .u64 pos)] := rfl
  have hbody : stdVecEraseFunc.body =
      (.seq (.callProg "t1" stdVecEraseCoreName ["t", "pos"])
        (.return_ (.var "t1"))) := rfl
  have hargs : lookupArgs [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos)] ["t", "pos"] =
      some [.stdVecOwned b len cap, .u64 pos] := by
    simp [lookupArgs, envLookup,
      show ("pos" : String) ≠ "t" by decide]
  have hcall : evalProgFunc vecGrowProg F' stdVecEraseCoreFunc
      [.stdVecOwned b len cap, .u64 pos] =
      stdVecEraseCoreFwd b len cap pos :=
    evalProgFunc_stdVecEraseCore F' b len cap pos hlive hbuf
      hpos hlen1 hS64 hF'
  cases hR : stdVecEraseCoreFwd b len cap pos with
  | error e =>
    have hcall' : evalProgFunc vecGrowProg F' stdVecEraseCoreFunc
        [.stdVecOwned b len cap, .u64 pos] = .error e := by
      rw [hcall, hR]
    have hstepCall := evalProgStmt_callProg_err vecGrowProg F' "t1"
        stdVecEraseCoreName ["t", "pos"] _ _
        stdVecEraseCoreFunc e hargs findFunc_stdVecEraseCore hcall'
    have hfwd : stdVecEraseFwd b len cap pos = .error e := by
      simp only [stdVecEraseFwd, hR]
    have hstmt : evalProgStmt vecGrowProg (F' + 1)
        stdVecEraseFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] = .error e := by
      rw [hbody]
      exact evalProgStmt_seq_err _ _ _ _ _ _ hstepCall
    simp only [evalProgFunc, hbind, hstmt, hfwd]
  | ok v =>
    have hcall' : evalProgFunc vecGrowProg F' stdVecEraseCoreFunc
        [.stdVecOwned b len cap, .u64 pos] = .ok v := by
      rw [hcall, hR]
    have hstepCall := evalProgStmt_callProg_ok vecGrowProg F' "t1"
        stdVecEraseCoreName ["t", "pos"] _ _
        stdVecEraseCoreFunc v hargs findFunc_stdVecEraseCore hcall'
    have hvar : evalExpr (.var "t1")
        [((("t1", v))), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] = .ok v := by
      simp [evalExpr, envLookup]
    have hret : evalProgStmt vecGrowProg (F' + 1)
        (.return_ (.var "t1"))
        [((("t1", v))), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok ([((("t1", v))), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)], .returned v) :=
      evalProgStmt_return _ _ _ _ _ hvar
    have hfwd : stdVecEraseFwd b len cap pos = .ok v := by
      simp only [stdVecEraseFwd, hR]
    have hstmt : evalProgStmt vecGrowProg (F' + 1)
        stdVecEraseFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok ([((("t1", v))), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)], .returned v) := by
      rw [hbody]
      exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCall).trans
        hret
    simp only [evalProgFunc, hbind, hstmt, hfwd]

/-! ## N7d-ii-c: `vec_erase_sum` entry forward + eval -/

/-- Value-level forward for `vec_erase_sum`: `reserve(10)` over the
    empty triple, three fast-path pushes (`1`, `2`, `3`), `begin` +
    one step, the `erase` forwarder at position `1`, two indexed
    reads, `checkedAddI32` once, destructor, return `4`. -/
def vecEraseSumEntryFwd : Result Value :=
  (stdVecReserveFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 64 10)).bind fun v1 =>
  (vecGrowOwned v1).bind fun (b1, l1, c1) =>
  (stdVecPushBackFwd b1 l1 c1 (BitVec.ofNat 32 1)).bind fun v2 =>
  (vecGrowOwned v2).bind fun (b2, l2, c2) =>
  (stdVecPushBackFwd b2 l2 c2 (BitVec.ofNat 32 2)).bind fun v3 =>
  (vecGrowOwned v3).bind fun (b3, l3, c3) =>
  (stdVecPushBackFwd b3 l3 c3 (BitVec.ofNat 32 3)).bind fun v4 =>
  (vecGrowOwned v4).bind fun (b4, l4, c4) =>
  (stdVecBeginFwd).bind fun bgv =>
  (vecGrowU64 bgv).bind fun bpos =>
  (stdVecPlusElFwd bpos (BitVec.ofNat 64 1)).bind fun p1v =>
  (vecGrowU64 p1v).bind fun p1 =>
  (stdVecEraseFwd b4 l4 c4 p1).bind fun v5 =>
  (vecGrowOwned v5).bind fun (b5, l5, c5) =>
  (stdVecGrowIndexFwd b5 l5 (BitVec.ofNat 64 0)).bind fun e0v =>
  (vecGrowI32 e0v).bind fun e0 =>
  (stdVecGrowIndexFwd b5 l5 (BitVec.ofNat 64 1)).bind fun e1v =>
  (vecGrowI32 e1v).bind fun e1 =>
  (checkedAddI32 e0 e1).bind fun s =>
  (stdVecDtorFwd b5 l5 c5).bind fun _ =>
  .ok (.i32 s)

/-- Iterator advance computes `0 + 1` (composer-local twin of
    `vecInsertPlusEl_eq`: the same closed computation, restated so
    `Erase` does not import the whole insert slice). -/
theorem vecErasePlusEl_eq :
    stdVecPlusElFwd (BitVec.ofNat 64 0) (BitVec.ofNat 64 1) =
      .ok (.u64 (BitVec.ofNat 64 1)) := rfl

/-- Third fast-path push writes `3` at index `2`. -/
theorem vecErasePush3_eq :
    stdVecPushBackFwd
      ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2), false⟩ 2 10
      (BitVec.ofNat 32 3) =
      .ok (.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10) := rfl

/-- The `erase` at position `1` shifts `[2, 3)` down and shrinks to
    length `2` (the surviving prefix is `[1, 3]`). -/
theorem vecEraseStep_eq :
    stdVecEraseFwd
      ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩ 3 10
      (BitVec.ofNat 64 1) =
      .ok (.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10) := rfl

/-- Indexed reads pin the two surviving words. -/
theorem vecEraseRead0_eq :
    stdVecGrowIndexFwd
      ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 3), false⟩ 2
      (BitVec.ofNat 64 0) =
      .ok (.i32 (BitVec.ofNat 32 1)) := rfl

/-- Indexed reads pin the two surviving words. -/
theorem vecEraseRead1_eq :
    stdVecGrowIndexFwd
      ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 3), false⟩ 2
      (BitVec.ofNat 64 1) =
      .ok (.i32 (BitVec.ofNat 32 3)) := rfl

/-- The single `nsw` add computes `1 + 3 = 4`. -/
theorem vecEraseAdd_eq :
    checkedAddI32 (BitVec.ofNat 32 1) (BitVec.ofNat 32 3) =
      .ok (BitVec.ofNat 32 4) := rfl

/-- The destructor frees the two-word triple. -/
theorem vecEraseDtor_eq :
    stdVecDtorFwd
      ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 3), false⟩ 2 10 =
      .ok (.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10) := rfl

/-- Mangled name of the closed `vec_erase_sum` entry. -/
def vecEraseSumEntryName : String := "_Z13vec_erase_sumv"

/-- Canonical CoreIR for the closed `vec_erase_sum` entry: default
    ctor, `reserve(10)`, three pushes (`1`, `2`, `3`), `begin` + one
    step, one `erase` (at position `1`, iterator drops), two
    indexed reads, one add, destructor (ii-b proves the forward
    computes `1 + 3 = 4`). -/
def vecEraseSumEntryFunc : Func :=
  ⟨vecEraseSumEntryName, [], .i 32,
   .seq (.callRet "v0" stdVecCtorName [])
   (.seq (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
   (.seq (.callProg "v1" stdVecReserveName ["v0", "n"])
   (.seq (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
   (.seq (.callProg "v2" stdVecPushBackName ["v1", "c0"])
   (.seq (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
   (.seq (.callProg "v3" stdVecPushBackName ["v2", "c1"])
   (.seq (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
   (.seq (.callProg "v4" stdVecPushBackName ["v3", "c2"])
   (.seq (.callRet "bpos" stdVecBeginName ["v4"])
   (.seq (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.callRet "p1" stdVecPlusElName ["bpos", "one"])
   (.seq (.callProg "v5" stdVecEraseName ["v4", "p1"])
   (.seq (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq (.callRet "e0" stdVecGrowIndexName ["v5", "n0"])
   (.seq (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.callRet "e1" stdVecGrowIndexName ["v5", "n1"])
   (.seq (.let_ "s" (.i 32) (.add (.var "e0") (.var "e1")))
   (.seq (.callRet "v6" stdVecDtorName ["v5"])
     (.return_ (.var "s"))))))))))))))))))))⟩

set_option maxRecDepth 8192 in
/-- `emit_correct` for `vec_erase_sum`: the closed entry over the
    grown program agrees with the compute-to-`4` forward. Fuel covers
    the five sequential `callProg` depths (`6 ≤ F`). -/
theorem evalProgFunc_vecEraseSumEntry (F : Nat) (hF : 6 ≤ F) :
    evalProgFunc vecGrowProg F vecEraseSumEntryFunc [] =
      vecEraseSumEntryFwd := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down 5 hF
  have hbind : bindArgs vecEraseSumEntryFunc.args [] = some [] := rfl
  have hbody : vecEraseSumEntryFunc.body =
      .seq (.callRet "v0" stdVecCtorName [])
      (.seq (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
      (.seq (.callProg "v1" stdVecReserveName ["v0", "n"])
      (.seq (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      (.seq (.callProg "v2" stdVecPushBackName ["v1", "c0"])
      (.seq (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      (.seq (.callProg "v3" stdVecPushBackName ["v2", "c1"])
      (.seq (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
      (.seq (.callProg "v4" stdVecPushBackName ["v3", "c2"])
      (.seq (.callRet "bpos" stdVecBeginName ["v4"])
      (.seq (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.callRet "p1" stdVecPlusElName ["bpos", "one"])
      (.seq (.callProg "v5" stdVecEraseName ["v4", "p1"])
      (.seq (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.callRet "e0" stdVecGrowIndexName ["v5", "n0"])
      (.seq (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.callRet "e1" stdVecGrowIndexName ["v5", "n1"])
      (.seq (.let_ "s" (.i 32) (.add (.var "e0") (.var "e1")))
      (.seq (.callRet "v6" stdVecDtorName ["v5"])
        (.return_ (.var "s")))))))))))))))))))) := rfl
  -- Step 1: the default ctor.
  have hargs0 : lookupArgs ([] : Env) [] = some [] := rfl
  have hcall0 : evalFuncFuel (F' + 1) stdVecEmptyCtorFunc [] =
      .ok (.stdVecOwned ⟨[], false⟩ 0 0) :=
    evalFuncFuel_stdVecEmptyCtor _
  have hstepV0 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "v0"
    stdVecCtorName [] ([] : Env) _ stdVecEmptyCtorFunc
    (.stdVecOwned ⟨[], false⟩ 0 0)
    hargs0 findFunc_stdVecEmptyCtor hcall0
  -- Step 2: `n = 10`.
  have hlitN : evalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
      [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 10)) := by
    simp [evalExpr, litVal]
  have hstepN : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
      [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok ([("n", .u64 (BitVec.ofNat 64 10)),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitN
  -- Step 3: `reserve(10)` takes the reallocation arm over the empty
  -- triple (zero words relocated, ten-word spare buffer).
  have hargsR : lookupArgs
      [((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v0", "n"] =
      some [.stdVecOwned ⟨[], false⟩ 0 0,
        .u64 (BitVec.ofNat 64 10)] := by
    simp [lookupArgs, envLookup,
      show ("v0" : String) ≠ "n" by decide]
  have hcallR : evalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      stdVecReserveFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 64 10) :=
    evalProgFunc_stdVecReserve F' _ 0 0 _ rfl (by decide)
      (Nat.zero_le _) (by decide) (by decide) (by omega)
  have hcallR' : evalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      .ok (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10) := by
    rw [hcallR, vecReserveStep_eq]
  have hstepV1 := evalProgStmt_callProg_ok vecGrowProg F' "v1"
    stdVecReserveName ["v0", "n"] _ _ stdVecReserveFunc
    (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)
    hargsR findFunc_stdVecReserve hcallR'
  -- Step 4: `c0 = 1`.
  have hlitC0 : evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      [((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    simp [evalExpr, litVal]
  have hstepC0 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      [((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok ([((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitC0
  -- Step 5: first push (fast path into the spare triple).
  have hargs1 : lookupArgs
      [((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v1", "c0"] =
      some [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] := by
    simp [lookupArgs, envLookup,
      show ("v1" : String) ≠ "c0" by decide]
  have hcallP1 : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      stdVecPushBackFwd ⟨List.replicate 10 0, false⟩ 0 10
        (BitVec.ofNat 32 1) :=
    evalProgFunc_stdVecPushBack F' _ 0 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP1' : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      .ok (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10) := by
    rw [hcallP1, vecReservePush1_eq]
  have hstepV2 := evalProgStmt_callProg_ok vecGrowProg F' "v2"
    stdVecPushBackName ["v1", "c0"] _ _ stdVecPushBackFunc
    (.stdVecOwned
      ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10)
    hargs1 findFunc_stdVecPushBack hcallP1'
  -- Step 6: `c1 = 2`.
  have hlitC1 : evalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
      [((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    simp [evalExpr, litVal]
  have hstepC1 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      [((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok ([((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitC1
  -- Step 7: second push (`2` at index `1`).
  have hargs2 : lookupArgs
      [((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v2", "c1"] =
      some [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 2)] := by
    simp [lookupArgs, envLookup,
      show ("v2" : String) ≠ "c1" by decide]
  have hcallP2 : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 2)] =
      stdVecPushBackFwd
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10 (BitVec.ofNat 32 2) :=
    evalProgFunc_stdVecPushBack F' _ 1 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP2' : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 2)] =
      .ok (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10) := by
    rw [hcallP2, vecReservePush2_eq]
  have hstepV3 := evalProgStmt_callProg_ok vecGrowProg F' "v3"
    stdVecPushBackName ["v2", "c1"] _ _ stdVecPushBackFunc
    (.stdVecOwned
      ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2), false⟩ 2 10)
    hargs2 findFunc_stdVecPushBack hcallP2'
  -- Step 8: `c2 = 3`.
  have hlitC2 : evalExpr (.lit (.i32 (BitVec.ofNat 32 3)))
      [((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    simp [evalExpr, litVal]
  have hstepC2 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
      [((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok ([((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitC2
  -- Step 9: third push (`3` at index `2`).
  have hargs3 : lookupArgs
      [((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v3", "c2"] =
      some [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .i32 (BitVec.ofNat 32 3)] := by
    simp [lookupArgs, envLookup,
      show ("v3" : String) ≠ "c2" by decide]
  have hcallP3 : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .i32 (BitVec.ofNat 32 3)] =
      stdVecPushBackFwd
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩
        2 10 (BitVec.ofNat 32 3) :=
    evalProgFunc_stdVecPushBack F' _ 2 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP3' : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .i32 (BitVec.ofNat 32 3)] =
      .ok (.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10) := by
    rw [hcallP3, vecErasePush3_eq]
  have hstepV4 := evalProgStmt_callProg_ok vecGrowProg F' "v4"
    stdVecPushBackName ["v3", "c2"] _ _ stdVecPushBackFunc
    (.stdVecOwned
      ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
      3 10)
    hargs3 findFunc_stdVecPushBack hcallP3'
  -- Step 10: `begin` reads the base offset (`0`).
  have hargsB : lookupArgs
      [((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v4"] =
      some [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10] := by
    simp [lookupArgs, envLookup]
  have hcallB : evalFuncFuel (F' + 1) stdVecBeginFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10] =
      stdVecBeginFwd :=
    evalFuncFuel_stdVecBegin _ _ _ _
  have hcallB' : evalFuncFuel (F' + 1) stdVecBeginFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    rw [hcallB]; rfl
  have hstepBpos := evalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "bpos" stdVecBeginName ["v4"] _ _ stdVecBeginFunc
      (.u64 (BitVec.ofNat 64 0))
      hargsB findFunc_stdVecBegin hcallB'
  -- Step 11: `one = 1`.
  have hlitOne : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hstepOne : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      [((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok ([((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitOne
  -- Step 12: `begin() + 1` advances to position `1`.
  have hargsP1 : lookupArgs
      [((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["bpos", "one"] =
      some [.u64 (BitVec.ofNat 64 0), .u64 (BitVec.ofNat 64 1)] := by
    simp [lookupArgs, envLookup,
      show ("bpos" : String) ≠ "one" by decide]
  have hcallP1x : evalFuncFuel (F' + 1) stdVecPlusElFunc
      [.u64 (BitVec.ofNat 64 0), .u64 (BitVec.ofNat 64 1)] =
      stdVecPlusElFwd (BitVec.ofNat 64 0) (BitVec.ofNat 64 1) :=
    evalFuncFuel_stdVecPlusEl _ _ _
  have hcallP1x' : evalFuncFuel (F' + 1) stdVecPlusElFunc
      [.u64 (BitVec.ofNat 64 0), .u64 (BitVec.ofNat 64 1)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    rw [hcallP1x]; rfl
  have hstepP1 := evalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "p1" stdVecPlusElName ["bpos", "one"] _ _ stdVecPlusElFunc
      (.u64 (BitVec.ofNat 64 1))
      hargsP1 findFunc_stdVecPlusEl hcallP1x'
  -- Step 13: the `erase` at position `1` (shift arm: `pos + 1 ≠ len`).
  have hargsV5 : lookupArgs
      [((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v4", "p1"] =
      some [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10,
        .u64 (BitVec.ofNat 64 1)] := by
    simp [lookupArgs, envLookup,
      show ("v4" : String) ≠ "p1" by decide,
      show ("v4" : String) ≠ "one" by decide,
      show ("v4" : String) ≠ "bpos" by decide]
  have hcallV5 : evalProgFunc vecGrowProg F' stdVecEraseFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10,
        .u64 (BitVec.ofNat 64 1)] =
      stdVecEraseFwd
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10 (BitVec.ofNat 64 1) :=
    evalProgFunc_stdVecErase F' _ 3 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallV5' : evalProgFunc vecGrowProg F' stdVecEraseFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10,
        .u64 (BitVec.ofNat 64 1)] =
      .ok (.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10) := by
    rw [hcallV5, vecEraseStep_eq]
  have hstepV5 := evalProgStmt_callProg_ok vecGrowProg F' "v5"
    stdVecEraseName ["v4", "p1"] _ _ stdVecEraseFunc
    (.stdVecOwned
      ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 3), false⟩ 2 10)
    hargsV5 findFunc_stdVecErase hcallV5'
  -- Step 14: `n0 = 0`.
  have hlitN0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hstepN0 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok ([((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitN0
  -- Step 15: first read pins `1`.
  have hargsE0 : lookupArgs
      [((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v5", "n0"] =
      some [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] := by
    simp [lookupArgs, envLookup,
      show ("v5" : String) ≠ "n0" by decide]
  have hget0 : (((((List.replicate 10 0).set 0
      (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 2)).set 2
      (BitVec.ofNat 32 3)).set 1
      (BitVec.ofNat 32 3))[(BitVec.ofNat 64 0).toNat]? =
      some (BitVec.ofNat 32 1) := by decide
  have hlt0 : (BitVec.ofNat 64 0).toNat < 2 := by decide
  have hcallE0 : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] =
      stdVecGrowIndexFwd
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2
        (BitVec.ofNat 64 0) :=
    evalFuncFuel_stdVecGrowIndex _ _ 2 10 _ rfl _ hget0 hlt0
  have hcallE0' : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    rw [hcallE0, vecEraseRead0_eq]
  have hstepE0 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "e0"
    stdVecGrowIndexName ["v5", "n0"] _ _ stdVecGrowIndexFunc
    (.i32 (BitVec.ofNat 32 1))
    hargsE0 findFunc_stdVecGrowIndex hcallE0'
  -- Step 16: `n1 = 1`.
  have hlitN1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hstepN1 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      [((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok ([((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitN1
  -- Step 17: second read pins `3`.
  have hargsE1 : lookupArgs
      [((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v5", "n1"] =
      some [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] := by
    simp [lookupArgs, envLookup,
      show ("v5" : String) ≠ "n1" by decide,
      show ("v5" : String) ≠ "e0" by decide,
      show ("v5" : String) ≠ "n0" by decide]
  have hget1 : (((((List.replicate 10 0).set 0
      (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 2)).set 2
      (BitVec.ofNat 32 3)).set 1
      (BitVec.ofNat 32 3))[(BitVec.ofNat 64 1).toNat]? =
      some (BitVec.ofNat 32 3) := by decide
  have hlt1 : (BitVec.ofNat 64 1).toNat < 2 := by decide
  have hcallE1 : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] =
      stdVecGrowIndexFwd
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2
        (BitVec.ofNat 64 1) :=
    evalFuncFuel_stdVecGrowIndex _ _ 2 10 _ rfl _ hget1 hlt1
  have hcallE1' : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    rw [hcallE1, vecEraseRead1_eq]
  have hstepE1 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "e1"
    stdVecGrowIndexName ["v5", "n1"] _ _ stdVecGrowIndexFunc
    (.i32 (BitVec.ofNat 32 3))
    hargsE1 findFunc_stdVecGrowIndex hcallE1'
  -- Step 18: `s = e0 + e1 = 4`.
  have he0 : envLookup
      [((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] "e0" =
      some (.i32 (BitVec.ofNat 32 1)) := by
    simp [envLookup,
      show ("e0" : String) ≠ "e1" by decide,
      show ("e0" : String) ≠ "n1" by decide]
  have he1 : envLookup
      [((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] "e1" =
      some (.i32 (BitVec.ofNat 32 3)) := by
    simp [envLookup]
  have hsE : evalExpr (.add (.var "e0") (.var "e1"))
      [((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 4)) := by
    cir_step evalExpr [he0, he1, vecEraseAdd_eq]
  have hstepS : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "s" (.i 32) (.add (.var "e0") (.var "e1")))
      [((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok ([((("s", .i32 (BitVec.ofNat 32 4)))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hsE
  -- Step 19: destructor frees the triple.
  have hargsD : lookupArgs
      [((("s", .i32 (BitVec.ofNat 32 4)))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v5"] =
      some [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10] := by
    simp [lookupArgs, envLookup,
      show ("v5" : String) ≠ "s" by decide,
      show ("v5" : String) ≠ "e1" by decide,
      show ("v5" : String) ≠ "n1" by decide,
      show ("v5" : String) ≠ "e0" by decide,
      show ("v5" : String) ≠ "n0" by decide]
  have hcallD : evalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10] =
      stdVecDtorFwd
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2
        10 :=
    evalFuncFuel_stdVecDtor _ _ _ _ (by decide)
  have hcallD' : evalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10] =
      .ok (.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10) := by
    rw [hcallD, vecEraseDtor_eq]
  have hstepV6 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "v6"
    stdVecDtorName ["v5"] _ _ stdVecDtorFunc
    (.stdVecOwned
      ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 3), true⟩
      2 10)
    hargsD findFunc_stdVecDtor hcallD'
  -- Step 20: return `4`.
  have hrE : evalExpr (.var "s")
      [((("v6", .stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10))),
        ((("s", .i32 (BitVec.ofNat 32 4)))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 4)) := by
    simp [evalExpr, envLookup]
  have hret : evalProgStmt vecGrowProg (F' + 1)
      (.return_ (.var "s"))
      [((("v6", .stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10))),
        ((("s", .i32 (BitVec.ofNat 32 4)))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok ([((("v6", .stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10))),
        ((("s", .i32 (BitVec.ofNat 32 4)))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)],
        .returned (.i32 (BitVec.ofNat 32 4))) :=
    evalProgStmt_return _ _ _ _ _ hrE
  have hstmt : evalProgStmt vecGrowProg (F' + 1)
      vecEraseSumEntryFunc.body [] =
      .ok ([((("v6", .stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10))),
        ((("s", .i32 (BitVec.ofNat 32 4)))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)],
        .returned (.i32 (BitVec.ofNat 32 4))) := by
    rw [hbody]
    exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV0).trans
      ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepN).trans
        ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV1).trans
          ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepC0).trans
            ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV2).trans
              ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepC1).trans
                ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV3).trans
                  ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepC2).trans
                    ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV4).trans
                      ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepBpos).trans
                        ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepOne).trans
                          ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepP1).trans
                            ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV5).trans
                              ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepN0).trans
                                ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepE0).trans
                                  ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepN1).trans
                                    ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepE1).trans
                                      ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepS).trans
                                        ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV6).trans
                                          hret))))))))))))))))))
  have hfwd : vecEraseSumEntryFwd = .ok (.i32 (BitVec.ofNat 32 4)) := by
    simp only [vecEraseSumEntryFwd, vecReserveStep_eq,
      vecReservePush1_eq, vecReservePush2_eq, vecErasePush3_eq,
      vecErasePlusEl_eq, vecEraseStep_eq, vecEraseRead0_eq,
      vecEraseRead1_eq, vecEraseAdd_eq, vecEraseDtor_eq,
      vecGrow_bind_ok, vecGrowOwned, vecGrowU64, vecGrowI32,
      stdVecBeginFwd]
  simp only [evalProgFunc, hbind, hstmt, hfwd]

