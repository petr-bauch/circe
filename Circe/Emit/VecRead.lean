/-
Circe.Emit.VecRead — N4d-iv-a `std::vector<int32_t>` reads: the
`size` leaf + the `operator[]` fused leaf + the `vec_read_sum`
index-loop entry.

The corpus (`tests/cpp/vec_read_sum.cpp`: entry takes the vector by
`const&`, sums `v[i]` over `v.size()`) captures only three defs —
no ctor/dtor/push/realloc reach the gate (growth is N4d-iv-b). The
chain is depth-2 (`vec_read_sum` → `size` → the `_M_finish` /
`_M_start` loads + `ptr_diff` + `cast`; `vec_read_sum` →
`operator[]` → the `_M_start` load + `ptr_stride`), but `size` has
no dead-assert skeleton at all (unlike span's `operator[]`): the
`ptr_diff` over the two loaded pointers plus the `s64 → u64` cast
is straight-line code.

Functionalization fuses edges exactly like the N4d-iii span slice:
`size` fuses the double `_M_impl` projection pair (`_M_finish` +
`_M_start` loads) + `ptr_diff` + `cast` into the `stdVecLen` read;
`operator[]` fuses the `_M_impl` projection + `_M_start` load +
`ptr_stride` + both loads into the `stdVecAt` read. The length
consistency (`(finish - start) / 4 = length`) is enforced by the
gate pinning the projection/`ptr_diff`/`cast` text, not by the
model — same division of labor as span's extent word. The
`vec_read_sum` entry loop fuses to a call-free `while_` leaf over
`stdVecLen`/`stdVecAt` (the S3a `skip_sum` precedent: loop-env
family + suffix fold + fuel side condition).
-/
import Circe.Emit.Fragment

/-! ## N4d-iv-a: `std::vector` size, index, entry -/

/-- The 3-word `std::vector<int32_t>` object model: the `_M_start` /
    `_M_finish` / `_M_end_of_storage` words (all erase in the value
    model, which reifies the element words as `stdVecVal`). -/
def stdVecObjTy : CType := .struct "std::vector<int>" [.u 64, .u 64, .u 64]

/-- Mangled callee names in `tests/cpp/vec_read_sum.cpp`. -/
def stdVecSizeName : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"
def stdVecIndexName : String :=
  "_ZNKSt6vectorIiSaIiEEixEm"
def stdVecReadSumName : String :=
  "_Z12vec_read_sumRKSt6vectorIiSaIiEE"

/-- Canonical CoreIR for `size`: the double `_M_impl` projection
    pair (`_M_finish` + `_M_start` loads) + `ptr_diff` + `cast`
    fused into the `stdVecLen` read. -/
def stdVecSizeFunc : Func :=
  ⟨stdVecSizeName,
   [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow }],
   .u 64,
   .return_ (.stdVecLen "s")⟩

/-- Canonical CoreIR for `operator[]`: the `_M_impl` projection +
    `_M_start` load + `ptr_stride` + both loads fused into the
    `stdVecAt` read (no assert skeleton at all — cf. the module
    docstring; the caller-side load is fused downstream, cf.
    `spanIndexFunc`). -/
def stdVecIndexFunc : Func :=
  ⟨stdVecIndexName,
   [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "n", ty := .u 64, role := .owned }],
   .i 32,
   .return_ (.stdVecAt "s" (.var "n"))⟩

/-- Loop body: `t = t+v[i]; i = i+1` (the `cir.for` body + step
    regions fused; the per-iteration `size()`/`operator[]` calls
    read the fused `stdVecLen`/`stdVecAt`). -/
def stdVecBody : CStmt :=
  .seq (.assign "t" (.add (.var "t") (.stdVecAt "s" (.var "i"))))
    (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- Loop: `while (i < s.size()) { ... }`. -/
def stdVecWhile : CStmt :=
  .while_ (.ult (.var "i") (.stdVecLen "s")) stdVecBody

/-- Canonical CoreIR for `vec_read_sum`: the accumulator/index
    initialization plus the call-free index loop (the S3a `skip_sum`
    shape: `cir.for` over `u64` with an `nsw` add maps to
    `while_` + `ult` + `add` + `uadd`). -/
def stdVecReadSumFunc : Func :=
  ⟨stdVecReadSumName,
   [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow }],
   .i 32,
   .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq stdVecWhile
         (.return_ (.var "t"))))⟩

/-- Value-level forward for `size`: the reified length as a
    `u64` word. -/
def stdVecSizeFwd (l : List (BitVec 32)) : Result Value :=
  .ok (.u64 (BitVec.ofNat 64 l.length))

/-- Value-level forward for `operator[]`: the word at `u64` index
    `n`, `OOB` off the end (mirrors `spanIndexFwd`). -/
def stdVecIndexFwd (l : List (BitVec 32)) (n : BitVec 64) : Result Value :=
  match l[n.toNat]? with
  | some x => .ok (.i32 x)
  | none => .error .OOB

/-- Checked-add fold over the suffix: the `nsw` accumulation with
    loud err-propagation (cf. `spanFold`, generalized to a dynamic
    length; structural recursion over the suffix list, so unfolding
    is clean — the loop invariant bridges via `stdVecFold_drop`). -/
def stdVecFold : List (BitVec 32) → BitVec 32 → Result (BitVec 32)
  | [], acc => .ok acc
  | x :: xs, acc =>
    match checkedAddI32 acc x with
    | .error e => .error e
    | .ok a => stdVecFold xs a

/-- Value-level forward for `vec_read_sum`: the checked-add fold
    from `0` over the reified words. -/
def stdVecReadSumFwd (l : List (BitVec 32)) : Result Value :=
  .i32 <$> stdVecFold l (BitVec.ofNat 32 0)

/-- The forward on a failed fold is the error (exact `<$>`
    rewrite, cf. `i32_map_error`). -/
theorem stdVecReadSumFwd_err (l : List (BitVec 32)) (e : Panic)
    (hfold : stdVecFold l (BitVec.ofNat 32 0) = .error e) :
    stdVecReadSumFwd l = .error e := by
  simp only [stdVecReadSumFwd, hfold, i32_map_error]

/-- The forward on a successful fold is the mapped word. -/
theorem stdVecReadSumFwd_ok (l : List (BitVec 32)) (acc' : BitVec 32)
    (hfold : stdVecFold l (BitVec.ofNat 32 0) = .ok acc') :
    stdVecReadSumFwd l = .ok (.i32 acc') := by
  simp only [stdVecReadSumFwd, hfold, i32_map_ok]

/-- Env fact for the `size` shape. -/
theorem envLookup_stdVecSize_s (l : List (BitVec 32)) :
    envLookup [("s", .stdVecVal l)] "s" = some (.stdVecVal l) := by
  simp [envLookup]

/-- `emit_correct` for `size` (total on vectors). -/
theorem evalFuncFuel_stdVecSize (F : Nat) (l : List (BitVec 32)) :
    evalFuncFuel F stdVecSizeFunc [.stdVecVal l] = stdVecSizeFwd l := by
  have hbind : bindArgs stdVecSizeFunc.args [.stdVecVal l] =
      some [("s", .stdVecVal l)] := rfl
  have hbody : stdVecSizeFunc.body = .return_ (.stdVecLen "s") := rfl
  have hs := envLookup_stdVecSize_s l
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, stdVecSizeFwd, hs]

/-- Env facts for the `operator[]` shape. -/
theorem envLookup_stdVecIndex_s (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("s", .stdVecVal l), ("n", .u64 n)] "s" =
      some (.stdVecVal l) := by
  simp [envLookup]

theorem envLookup_stdVecIndex_n (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("s", .stdVecVal l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
  simp [envLookup, show ("n" : String) ≠ "s" by decide]

/-- `emit_correct` for `operator[]` (all inputs, hit and `OOB`). -/
theorem evalFuncFuel_stdVecIndex (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) :
    evalFuncFuel F stdVecIndexFunc [.stdVecVal l, .u64 n] =
      stdVecIndexFwd l n := by
  have hbind : bindArgs stdVecIndexFunc.args [.stdVecVal l, .u64 n] =
      some [("s", .stdVecVal l), ("n", .u64 n)] := rfl
  have hbody : stdVecIndexFunc.body =
      .return_ (.stdVecAt "s" (.var "n")) := rfl
  have hs := envLookup_stdVecIndex_s l n
  have hn := envLookup_stdVecIndex_n l n
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, stdVecIndexFwd, hs, hn] <;>
    (cases h : l[n.toNat]? <;> simp_all)

/-- Loop environments: `u64` index `k` and accumulator, view fixed. -/
def mkStdVecEnv (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32) : Env :=
  [("i", .u64 (BitVec.ofNat 64 k)), ("t", .i32 acc), ("s", .stdVecVal l)]

theorem mkStdVecEnv_i (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32) :
    envLookup (mkStdVecEnv l k acc) "i" =
      some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkStdVecEnv, envLookup]

theorem mkStdVecEnv_t (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32) :
    envLookup (mkStdVecEnv l k acc) "t" = some (.i32 acc) := by
  simp [mkStdVecEnv, envLookup, show ("t" : String) ≠ "i" by decide]

theorem mkStdVecEnv_s (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32) :
    envLookup (mkStdVecEnv l k acc) "s" = some (.stdVecVal l) := by
  simp [mkStdVecEnv, envLookup, show ("s" : String) ≠ "i" by decide,
    show ("s" : String) ≠ "t" by decide]

/-- Updating `t` stays in the env family. -/
theorem stdVecEnv_update_t (l : List (BitVec 32)) (k : Nat)
    (acc v : BitVec 32) :
    envUpdate (mkStdVecEnv l k acc) "t" (.i32 v) =
      some (mkStdVecEnv l k v) := by
  simp [mkStdVecEnv, envUpdate, show ("t" : String) ≠ "i" by decide]

/-- Updating `i` stays in the env family. -/
theorem stdVecEnv_update_i (l : List (BitVec 32)) (k k' : Nat)
    (acc : BitVec 32) :
    envUpdate (mkStdVecEnv l k acc) "i" (.u64 (BitVec.ofNat 64 k')) =
      some (mkStdVecEnv l k' acc) := by
  simp [mkStdVecEnv, envUpdate]

/-- The loop condition reads the `u64` index against the reified
    length (both sides need the `2^64` bound: the index from the
    fuel-side descent, the length from the `hl64` hypothesis — a
    real vector is address-bounded, so this excludes only the
    `ofNat` wraparound case, never a real input). -/
theorem stdVecCond_eval (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32)
    (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.stdVecLen "s")) (mkStdVecEnv l k acc) =
      .ok (.b (decide (k < l.length))) := by
  have hi := mkStdVecEnv_i l k acc
  have hs := mkStdVecEnv_s l k acc
  have hlen : (BitVec.ofNat 64 l.length).toNat = l.length :=
    ofNat64_toNat _ hl64
  simp [evalExpr, hi, hs, ofNat64_ult k _ hk64, hlen]

/-- Body with a successful add: accumulate and step (any fuel). -/
theorem stdVecBody_step_ok (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x a : BitVec 32)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .ok a) :
    evalStmtFuel F stdVecBody (mkStdVecEnv l k acc) =
      .ok (mkStdVecEnv l (k + 1) a, .fellThrough) := by
  have hi := mkStdVecEnv_i l k acc
  have ht := mkStdVecEnv_t l k acc
  have hs := mkStdVecEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : evalExpr (.add (.var "t") (.stdVecAt "s" (.var "i")))
        (mkStdVecEnv l k acc) = .ok (.i32 a) := by
    cir_step evalExpr [ht, hi, hs, htn, hget, hc]
  have hincr : evalExpr (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
        (mkStdVecEnv l k a) =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h1 := mkStdVecEnv_i l k a
    simp only [evalExpr, litVal, h1, ofNat64_add_one]
  have up1 := stdVecEnv_update_t l k acc a
  have up2 := stdVecEnv_update_i l k (k + 1) a
  cases F <;>
    simp [stdVecBody, evalStmtFuel, evalStmtZero, evalStmtWith,
      hadd, hincr, up1, up2]

/-- Body with an overflowing add: the `nsw` error is loud, the
    index never advances (any fuel). -/
theorem stdVecBody_step_err (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x : BitVec 32) (e : Panic)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .error e) :
    evalStmtFuel F stdVecBody (mkStdVecEnv l k acc) = .error e := by
  have hi := mkStdVecEnv_i l k acc
  have ht := mkStdVecEnv_t l k acc
  have hs := mkStdVecEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : evalExpr (.add (.var "t") (.stdVecAt "s" (.var "i")))
        (mkStdVecEnv l k acc) = .error e := by
    cir_step evalExpr [ht, hi, hs, htn, hget, hc]
  cases F <;>
    simp [stdVecBody, evalStmtFuel, evalStmtZero, evalStmtWith, hadd]

/-- The fold over a dropped suffix unfolds at the live head
    (proved once by list induction, so the loop proof never
    unfolds a well-founded fixpoint). -/
theorem stdVecFold_drop (l : List (BitVec 32)) (k : Nat)
    (acc : BitVec 32) :
    stdVecFold (l.drop k) acc =
      match l[k]? with
      | none => .ok acc
      | some x =>
        match checkedAddI32 acc x with
        | .error e => .error e
        | .ok a => stdVecFold (l.drop (k + 1)) a := by
  induction l generalizing k with
  | nil => simp [stdVecFold]
  | cons y ys ih =>
    cases k with
    | zero => simp [stdVecFold]
    | succ k =>
      simp only [List.drop_succ_cons]
      exact ih k

/-- Unfolding the suffix fold at a live index. -/
theorem stdVecFold_step (l : List (BitVec 32)) (k : Nat)
    (acc x : BitVec 32)
    (hget : l[k]? = some x) :
    stdVecFold (l.drop k) acc =
      match checkedAddI32 acc x with
      | .error e => .error e
      | .ok a => stdVecFold (l.drop (k + 1)) a := by
  conv => lhs; rw [stdVecFold_drop]
  simp [hget]

/-- Unfolding the suffix fold past the end. -/
theorem stdVecFold_nil (l : List (BitVec 32)) (k : Nat)
    (acc : BitVec 32)
    (hget : l[k]? = none) :
    stdVecFold (l.drop k) acc = .ok acc := by
  conv => lhs; rw [stdVecFold_drop]
  simp [hget]

/-- Loop correctness: folds the checked-add suffix, exits with
    `i = length` (fuel-generalized; the `+1` absorbs the final exit
    iteration, so the zero-fuel case is vacuous — the S3a
    `skipWhile_correct` shape). -/
theorem stdVecWhile_correct (l : List (BitVec 32))
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ l.length) (hl64 : l.length < 2 ^ 64)
    (hF : l.length - k + 1 ≤ F) :
    evalStmtFuel F stdVecWhile (mkStdVecEnv l k acc) =
      match stdVecFold (l.drop k) acc with
      | .error e => .error e
      | .ok acc' => .ok (mkStdVecEnv l l.length acc', .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < l.length
    · have hk64 : k < 2 ^ 64 := by omega
      have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hlt
      have hcond : evalExpr (.ult (.var "i") (.stdVecLen "s"))
            (mkStdVecEnv l k acc) = .ok (.b true) := by
        simpa [hlt] using (stdVecCond_eval l k acc hk64 hl64)
      have hunfold := stdVecFold_step l k acc l[k] hget
      cases hc : checkedAddI32 acc l[k] with
      | error e =>
        have hbody := stdVecBody_step_err F l k acc l[k] e hlt hk64 hl64
          hget hc
        have hstep : evalStmtFuel (F + 1) stdVecWhile (mkStdVecEnv l k acc)
            = .error e := by
          simp [stdVecWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep, hunfold, hc]
      | ok a =>
        have hbody := stdVecBody_step_ok F l k acc l[k] a hlt hk64 hl64
          hget hc
        have hstep : evalStmtFuel (F + 1) stdVecWhile (mkStdVecEnv l k acc)
            = evalStmtFuel F stdVecWhile (mkStdVecEnv l (k + 1) a) := by
          simp [stdVecWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep, hunfold, hc]
        exact ih (k + 1) a (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.stdVecLen "s"))
            (mkStdVecEnv l l.length acc) = .ok (.b false) := by
        have hfalse : (decide (l.length < l.length)) = false := by
          simp
        have hk64 : l.length < 2 ^ 64 := hl64
        have h := stdVecCond_eval l l.length acc hk64 hl64
        rwa [hfalse] at h
      have hnone : l[l.length]? = none :=
        List.getElem?_eq_none (Nat.le_refl _)
      have hnil : stdVecFold [] acc = .ok acc := rfl
      simp [stdVecWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil]

/-- `emit_correct` for `vec_read_sum`, fuel-generalized (the S3a
    `evalFuncFuel_skip` shape; the fuel hypothesis is the slice's
    dynamic-length side condition, discharged by `omega` at the
    default fuel for short vectors). -/
theorem evalFuncFuel_stdVecReadSum (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    evalFuncFuel F stdVecReadSumFunc [.stdVecVal l] = stdVecReadSumFwd l := by
  have hbind : bindArgs stdVecReadSumFunc.args [.stdVecVal l] =
      some [("s", .stdVecVal l)] := rfl
  have hbody : stdVecReadSumFunc.body =
      .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq stdVecWhile
            (.return_ (.var "t")))) := rfl
  have henv : [("i", .u64 (BitVec.ofNat 64 0)),
        ("t", .i32 (BitVec.ofNat 32 0)),
        ("s", .stdVecVal l)]
      = mkStdVecEnv l 0 (BitVec.ofNat 32 0) := rfl
  cases hfold : stdVecFold l (BitVec.ofNat 32 0) with
  | error e =>
    have hsum0 : stdVecReadSumFwd l = .error e := stdVecReadSumFwd_err l e hfold
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            stdVecWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0)) = .error e := by
        have h := stdVecWhile_correct l 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, stdVecReadSumFunc, bindArgs, evalStmtFuel,
        evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopH0, hsum0]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            stdVecWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0)) = .error e := by
        have h := stdVecWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, stdVecReadSumFunc, bindArgs, evalStmtFuel,
        evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopS, hsum0]
  | ok acc' =>
    have hsret : envLookup (mkStdVecEnv l l.length acc') "t" =
        some (.i32 acc') :=
      mkStdVecEnv_t l l.length acc'
    have hsum : stdVecReadSumFwd l = .ok (.i32 acc') :=
      stdVecReadSumFwd_ok l acc' hfold
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            stdVecWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0)) =
            .ok (mkStdVecEnv l l.length acc', .fellThrough) := by
        have h := stdVecWhile_correct l 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, stdVecReadSumFunc, bindArgs, evalStmtFuel,
        evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopH0, hsret, hsum]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            stdVecWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0)) =
            .ok (mkStdVecEnv l l.length acc', .fellThrough) := by
        have h := stdVecWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, stdVecReadSumFunc, bindArgs, evalStmtFuel,
        evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopS, hsret, hsum]

/-- `emit_correct` for `vec_read_sum` at the default fuel — for short
    vectors (the driver only feeds lengths `≤ 8`, far below
    `EVAL_FUEL = 4096`; longer vectors need an explicit fuel
    hypothesis, the honest dynamic-length side condition). -/
theorem emit_correct_stdVecReadSum (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hlen : l.length + 1 ≤ EVAL_FUEL) :
    evalFunc stdVecReadSumFunc [.stdVecVal l] = stdVecReadSumFwd l :=
  evalFuncFuel_stdVecReadSum EVAL_FUEL l hl64 hlen
