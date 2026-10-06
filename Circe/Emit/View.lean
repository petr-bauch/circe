/-
Circe.Emit.View — N7a `std::string_view` range-for sum: the `begin`
/ `end` iterator leaves + the `view_sum` pointer-chase entry.

The C++ range-for lowers to `begin()` / `end` calls plus a
`cir.for` whose condition compares two `!cir.ptr<!s8i>` values
(`cir.cmp ne`), whose body dereferences the begin pointer (`s8i`
load + `s8i -> s32i` sext + `nsw` add), and whose step advances it
by one (`cir.ptr_stride` with an `s32` stride). The transfer
normalizes this pointer-chase loop to an index loop over erased
`u64` offsets (the N4d-iv-b1 iterator precedent: positions erase
to offsets, `begin` to `0`, `end` to `len`):

- `begin` (`_M_str` load, call-free) fuses to the `0` offset;
- `end` (`_M_str` + `_M_len` loads + `ptr_stride`, call-free)
  fuses to the `len` offset (`viewLen` read);
- the entry fuses the two call sites + the chase loop to a
  call-free `while_` over `viewLen`/`viewAt` (the S3a `skip_sum`
  precedent). The normalization is by construction of the
  canonical `Func`: `ne` on stride-linked pointers with a fixed
  base and unit stride coincides with `i < len` on offsets, and
  each correspondence is pinned textually by the gate
  (`isViewSumShape`: exactly one `cir.cmp ne` on pointers, one
  `s32`-stride `ptr_stride`, one `s8i` load, one integral
  `s8i -> s32i` cast, one `nsw` add) and checked empirically by
  the native differential test.

The viewed bytes reify as `viewVal` (`List (BitVec 8)`); `viewAt`
delivers the sign-extended `i32` (x86 `char` is signed — the
high-bit diff driver pins this against native; see
`docs/VERIFYING.md`). `OOB` off the end mirrors `spanAt`.
-/
import Circe.Emit.Fragment

/-! ## N7a: `std::string_view` begin / end / entry -/

/-- The 2-word `std::string_view` object model: the length word
    plus the base-address word (both erase in the value model,
    which reifies the viewed bytes as `viewVal`). -/
def viewObjTy : CType := .struct "std::string_view<char>" [.u 64, .u 64]

/-- Mangled callee names in `tests/cpp/view_sum.cpp`. -/
def viewBeginName : String :=
  "_ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv"
def viewEndName : String :=
  "_ZNKSt17basic_string_viewIcSt11char_traitsIcEE3endEv"
def viewSumName : String :=
  "_Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE"

/-- Canonical CoreIR for `begin`: the `_M_str` load fuses to the
    erased `0` offset (cf. `stdVecBeginFunc`). -/
def viewBeginFunc : Func :=
  ⟨viewBeginName,
   [{ name := "s", ty := viewObjTy, role := .sharedBorrow }],
   .u 64,
   .return_ (.lit (.u64 (BitVec.ofNat 64 0)))⟩

/-- Canonical CoreIR for `end`: the `_M_str` / `_M_len` loads +
    `ptr_stride` fuse to the `len` offset (cf. `stdVecEndFunc`). -/
def viewEndFunc : Func :=
  ⟨viewEndName,
   [{ name := "s", ty := viewObjTy, role := .sharedBorrow }],
   .u 64,
   .return_ (.viewLen "s")⟩

/-- Loop body: `t = t+sext(s[i]); i = i+1` (the chase-loop body +
    step regions fused; the per-iteration pointer chase reads the
    fused `viewAt`). -/
def viewBody : CStmt :=
  .seq (.assign "t" (.add (.var "t") (.viewAt "s" (.var "i"))))
    (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- Loop: `while (i < s.size()) { ... }` (the normalized form of
    the `begin != end` chase). -/
def viewWhile : CStmt :=
  .while_ (.ult (.var "i") (.viewLen "s")) viewBody

/-- Canonical CoreIR for `view_sum`: the accumulator/index
    initialization plus the call-free index loop. -/
def viewSumFunc : Func :=
  ⟨viewSumName,
   [{ name := "s", ty := viewObjTy, role := .sharedBorrow }],
   .i 32,
   .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq viewWhile
         (.return_ (.var "t"))))⟩

/-- Value-level forward for `begin`. -/
def viewBeginFwd : Result Value :=
  .ok (.u64 (BitVec.ofNat 64 0))

/-- Value-level forward for `end`. -/
def viewEndFwd (l : List (BitVec 8)) : Result Value :=
  .ok (.u64 (BitVec.ofNat 64 l.length))

/-- `emit_correct` for `begin` (any fuel). -/
theorem evalFuncFuel_viewBegin (F : Nat) (l : List (BitVec 8)) :
    evalFuncFuel F viewBeginFunc [.viewVal l] = viewBeginFwd := by
  have hbind : bindArgs viewBeginFunc.args [.viewVal l] =
      some [("s", .viewVal l)] := rfl
  have hbody : viewBeginFunc.body =
      .return_ (.lit (.u64 (BitVec.ofNat 64 0))) := rfl
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, viewBeginFwd]

/-- Env fact for the `end` shape. -/
theorem envLookup_viewEnd_s (l : List (BitVec 8)) :
    envLookup [("s", .viewVal l)] "s" = some (.viewVal l) := by
  simp [envLookup]

/-- `emit_correct` for `end` (any fuel). -/
theorem evalFuncFuel_viewEnd (F : Nat) (l : List (BitVec 8)) :
    evalFuncFuel F viewEndFunc [.viewVal l] = viewEndFwd l := by
  have hbind : bindArgs viewEndFunc.args [.viewVal l] =
      some [("s", .viewVal l)] := rfl
  have hbody : viewEndFunc.body = .return_ (.viewLen "s") := rfl
  have hs := envLookup_viewEnd_s l
  have hlen : evalExpr (.viewLen "s") [("s", .viewVal l)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_viewLen_some "s" _ l hs
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, hlen, viewEndFwd]

/-- Checked-add fold over the suffix: the `nsw` accumulation with
    loud err-propagation, each byte sign-extended at the head
    (cf. `spanFold`). -/
def viewFold : List (BitVec 8) → BitVec 32 → Result (BitVec 32)
  | [], acc => .ok acc
  | x :: xs, acc =>
    match checkedAddI32 acc (x.signExtend 32) with
    | .error e => .error e
    | .ok a => viewFold xs a

/-- Value-level forward for `view_sum`: the checked-add fold from
    `0` over the reified bytes. -/
def viewSumFwd (l : List (BitVec 8)) : Result Value :=
  .i32 <$> viewFold l (BitVec.ofNat 32 0)

/-- The forward on a failed fold is the error (exact `<$>`
    rewrite, cf. `i32_map_error`). -/
theorem viewSumFwd_err (l : List (BitVec 8)) (e : Panic)
    (hfold : viewFold l (BitVec.ofNat 32 0) = .error e) :
    viewSumFwd l = .error e := by
  simp only [viewSumFwd, hfold, i32_map_error]

/-- The forward on a successful fold is the mapped word. -/
theorem viewSumFwd_ok (l : List (BitVec 8)) (acc' : BitVec 32)
    (hfold : viewFold l (BitVec.ofNat 32 0) = .ok acc') :
    viewSumFwd l = .ok (.i32 acc') := by
  simp only [viewSumFwd, hfold, i32_map_ok]

/-- Loop environments: `u64` index `k` and accumulator, view fixed. -/
def mkViewEnv (l : List (BitVec 8)) (k : Nat) (acc : BitVec 32) : Env :=
  [("i", .u64 (BitVec.ofNat 64 k)), ("t", .i32 acc), ("s", .viewVal l)]

theorem mkViewEnv_i (l : List (BitVec 8)) (k : Nat) (acc : BitVec 32) :
    envLookup (mkViewEnv l k acc) "i" =
      some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkViewEnv, envLookup]

theorem mkViewEnv_t (l : List (BitVec 8)) (k : Nat) (acc : BitVec 32) :
    envLookup (mkViewEnv l k acc) "t" = some (.i32 acc) := by
  simp [mkViewEnv, envLookup, show ("t" : String) ≠ "i" by decide]

theorem mkViewEnv_s (l : List (BitVec 8)) (k : Nat) (acc : BitVec 32) :
    envLookup (mkViewEnv l k acc) "s" = some (.viewVal l) := by
  simp [mkViewEnv, envLookup, show ("s" : String) ≠ "i" by decide,
    show ("s" : String) ≠ "t" by decide]

/-- Updating `t` stays in the env family. -/
theorem viewEnv_update_t (l : List (BitVec 8)) (k : Nat)
    (acc v : BitVec 32) :
    envUpdate (mkViewEnv l k acc) "t" (.i32 v) =
      some (mkViewEnv l k v) := by
  simp [mkViewEnv, envUpdate, show ("t" : String) ≠ "i" by decide]

/-- Updating `i` stays in the env family. -/
theorem viewEnv_update_i (l : List (BitVec 8)) (k k' : Nat)
    (acc : BitVec 32) :
    envUpdate (mkViewEnv l k acc) "i" (.u64 (BitVec.ofNat 64 k')) =
      some (mkViewEnv l k' acc) := by
  simp [mkViewEnv, envUpdate]

/-- The loop condition reads the `u64` index against the reified
    length (both sides need the `2^64` bound: the index from the
    fuel-side descent, the length from the `hl64` extent
    hypothesis — a real view is address-bounded). -/
theorem viewCond_eval (l : List (BitVec 8)) (k : Nat) (acc : BitVec 32)
    (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.viewLen "s")) (mkViewEnv l k acc) =
      .ok (.b (decide (k < l.length))) := by
  have hi := mkViewEnv_i l k acc
  have hs := mkViewEnv_s l k acc
  have hlen : (BitVec.ofNat 64 l.length).toNat = l.length :=
    ofNat64_toNat _ hl64
  simp [evalExpr, hi, hs, ofNat64_ult k _ hk64, hlen]

/-- Body with a successful add: accumulate and step (any fuel). -/
theorem viewBody_step_ok (F : Nat) (l : List (BitVec 8)) (k : Nat)
    (acc : BitVec 32) (b : BitVec 8) (a : BitVec 32)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some b)
    (hc : checkedAddI32 acc (b.signExtend 32) = .ok a) :
    evalStmtFuel F viewBody (mkViewEnv l k acc) =
      .ok (mkViewEnv l (k + 1) a, .fellThrough) := by
  have hi := mkViewEnv_i l k acc
  have ht := mkViewEnv_t l k acc
  have hs := mkViewEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : evalExpr (.add (.var "t") (.viewAt "s" (.var "i")))
        (mkViewEnv l k acc) = .ok (.i32 a) := by
    cir_step evalExpr [ht, hi, hs, htn, hget, hc]
  have hincr : evalExpr (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
        (mkViewEnv l k a) =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h1 := mkViewEnv_i l k a
    simp only [evalExpr, litVal, h1, ofNat64_add_one]
  have up1 := viewEnv_update_t l k acc a
  have up2 := viewEnv_update_i l k (k + 1) a
  cases F <;>
    simp [viewBody, evalStmtFuel, evalStmtZero, evalStmtWith,
      hadd, hincr, up1, up2]

/-- Body with an overflowing add: the `nsw` error is loud, the
    index never advances (any fuel). -/
theorem viewBody_step_err (F : Nat) (l : List (BitVec 8)) (k : Nat)
    (acc : BitVec 32) (b : BitVec 8) (e : Panic)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some b)
    (hc : checkedAddI32 acc (b.signExtend 32) = .error e) :
    evalStmtFuel F viewBody (mkViewEnv l k acc) = .error e := by
  have hi := mkViewEnv_i l k acc
  have ht := mkViewEnv_t l k acc
  have hs := mkViewEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : evalExpr (.add (.var "t") (.viewAt "s" (.var "i")))
        (mkViewEnv l k acc) = .error e := by
    cir_step evalExpr [ht, hi, hs, htn, hget, hc]
  cases F <;>
    simp [viewBody, evalStmtFuel, evalStmtZero, evalStmtWith, hadd]

/-- The fold over a dropped suffix unfolds at the live head
    (proved once by list induction, so the loop proof never
    unfolds a well-founded fixpoint). -/
theorem viewFold_drop (l : List (BitVec 8)) (k : Nat)
    (acc : BitVec 32) :
    viewFold (l.drop k) acc =
      match l[k]? with
      | none => .ok acc
      | some x =>
        match checkedAddI32 acc (x.signExtend 32) with
        | .error e => .error e
        | .ok a => viewFold (l.drop (k + 1)) a := by
  induction l generalizing k with
  | nil => simp [viewFold]
  | cons y ys ih =>
    cases k with
    | zero => simp [viewFold]
    | succ k =>
      simp only [List.drop_succ_cons]
      exact ih k

/-- Unfolding the suffix fold at a live index. -/
theorem viewFold_step (l : List (BitVec 8)) (k : Nat)
    (acc : BitVec 32) (b : BitVec 8)
    (hget : l[k]? = some b) :
    viewFold (l.drop k) acc =
      match checkedAddI32 acc (b.signExtend 32) with
      | .error e => .error e
      | .ok a => viewFold (l.drop (k + 1)) a := by
  conv => lhs; rw [viewFold_drop]
  simp [hget]

/-- Unfolding the suffix fold past the end. -/
theorem viewFold_nil (l : List (BitVec 8)) (k : Nat)
    (acc : BitVec 32)
    (hget : l[k]? = none) :
    viewFold (l.drop k) acc = .ok acc := by
  conv => lhs; rw [viewFold_drop]
  simp [hget]

/-- Loop correctness: folds the checked-add suffix, exits with
    `i = length` (fuel-generalized; the `+1` absorbs the final exit
    iteration, so the zero-fuel case is vacuous — the S3a
    `skipWhile_correct` shape). -/
theorem viewWhile_correct (l : List (BitVec 8))
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ l.length) (hl64 : l.length < 2 ^ 64)
    (hF : l.length - k + 1 ≤ F) :
    evalStmtFuel F viewWhile (mkViewEnv l k acc) =
      match viewFold (l.drop k) acc with
      | .error e => .error e
      | .ok acc' => .ok (mkViewEnv l l.length acc', .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < l.length
    · have hk64 : k < 2 ^ 64 := by omega
      have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hlt
      have hcond : evalExpr (.ult (.var "i") (.viewLen "s"))
            (mkViewEnv l k acc) = .ok (.b true) := by
        simpa [hlt] using (viewCond_eval l k acc hk64 hl64)
      have hunfold := viewFold_step l k acc l[k] hget
      cases hc : checkedAddI32 acc ((l[k]).signExtend 32) with
      | error e =>
        have hbody := viewBody_step_err F l k acc l[k] e hlt hk64 hl64
          hget hc
        have hstep : evalStmtFuel (F + 1) viewWhile (mkViewEnv l k acc)
            = .error e := by
          simp [viewWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep, hunfold, hc]
      | ok a =>
        have hbody := viewBody_step_ok F l k acc l[k] a hlt hk64 hl64
          hget hc
        have hstep : evalStmtFuel (F + 1) viewWhile (mkViewEnv l k acc)
            = evalStmtFuel F viewWhile (mkViewEnv l (k + 1) a) := by
          simp [viewWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep, hunfold, hc]
        exact ih (k + 1) a (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.viewLen "s"))
            (mkViewEnv l l.length acc) = .ok (.b false) := by
        have hfalse : (decide (l.length < l.length)) = false := by
          simp
        have hk64 : l.length < 2 ^ 64 := hl64
        have h := viewCond_eval l l.length acc hk64 hl64
        rwa [hfalse] at h
      have hnone : l[l.length]? = none :=
        List.getElem?_eq_none (Nat.le_refl _)
      have hnil : viewFold [] acc = .ok acc := rfl
      simp [viewWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil]

/-- `emit_correct` for `view_sum`, fuel-generalized (the S3a
    `evalFuncFuel_skip` shape; the fuel hypothesis is the slice's
    dynamic-length side condition, discharged by `omega` at the
    default fuel for short views). -/
theorem evalFuncFuel_viewSum (F : Nat) (l : List (BitVec 8))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    evalFuncFuel F viewSumFunc [.viewVal l] = viewSumFwd l := by
  have hbind : bindArgs viewSumFunc.args [.viewVal l] =
      some [("s", .viewVal l)] := rfl
  have hbody : viewSumFunc.body =
      .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq viewWhile
            (.return_ (.var "t")))) := rfl
  have henv : [("i", .u64 (BitVec.ofNat 64 0)),
        ("t", .i32 (BitVec.ofNat 32 0)),
        ("s", .viewVal l)]
      = mkViewEnv l 0 (BitVec.ofNat 32 0) := rfl
  cases hfold : viewFold l (BitVec.ofNat 32 0) with
  | error e =>
    have hsum0 : viewSumFwd l = .error e := viewSumFwd_err l e hfold
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            viewWhile (mkViewEnv l 0 (BitVec.ofNat 32 0)) = .error e := by
        have h := viewWhile_correct l 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, viewSumFunc, bindArgs, evalStmtFuel,
        evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopH0, hsum0]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            viewWhile (mkViewEnv l 0 (BitVec.ofNat 32 0)) = .error e := by
        have h := viewWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, viewSumFunc, bindArgs, evalStmtFuel,
        evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopS, hsum0]
  | ok acc' =>
    have hsret : envLookup (mkViewEnv l l.length acc') "t" =
        some (.i32 acc') :=
      mkViewEnv_t l l.length acc'
    have hsum : viewSumFwd l = .ok (.i32 acc') :=
      viewSumFwd_ok l acc' hfold
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            viewWhile (mkViewEnv l 0 (BitVec.ofNat 32 0)) =
            .ok (mkViewEnv l l.length acc', .fellThrough) := by
        have h := viewWhile_correct l 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, viewSumFunc, bindArgs, evalStmtFuel,
        evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopH0, hsret, hsum]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            viewWhile (mkViewEnv l 0 (BitVec.ofNat 32 0)) =
            .ok (mkViewEnv l l.length acc', .fellThrough) := by
        have h := viewWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, viewSumFunc, bindArgs, evalStmtFuel,
        evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopS, hsret, hsum]

/-- `emit_correct` for `view_sum` at the default fuel — for short
    views (the driver only feeds lengths `≤ 8`, far below
    `EVAL_FUEL = 4096`; longer views need an explicit fuel
    hypothesis, the honest dynamic-length side condition). -/
theorem emit_correct_viewSum (l : List (BitVec 8))
    (hl64 : l.length < 2 ^ 64) (hlen : l.length + 1 ≤ EVAL_FUEL) :
    evalFunc viewSumFunc [.viewVal l] = viewSumFwd l :=
  evalFuncFuel_viewSum EVAL_FUEL l hl64 hlen
