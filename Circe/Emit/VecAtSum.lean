/-
Circe.Emit.VecAtSum — N4d-iv-d `std::vector::at` checked sum: the
`vec_at_sum` index-loop entry over the N4d-iv-c `at()` read.

The corpus (`tests/cpp/vec_at_sum.cpp`: entry takes the vector by
`const&`, sums `v.at(i)` over `v.size()` with `nsw` adds) captures
the entry + `size` + `at()` + `_M_range_check` + `operator[]` defs.
The entry functionalizes to a call-free fused `while_` loop (the
`vec_read_sum` precedent): per iteration the `_M_range_check`
guard fuses to an `if_` around the inherited `stdVecBody`
(read + checked add + index advance), the throw arm fusing to
`fail`. A `callRet`-per-iteration composer was considered and
rejected: `while_` bodies delegate to the call-free evaluator
(`evalStmtFuel`), so calls cannot appear inside loop bodies —
fusion is structural, not a shortcut.

Error precedence: the loop bound `i < len` subsumes the guard, so
the `AssertFail` leg is dead-but-propagated (pinned by
`vecAtSumBody_guard_false`); the live failure is the `nsw`
overflow. The forward is therefore the inherited `stdVecFold`.
-/
import Circe.Emit.VecRead
import Circe.Emit.VecAt

/-! ## N4d-iv-d: `vec_at_sum` entry -/

/-- Mangled name of the checked-sum entry. -/
def vecAtSumName : String :=
  "_Z10vec_at_sumRKSt6vectorIiSaIiEE"

/-- The per-iteration guard: the fused `_M_range_check`
    (`i < size`, same expression as the loop condition). -/
def vecAtSumGuard : CExpr :=
  .ult (.var "i") (.stdVecLen "s")

/-- Canonical CoreIR for the entry: accumulator/index init plus the
    guarded index loop (the guard wraps the inherited `stdVecBody`;
    the throw arm is `fail`). -/
def vecAtSumBody : CStmt :=
  .if_ vecAtSumGuard stdVecBody .fail

/-- Loop: `while (i < s.size()) { checked-read, add, advance }`. -/
def vecAtSumWhile : CStmt :=
  .while_ (.ult (.var "i") (.stdVecLen "s")) vecAtSumBody

/-- Canonical CoreIR for `vec_at_sum`. -/
def vecAtSumFunc : Func :=
  ⟨vecAtSumName,
   [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow }],
   .i 32,
   .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq vecAtSumWhile
         (.return_ (.var "t"))))⟩

/-- Value-level forward for the entry: the inherited checked-add
    fold (the guard is subsumed by the loop bound, so the fold
    never sees `AssertFail`). -/
def vecAtSumFwd : List (BitVec 32) → Result Value :=
  stdVecReadSumFwd

/-- Guard evaluation (the subsumption the precedence rests on). -/
theorem vecAtSumGuard_eval (l : List (BitVec 32)) (k : Nat)
    (acc : BitVec 32) (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64) :
    evalExpr vecAtSumGuard (mkStdVecEnv l k acc) =
      .ok (.b (decide (k < l.length))) := by
  simpa [vecAtSumGuard] using stdVecCond_eval l k acc hk64 hl64

/-- Error precedence (dead-but-propagated): past the end the guard
    is false and the body aborts loudly (any fuel). -/
theorem vecAtSumBody_guard_false (F : Nat) (l : List (BitVec 32))
    (k : Nat) (acc : BitVec 32) (hl64 : l.length < 2 ^ 64)
    (hk64 : k < 2 ^ 64) (hk : l.length ≤ k) :
    evalStmtFuel F vecAtSumBody (mkStdVecEnv l k acc) =
      .error .AssertFail := by
  have hc : evalExpr vecAtSumGuard (mkStdVecEnv l k acc) =
      .ok (.b false) := by
    have h := vecAtSumGuard_eval l k acc hk64 hl64
    simpa [Nat.not_lt.mpr hk] using h
  simp only [vecAtSumBody]
  exact (evalStmtFuel_if_false _ _ _ _ _ hc).trans
    (evalStmtFuel_fail _ _)

/-- Body with a successful add: guard holds in-loop (subsumption),
    so the step is the inherited body step (any fuel). -/
theorem vecAtSumBody_step_ok (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x a : BitVec 32)
    (hlt : k < l.length) (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .ok a) :
    evalStmtFuel F vecAtSumBody (mkStdVecEnv l k acc) =
      .ok (mkStdVecEnv l (k + 1) a, .fellThrough) := by
  have hg : evalExpr vecAtSumGuard (mkStdVecEnv l k acc) =
      .ok (.b true) := by
    have h := vecAtSumGuard_eval l k acc hk64 hl64
    simpa [hlt] using h
  have hbody := stdVecBody_step_ok F l k acc x a hlt hk64 hl64 hget hc
  simp only [vecAtSumBody]
  rw [evalStmtFuel_if_true _ _ _ _ _ hg]
  exact hbody

/-- Body with an overflowing add: the `nsw` error is loud, the
    index never advances (any fuel). -/
theorem vecAtSumBody_step_err (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x : BitVec 32) (e : Panic)
    (hlt : k < l.length) (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .error e) :
    evalStmtFuel F vecAtSumBody (mkStdVecEnv l k acc) = .error e := by
  have hg : evalExpr vecAtSumGuard (mkStdVecEnv l k acc) =
      .ok (.b true) := by
    have h := vecAtSumGuard_eval l k acc hk64 hl64
    simpa [hlt] using h
  have hbody := stdVecBody_step_err F l k acc x e hlt hk64 hl64 hget hc
  simp only [vecAtSumBody]
  rw [evalStmtFuel_if_true _ _ _ _ _ hg]
  exact hbody

/-- Loop correctness: folds the checked-add suffix, exits with
    `i = length` (fuel-generalized; mirrors `stdVecWhile_correct`
    — the guard is subsumed, so the fold is the inherited one). -/
theorem vecAtSumWhile_correct (l : List (BitVec 32))
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ l.length) (hl64 : l.length < 2 ^ 64)
    (hF : l.length - k + 1 ≤ F) :
    evalStmtFuel F vecAtSumWhile (mkStdVecEnv l k acc) =
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
        have hbody := vecAtSumBody_step_err F l k acc l[k] e hlt hk64 hl64
          hget hc
        have hstep : evalStmtFuel (F + 1) vecAtSumWhile (mkStdVecEnv l k acc)
            = .error e := by
          simp [vecAtSumWhile, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hbody]
        rw [hstep, hunfold, hc]
      | ok a =>
        have hbody := vecAtSumBody_step_ok F l k acc l[k] a hlt hk64 hl64
          hget hc
        have hstep : evalStmtFuel (F + 1) vecAtSumWhile (mkStdVecEnv l k acc)
            = evalStmtFuel F vecAtSumWhile (mkStdVecEnv l (k + 1) a) := by
          simp [vecAtSumWhile, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hbody]
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
      have hnil : stdVecFold [] acc = .ok acc := rfl
      simp [vecAtSumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil]

/-- `emit_correct` for `vec_at_sum`, fuel-generalized (the S3a shape;
    the fuel hypothesis is the slice's dynamic-length side
    condition). -/
theorem evalFuncFuel_vecAtSum (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    evalFuncFuel F vecAtSumFunc [.stdVecVal l] = vecAtSumFwd l := by
  have hbind : bindArgs vecAtSumFunc.args [.stdVecVal l] =
      some [("s", .stdVecVal l)] := rfl
  have hbody : vecAtSumFunc.body =
      .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq vecAtSumWhile
            (.return_ (.var "t")))) := rfl
  have henv : [("i", .u64 (BitVec.ofNat 64 0)),
        ("t", .i32 (BitVec.ofNat 32 0)),
        ("s", .stdVecVal l)]
      = mkStdVecEnv l 0 (BitVec.ofNat 32 0) := rfl
  cases hfold : stdVecFold l (BitVec.ofNat 32 0) with
  | error e =>
    have hsum0 : vecAtSumFwd l = .error e := stdVecReadSumFwd_err l e hfold
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            vecAtSumWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0)) = .error e := by
        have h := vecAtSumWhile_correct l 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, vecAtSumFunc, bindArgs, evalStmtFuel,
        evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopH0, hsum0]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            vecAtSumWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0)) = .error e := by
        have h := vecAtSumWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, vecAtSumFunc, bindArgs, evalStmtFuel,
        evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopS, hsum0]
  | ok a =>
    have hsret : envLookup (mkStdVecEnv l l.length a) "t" =
        some (.i32 a) :=
      mkStdVecEnv_t l l.length a
    have hsum0 : vecAtSumFwd l = .ok (.i32 a) := stdVecReadSumFwd_ok l a hfold
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            vecAtSumWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0)) =
            .ok ((mkStdVecEnv l l.length a, .fellThrough)) := by
        have h := vecAtSumWhile_correct l 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, vecAtSumFunc, bindArgs, evalStmtFuel,
        evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopH0, hsum0]
      rw [hsret]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            vecAtSumWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0)) =
            .ok ((mkStdVecEnv l l.length a, .fellThrough)) := by
        have h := vecAtSumWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, vecAtSumFunc, bindArgs, evalStmtFuel,
        evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopS, hsret, hsum0]
