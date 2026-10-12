/-
Circe.Emit.VecAt — `at()` checked reads over `const std::vector<int>&`
(the N4d-iv read family, third member after `size` / `operator[]`).

The corpus (`tests/cpp/vec_at_one.cpp`: `return v.at(0)`) lowers to a
three-level call chain over frozen leaves: the entry calls const
`at()`, which calls `_M_range_check` (branch on `cmp ge n size`,
noreturn `__throw_out_of_range_fmt` on the taken arm) and the
admitted `operator[]`. Readers never write. Like `vec_read_sum`
(N4d-iv-b2), call-text maps to canonical call-free Funcs: the guard
fuses into each body, and the throw arm fuses to `fail` (the
`_M_check_len` precedent — under our `-fno-exceptions` builds an
out-of-range `at()` literally aborts, so loud `AssertFail` is the
honest model, never silent; it is deliberately distinct from
`operator[]`'s catchable `OOB`).
-/
import Circe.Emit.VecRead

def stdVecRangeCheckName : String :=
  "_ZNKSt6vectorIiSaIiEE14_M_range_checkEm"
def stdVecAtName : String := "_ZNKSt6vectorIiSaIiEE2atEm"
def vecAtOneName : String := "_Z10vec_at_oneRKSt6vectorIiSaIiEE"
/-- The noreturn `printf`-style throw called on the OOB arm. -/
def stdVecRangeCheckThrowName : String :=
  "_ZSt24__throw_out_of_range_fmtPKcz"

/-- `n.ult (ofNat len)` bridge (mirror of `ofNat64_ult`, which goes
    the other direction). -/
theorem ult_ofNat64_len (n : BitVec 64) (len : Nat) (h : len < 2 ^ 64) :
    n.ult (BitVec.ofNat 64 len) = decide (n.toNat < len) := by
  rw [BitVec.ult_eq_decide, ofNat64_toNat len h]

/-! ## `_M_range_check` leaf: the guard, fused -/

/-- Canonical CoreIR for `_M_range_check`: branch on `n < size`,
    echo the checked index, abort (`fail`) past the end. -/
def stdVecRangeCheckFunc : Func :=
  ⟨stdVecRangeCheckName,
   [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "n", ty := .u 64, role := .owned }],
   .u 64,
   .if_ (.ult (.var "n") (.stdVecLen "s"))
     (.return_ (.var "n"))
     .fail⟩

/-- Value-level forward for `_M_range_check`. -/
def stdVecRangeCheckFwd (l : List (BitVec 32)) (n : BitVec 64) :
    Result Value :=
  if n.toNat < l.length then .ok (.u64 n) else .error .AssertFail

theorem stdVecRangeCheckFwd_ok (l : List (BitVec 32)) (n : BitVec 64)
    (h : n.toNat < l.length) :
    stdVecRangeCheckFwd l n = .ok (.u64 n) := by
  simp [stdVecRangeCheckFwd, h]

theorem stdVecRangeCheckFwd_fail (l : List (BitVec 32)) (n : BitVec 64)
    (h : ¬ n.toNat < l.length) :
    stdVecRangeCheckFwd l n = .error .AssertFail := by
  simp [stdVecRangeCheckFwd, h]

/-- The guard reads the index against the reified length. -/
theorem stdVecRangeCheckCond_eval (l : List (BitVec 32)) (n : BitVec 64)
    (hlen64 : l.length < 2 ^ 64) :
    evalExpr (.ult (.var "n") (.stdVecLen "s"))
      [("s", .stdVecVal l), ("n", .u64 n)] =
      .ok (.b (decide (n.toNat < l.length))) := by
  have hn := envLookup_stdVecIndex_n l n
  have hs := envLookup_stdVecIndex_s l n
  have hsize : evalExpr (.stdVecLen "s")
      [("s", .stdVecVal l), ("n", .u64 n)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some "s" _ l hs
  have hnv : evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hsize
  rw [ult_ofNat64_len n l.length hlen64] at hult
  exact hult

/-- `emit_correct` for `_M_range_check` (all inputs, hit and abort;
    loop-free, any fuel). -/
theorem evalFuncFuel_stdVecRangeCheck (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (hlen64 : l.length < 2 ^ 64) :
    evalFuncFuel F stdVecRangeCheckFunc [.stdVecVal l, .u64 n] =
      stdVecRangeCheckFwd l n := by
  have hbind : bindArgs stdVecRangeCheckFunc.args [.stdVecVal l, .u64 n] =
      some [("s", .stdVecVal l), ("n", .u64 n)] := rfl
  have hbody : stdVecRangeCheckFunc.body =
      .if_ (.ult (.var "n") (.stdVecLen "s"))
        (.return_ (.var "n"))
        .fail := rfl
  have hn := envLookup_stdVecIndex_n l n
  have hnv : evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  by_cases h : n.toNat < l.length
  · have hc : evalExpr (.ult (.var "n") (.stdVecLen "s"))
        [("s", .stdVecVal l), ("n", .u64 n)] = .ok (.b true) := by
      simpa [h] using stdVecRangeCheckCond_eval l n hlen64
    have hfwd : stdVecRangeCheckFwd l n = .ok (.u64 n) :=
      stdVecRangeCheckFwd_ok l n h
    have hstmt : evalStmtFuel F stdVecRangeCheckFunc.body
        [("s", .stdVecVal l), ("n", .u64 n)] =
        .ok ([("s", .stdVecVal l), ("n", .u64 n)], .returned (.u64 n)) := by
      rw [hbody]
      exact (evalStmtFuel_if_true _ _ _ _ _ hc).trans
        (evalStmtFuel_return F _ _ _ hnv)
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  · have hc : evalExpr (.ult (.var "n") (.stdVecLen "s"))
        [("s", .stdVecVal l), ("n", .u64 n)] = .ok (.b false) := by
      simpa [h] using stdVecRangeCheckCond_eval l n hlen64
    have hfwd : stdVecRangeCheckFwd l n = .error .AssertFail :=
      stdVecRangeCheckFwd_fail l n h
    have hstmt : evalStmtFuel F stdVecRangeCheckFunc.body
        [("s", .stdVecVal l), ("n", .u64 n)] = .error .AssertFail := by
      rw [hbody]
      exact (evalStmtFuel_if_false _ _ _ _ _ hc).trans
        (evalStmtFuel_fail _ _)
    simp [evalFuncFuel, hbind, hstmt, hfwd]

/-- Abort corollary at any fuel (for the transfer side). -/
theorem evalFuncFuel_stdVecRangeCheck_fail (F : Nat)
    (l : List (BitVec 32)) (n : BitVec 64)
    (hlen64 : l.length < 2 ^ 64) (hlt : ¬ n.toNat < l.length) :
    evalFuncFuel F stdVecRangeCheckFunc [.stdVecVal l, .u64 n] =
      .error .AssertFail := by
  rw [evalFuncFuel_stdVecRangeCheck F l n hlen64,
    stdVecRangeCheckFwd_fail l n hlt]

/-! ## `at()` const method: the guarded read, fused -/

/-- Canonical CoreIR for const `at()`: the range guard fused with
    the `operator[]` read (call-text calls both; the body is the
    canonical claim, per the `vec_read_sum` precedent). -/
def stdVecAtFunc : Func :=
  ⟨stdVecAtName,
   [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "n", ty := .u 64, role := .owned }],
   .i 32,
   .if_ (.ult (.var "n") (.stdVecLen "s"))
     (.return_ (.stdVecAt "s" (.var "n")))
     .fail⟩

/-- Value-level forward for `at()`: the `operator[]` forward
    in-range, loud abort past the end (deliberately distinct from
    `operator[]`'s catchable `OOB` — the throw aborts). -/
def stdVecAtFwd (l : List (BitVec 32)) (n : BitVec 64) : Result Value :=
  if n.toNat < l.length then stdVecIndexFwd l n else .error .AssertFail

theorem stdVecAtFwd_ok (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) (hle : n.toNat < l.length)
    (hget : l[n.toNat]? = some x) :
    stdVecAtFwd l n = .ok (.i32 x) := by
  simp only [stdVecAtFwd, hle, ↓reduceIte, stdVecIndexFwd, hget]

theorem stdVecAtFwd_fail (l : List (BitVec 32)) (n : BitVec 64)
    (h : ¬ n.toNat < l.length) :
    stdVecAtFwd l n = .error .AssertFail := by
  simp [stdVecAtFwd, h]

/-- `emit_correct` for `at()` (all inputs; loop-free, any fuel). -/
theorem evalFuncFuel_stdVecAt (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (hlen64 : l.length < 2 ^ 64) :
    evalFuncFuel F stdVecAtFunc [.stdVecVal l, .u64 n] =
      stdVecAtFwd l n := by
  have hbind : bindArgs stdVecAtFunc.args [.stdVecVal l, .u64 n] =
      some [("s", .stdVecVal l), ("n", .u64 n)] := rfl
  have hbody : stdVecAtFunc.body =
      .if_ (.ult (.var "n") (.stdVecLen "s"))
        (.return_ (.stdVecAt "s" (.var "n")))
        .fail := rfl
  have hn := envLookup_stdVecIndex_n l n
  have hs := envLookup_stdVecIndex_s l n
  have hnv : evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  by_cases h : n.toNat < l.length
  · have hne : l[n.toNat]? ≠ none := by
      rw [ne_eq, List.getElem?_eq_none_iff]
      omega
    obtain ⟨x, hget'⟩ := Option.ne_none_iff_exists.mp hne
    have hget : l[n.toNat]? = some x := by simpa using hget'.symm
    have hc : evalExpr (.ult (.var "n") (.stdVecLen "s"))
        [("s", .stdVecVal l), ("n", .u64 n)] = .ok (.b true) := by
      simpa [h] using stdVecRangeCheckCond_eval l n hlen64
    have hfwd : stdVecAtFwd l n = .ok (.i32 x) :=
      stdVecAtFwd_ok l n x h hget
    have hread : evalExpr (.stdVecAt "s" (.var "n"))
        [("s", .stdVecVal l), ("n", .u64 n)] = .ok (.i32 x) :=
      evalExpr_stdVecAt_some "s" _ _ _ _ _ hs hnv hget
    have hstmt : evalStmtFuel F stdVecAtFunc.body
        [("s", .stdVecVal l), ("n", .u64 n)] =
        .ok ([("s", .stdVecVal l), ("n", .u64 n)], .returned (.i32 x)) := by
      rw [hbody]
      exact (evalStmtFuel_if_true _ _ _ _ _ hc).trans
        (evalStmtFuel_return F _ _ _ hread)
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  · have hc : evalExpr (.ult (.var "n") (.stdVecLen "s"))
        [("s", .stdVecVal l), ("n", .u64 n)] = .ok (.b false) := by
      simpa [h] using stdVecRangeCheckCond_eval l n hlen64
    have hfwd : stdVecAtFwd l n = .error .AssertFail :=
      stdVecAtFwd_fail l n h
    have hstmt : evalStmtFuel F stdVecAtFunc.body
        [("s", .stdVecVal l), ("n", .u64 n)] = .error .AssertFail := by
      rw [hbody]
      exact (evalStmtFuel_if_false _ _ _ _ _ hc).trans
        (evalStmtFuel_fail _ _)
    simp [evalFuncFuel, hbind, hstmt, hfwd]

/-! ## Entry: `vec_at_one` (const index, fused) -/

/-- Canonical CoreIR for the entry: the guard + read at literal `0`
    (call-text calls `at()` once; the caller-side load fuses
    downstream, per N4d-iv-a). -/
def vecAtOneFunc : Func :=
  ⟨vecAtOneName,
   [{ name := "v", ty := stdVecObjTy, role := .sharedBorrow }],
   .i 32,
   .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
     (.return_ (.stdVecAt "v" (.lit (.u64 (BitVec.ofNat 64 0)))))
     .fail⟩

/-- Value-level forward for the entry. -/
def vecAtOneFwd (l : List (BitVec 32)) : Result Value :=
  match l[0]? with
  | some x => .ok (.i32 x)
  | none => .error .AssertFail

/-- The entry guard at literal `0`. -/
theorem vecAtOneCond_eval (l : List (BitVec 32)) (hlen64 : l.length < 2 ^ 64) :
    evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
      [("v", .stdVecVal l)] =
      .ok (.b (decide (0 < l.length))) := by
  have hv : envLookup [("v", .stdVecVal l)] "v" = some (.stdVecVal l) := by
    simp [envLookup]
  have hsize : evalExpr (.stdVecLen "v") [("v", .stdVecVal l)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some "v" _ l hv
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal l)] = .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hult := evalExpr_ult_u64 _ _ _ _ _ hlit hsize
  have hbridge : (BitVec.ofNat 64 0).ult (BitVec.ofNat 64 l.length) =
      decide (0 < l.length) := by
    rw [BitVec.ult_eq_decide]
    simp [ofNat64_toNat _ hlen64]
  rw [hbridge] at hult
  exact hult

/-- `emit_correct` for the entry (all inputs; loop-free, any fuel). -/
theorem evalFuncFuel_vecAtOne (F : Nat) (l : List (BitVec 32))
    (hlen64 : l.length < 2 ^ 64) :
    evalFuncFuel F vecAtOneFunc [.stdVecVal l] = vecAtOneFwd l := by
  have hbind : bindArgs vecAtOneFunc.args [.stdVecVal l] =
      some [("v", .stdVecVal l)] := rfl
  have hbody : vecAtOneFunc.body =
      .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
        (.return_ (.stdVecAt "v" (.lit (.u64 (BitVec.ofNat 64 0)))))
        .fail := rfl
  have hv : envLookup [("v", .stdVecVal l)] "v" = some (.stdVecVal l) := by
    simp [envLookup]
  have hzero : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by omega)
  by_cases h : 0 < l.length
  · have hne : l[(0 : Nat)]? ≠ none := by
      rw [ne_eq, List.getElem?_eq_none_iff]
      omega
    obtain ⟨x, hget'⟩ := Option.ne_none_iff_exists.mp hne
    have hget : l[0]? = some x := by simpa using hget'.symm
    have hc : evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
        [("v", .stdVecVal l)] = .ok (.b true) := by
      simpa [h] using vecAtOneCond_eval l hlen64
    have hfwd : vecAtOneFwd l = .ok (.i32 x) := by
      simp [vecAtOneFwd, hget]
    have hget' : l[(BitVec.ofNat 64 0).toNat]? = some x := by
      rw [hzero]; exact hget
    have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("v", .stdVecVal l)] = .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hread : evalExpr (.stdVecAt "v" (.lit (.u64 (BitVec.ofNat 64 0))))
        [("v", .stdVecVal l)] = .ok (.i32 x) :=
      evalExpr_stdVecAt_some "v" _ _ _ _ _ hv hlit hget'
    have hstmt : evalStmtFuel F vecAtOneFunc.body [("v", .stdVecVal l)] =
        .ok ([("v", .stdVecVal l)], .returned (.i32 x)) := by
      rw [hbody]
      exact (evalStmtFuel_if_true _ _ _ _ _ hc).trans
        (evalStmtFuel_return F _ _ _ hread)
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  · have hc : evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
        [("v", .stdVecVal l)] = .ok (.b false) := by
      simpa [h] using vecAtOneCond_eval l hlen64
    have hfwd : vecAtOneFwd l = .error .AssertFail := by
      have hempty : l[0]? = none := by
        rw [List.getElem?_eq_none]
        simpa using h
      simp [vecAtOneFwd, hempty]
    have hstmt : evalStmtFuel F vecAtOneFunc.body [("v", .stdVecVal l)] =
        .error .AssertFail := by
      rw [hbody]
      exact (evalStmtFuel_if_false _ _ _ _ _ hc).trans
        (evalStmtFuel_fail _ _)
    simp [evalFuncFuel, hbind, hstmt, hfwd]
