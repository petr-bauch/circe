/-
Circe.Emit.Span — N4d-iii `std::span<const int32_t>` index-sum: the
`_M_extent` extent leaf + the `size` entry + the `operator[]` fused
leaf + the `span_sum` index-loop entry.

The C++ call chain is depth-3 (`span_sum` → `size` → `_M_extent` →
the `_M_extent_value` load; `span_sum` → `operator[]` → live `size`
call in the dead assert arm) but `evalProgStmt` dispatches callees
via `evalFuncFuel`, which only evaluates call-free bodies (the S1
DAG discipline). So functionalization fuses edges, exactly like the
N4d-ii leaf fusions (`optDerefOpFunc` fuses two call edges into the
`optGet` read): `size` fuses the `get_member [1]` (`_M_extent`)
projection + the `_M_extent` call into the `spanLen` read;
`operator[]` fuses the `get_member [0]` (`_M_ptr`) projection + the
`ptr_stride` + both loads into the `spanAt` read. `_M_extent` still
validates separately to `spanExtentFunc` (same value story: the
`get_member [0]` (`_M_extent_value`) projection + retval load fused
into the `spanLen` read), so misshapen variants of every def reject
loudly.

The `operator[]` dead-assert scope (`cir.ternary` over a `false`
const + one-sided `cir.if` + `cir.unreachable` in a do-while-false
scope, the disabled-`_GLIBCXX_ASSERT` skeleton — cf. `span:278`,
which unlike the N4d-ii `__glibcxx_assert` is unconditional `do {
... } while (false)`) is dead code: the ternary condition is the
literal `false`, so the live `size()` call in the untaken arm never
evaluates and the `unreachable` never fires. It is dropped from
`spanIndexFunc`; the gate (`isSpanIndexShape`) pins the dead
skeleton textually — including the live `size()` call in the dead
arm — so an enabled-assert variant rejects loudly instead of being
silently modeled (stronger than the N4d-ii pin, which only had a
dead leaf call in its dead arm).

The `span_sum` entry loop (`cir.for` with per-iteration `size()`
and `operator[]` calls) fuses to a call-free `while_` leaf over
`spanLen`/`spanAt` (the S3a `skip_sum` precedent,
`Circe.Emit.Flow`: loop-env family + suffix fold + fuel side
condition). The fusion is semantics-preserving: both callees are
pure reads over the reified view (`sharedBorrow` pure-copy snapshot
semantics, the S1 `sum_array` precedent), so evaluating them once
per iteration against the unchanged view equals reading the fused
`spanLen`/`spanAt` against the same view. The gate pins the
un-fused call sites textually (`isSpanSumShape` admits exactly one
`size` site in `cond` and one `operator[]` site in `body`), and the
`nsw` err-propagation threads through the checked-add fold.
-/
import Circe.Emit.Fragment

/-! ## N4d-iii: `std::span` extent leaf, size, index, entry -/

/-- The 2-word `std::span<const int32_t>` object model: the address
    word plus the extent word (both erase in the value model, which
    reifies the viewed words as `spanVal`). -/
def spanObjTy : CType := .struct "std::span<const int>" [.u 64, .u 64]

/-- The 1-word `__extent_storage` object model: the `_M_extent_value`
    word (erases; the extent is the `spanVal` length). -/
def spanExtentObjTy : CType :=
  .struct "std::__detail::__extent_storage" [.u 64]

/-- Mangled callee names in `tests/cpp/span_sum.cpp`. -/
def spanExtentName : String :=
  "_ZNKSt8__detail16__extent_storageILm18446744073709551615EE9_M_extentEv"
def spanSizeName : String :=
  "_ZNKSt4spanIKiLm18446744073709551615EE4sizeEv"
def spanIndexName : String :=
  "_ZNKSt4spanIKiLm18446744073709551615EEixEm"
def spanSumName : String :=
  "_Z8span_sumSt4spanIKiLm18446744073709551615EE"

/-- Canonical CoreIR for `_M_extent`: the `get_member [0]`
    (`_M_extent_value`) projection + retval load fused into the
    `spanLen` read. -/
def spanExtentFunc : Func :=
  ⟨spanExtentName,
   [{ name := "e", ty := spanExtentObjTy, role := .sharedBorrow }],
   .u 64,
   .return_ (.spanLen "e")⟩

/-- Canonical CoreIR for `size`: the `get_member [1]` (`_M_extent`)
    projection + the `_M_extent` call fused into the `spanLen` read
    (cf. `optHasValueFunc`). -/
def spanSizeFunc : Func :=
  ⟨spanSizeName,
   [{ name := "s", ty := spanObjTy, role := .sharedBorrow }],
   .u 64,
   .return_ (.spanLen "s")⟩

/-- Canonical CoreIR for `operator[]`: the `get_member [0]`
    (`_M_ptr`) projection + `ptr_stride` + both loads fused into the
    `spanAt` read (the dead assert scope is dropped, cf. the module
    docstring; the caller-side load is fused downstream, cf.
    `optDerefOpFunc`). -/
def spanIndexFunc : Func :=
  ⟨spanIndexName,
   [{ name := "s", ty := spanObjTy, role := .sharedBorrow },
    { name := "n", ty := .u 64, role := .owned }],
   .i 32,
   .return_ (.spanAt "s" (.var "n"))⟩

/-- Loop body: `t = t+s[i]; i = i+1` (the `cir.for` body + step
    regions fused; the per-iteration `size()`/`operator[]` calls
    read the fused `spanLen`/`spanAt`). -/
def spanBody : CStmt :=
  .seq (.assign "t" (.add (.var "t") (.spanAt "s" (.var "i"))))
    (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- Loop: `while (i < s.size()) { ... }`. -/
def spanWhile : CStmt :=
  .while_ (.ult (.var "i") (.spanLen "s")) spanBody

/-- Canonical CoreIR for `span_sum`: the accumulator/index/element
    initialization plus the call-free index loop (the S3a `skip_sum`
    shape: `cir.for` over `u64` with an `nsw` add maps to
    `while_` + `ult` + `add` + `uadd`). -/
def spanSumFunc : Func :=
  ⟨spanSumName,
   [{ name := "s", ty := spanObjTy, role := .sharedBorrow }],
   .i 32,
   .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq spanWhile
         (.return_ (.var "t"))))⟩

/-- Value-level forward for `_M_extent`: the reified length as a
    `u64` word. -/
def spanExtentFwd (l : List (BitVec 32)) : Result Value :=
  .ok (.u64 (BitVec.ofNat 64 l.length))

/-- Value-level forward for `size`: the same read (the call edge is
    fused, so the forward is the leaf forward by definition). -/
def spanSizeFwd (l : List (BitVec 32)) : Result Value :=
  spanExtentFwd l

theorem spanSizeFwd_is_call (l : List (BitVec 32)) :
    spanSizeFwd l = spanExtentFwd l := rfl

/-- Value-level forward for `operator[]`: the word at `u64` index
    `n`, `OOB` off the end (mirrors `arrayRefFwd`). -/
def spanIndexFwd (l : List (BitVec 32)) (n : BitVec 64) : Result Value :=
  match l[n.toNat]? with
  | some x => .ok (.i32 x)
  | none => .error .OOB

/-- Checked-add fold over the suffix: the `nsw` accumulation with
    loud err-propagation (cf. `arraySumFwd`, generalized to a
    dynamic length; structural recursion over the suffix list, so
    unfolding is clean — the loop invariant bridges via
    `spanFold_drop`). -/
def spanFold : List (BitVec 32) → BitVec 32 → Result (BitVec 32)
  | [], acc => .ok acc
  | x :: xs, acc =>
    match checkedAddI32 acc x with
    | .error e => .error e
    | .ok a => spanFold xs a

/-- Value-level forward for `span_sum`: the checked-add fold from
    `0` over the reified words. -/
def spanSumFwd (l : List (BitVec 32)) : Result Value :=
  .i32 <$> spanFold l (BitVec.ofNat 32 0)

/-- The forward on a failed fold is the error (exact `<$>`
    rewrite, cf. `i32_map_error`). -/
theorem spanSumFwd_err (l : List (BitVec 32)) (e : Panic)
    (hfold : spanFold l (BitVec.ofNat 32 0) = .error e) :
    spanSumFwd l = .error e := by
  simp only [spanSumFwd, hfold, i32_map_error]

/-- The forward on a successful fold is the mapped word. -/
theorem spanSumFwd_ok (l : List (BitVec 32)) (acc' : BitVec 32)
    (hfold : spanFold l (BitVec.ofNat 32 0) = .ok acc') :
    spanSumFwd l = .ok (.i32 acc') := by
  simp only [spanSumFwd, hfold, i32_map_ok]

/-- Env fact for the `_M_extent` shape. -/
theorem envLookup_spanExtent_e (l : List (BitVec 32)) :
    envLookup [("e", .spanVal l)] "e" = some (.spanVal l) := by
  simp [envLookup]

/-- `emit_correct` for `_M_extent` (total on spans). -/
theorem evalFuncFuel_spanExtent (F : Nat) (l : List (BitVec 32)) :
    evalFuncFuel F spanExtentFunc [.spanVal l] = spanExtentFwd l := by
  have hbind : bindArgs spanExtentFunc.args [.spanVal l] =
      some [("e", .spanVal l)] := rfl
  have hbody : spanExtentFunc.body = .return_ (.spanLen "e") := rfl
  have he := envLookup_spanExtent_e l
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, spanExtentFwd, he]

/-- Env fact for the `size` shape. -/
theorem envLookup_spanSize_s (l : List (BitVec 32)) :
    envLookup [("s", .spanVal l)] "s" = some (.spanVal l) := by
  simp [envLookup]

/-- `emit_correct` for `size` (same read, fused call edge). -/
theorem evalFuncFuel_spanSize (F : Nat) (l : List (BitVec 32)) :
    evalFuncFuel F spanSizeFunc [.spanVal l] = spanSizeFwd l := by
  have hbind : bindArgs spanSizeFunc.args [.spanVal l] =
      some [("s", .spanVal l)] := rfl
  have hbody : spanSizeFunc.body = .return_ (.spanLen "s") := rfl
  have hs := envLookup_spanSize_s l
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, spanSizeFwd, spanExtentFwd, hs]

/-- Env facts for the `operator[]` shape. -/
theorem envLookup_spanIndex_s (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("s", .spanVal l), ("n", .u64 n)] "s" =
      some (.spanVal l) := by
  simp [envLookup]

theorem envLookup_spanIndex_n (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("s", .spanVal l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
  simp [envLookup, show ("n" : String) ≠ "s" by decide]

/-- `emit_correct` for `operator[]` (all inputs, hit and `OOB`). -/
theorem evalFuncFuel_spanIndex (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) :
    evalFuncFuel F spanIndexFunc [.spanVal l, .u64 n] =
      spanIndexFwd l n := by
  have hbind : bindArgs spanIndexFunc.args [.spanVal l, .u64 n] =
      some [("s", .spanVal l), ("n", .u64 n)] := rfl
  have hbody : spanIndexFunc.body =
      .return_ (.spanAt "s" (.var "n")) := rfl
  have hs := envLookup_spanIndex_s l n
  have hn := envLookup_spanIndex_n l n
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, spanIndexFwd, hs, hn] <;>
    (cases h : l[n.toNat]? <;> simp_all)

/-- Loop environments: `u64` index `k` and accumulator, view fixed. -/
def mkSpanEnv (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32) : Env :=
  [("i", .u64 (BitVec.ofNat 64 k)), ("t", .i32 acc), ("s", .spanVal l)]

theorem mkSpanEnv_i (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32) :
    envLookup (mkSpanEnv l k acc) "i" =
      some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkSpanEnv, envLookup]

theorem mkSpanEnv_t (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32) :
    envLookup (mkSpanEnv l k acc) "t" = some (.i32 acc) := by
  simp [mkSpanEnv, envLookup, show ("t" : String) ≠ "i" by decide]

theorem mkSpanEnv_s (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32) :
    envLookup (mkSpanEnv l k acc) "s" = some (.spanVal l) := by
  simp [mkSpanEnv, envLookup, show ("s" : String) ≠ "i" by decide,
    show ("s" : String) ≠ "t" by decide]

/-- Updating `t` stays in the env family. -/
theorem spanEnv_update_t (l : List (BitVec 32)) (k : Nat)
    (acc v : BitVec 32) :
    envUpdate (mkSpanEnv l k acc) "t" (.i32 v) =
      some (mkSpanEnv l k v) := by
  simp [mkSpanEnv, envUpdate, show ("t" : String) ≠ "i" by decide]

/-- Updating `i` stays in the env family. -/
theorem spanEnv_update_i (l : List (BitVec 32)) (k k' : Nat)
    (acc : BitVec 32) :
    envUpdate (mkSpanEnv l k acc) "i" (.u64 (BitVec.ofNat 64 k')) =
      some (mkSpanEnv l k' acc) := by
  simp [mkSpanEnv, envUpdate]

/-- The loop condition reads the `u64` index against the reified
    extent (both sides need the `2^64` bound: the index from the
    fuel-side descent, the extent from the `hl64` extent hypothesis
    — a real span is address-bounded, so this excludes only the
    `ofNat` wraparound case, never a real input). -/
theorem spanCond_eval (l : List (BitVec 32)) (k : Nat) (acc : BitVec 32)
    (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.spanLen "s")) (mkSpanEnv l k acc) =
      .ok (.b (decide (k < l.length))) := by
  have hi := mkSpanEnv_i l k acc
  have hs := mkSpanEnv_s l k acc
  have hlen : (BitVec.ofNat 64 l.length).toNat = l.length :=
    ofNat64_toNat _ hl64
  simp [evalExpr, hi, hs, ofNat64_ult k _ hk64, hlen]

/-- Body with a successful add: accumulate and step (any fuel). -/
theorem spanBody_step_ok (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x a : BitVec 32)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .ok a) :
    evalStmtFuel F spanBody (mkSpanEnv l k acc) =
      .ok (mkSpanEnv l (k + 1) a, .fellThrough) := by
  have hi := mkSpanEnv_i l k acc
  have ht := mkSpanEnv_t l k acc
  have hs := mkSpanEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : evalExpr (.add (.var "t") (.spanAt "s" (.var "i")))
        (mkSpanEnv l k acc) = .ok (.i32 a) := by
    cir_step evalExpr [ht, hi, hs, htn, hget, hc]
  have hincr : evalExpr (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
        (mkSpanEnv l k a) =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h1 := mkSpanEnv_i l k a
    simp only [evalExpr, litVal, h1, ofNat64_add_one]
  have up1 := spanEnv_update_t l k acc a
  have up2 := spanEnv_update_i l k (k + 1) a
  cases F <;>
    simp [spanBody, evalStmtFuel, evalStmtZero, evalStmtWith,
      hadd, hincr, up1, up2]

/-- Body with an overflowing add: the `nsw` error is loud, the
    index never advances (any fuel). -/
theorem spanBody_step_err (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x : BitVec 32) (e : Panic)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .error e) :
    evalStmtFuel F spanBody (mkSpanEnv l k acc) = .error e := by
  have hi := mkSpanEnv_i l k acc
  have ht := mkSpanEnv_t l k acc
  have hs := mkSpanEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : evalExpr (.add (.var "t") (.spanAt "s" (.var "i")))
        (mkSpanEnv l k acc) = .error e := by
    cir_step evalExpr [ht, hi, hs, htn, hget, hc]
  cases F <;>
    simp [spanBody, evalStmtFuel, evalStmtZero, evalStmtWith, hadd]

/-- The fold over a dropped suffix unfolds at the live head
    (proved once by list induction, so the loop proof never
    unfolds a well-founded fixpoint). -/
theorem spanFold_drop (l : List (BitVec 32)) (k : Nat)
    (acc : BitVec 32) :
    spanFold (l.drop k) acc =
      match l[k]? with
      | none => .ok acc
      | some x =>
        match checkedAddI32 acc x with
        | .error e => .error e
        | .ok a => spanFold (l.drop (k + 1)) a := by
  induction l generalizing k with
  | nil => simp [spanFold]
  | cons y ys ih =>
    cases k with
    | zero => simp [spanFold]
    | succ k =>
      simp only [List.drop_succ_cons]
      exact ih k

/-- Unfolding the suffix fold at a live index. -/
theorem spanFold_step (l : List (BitVec 32)) (k : Nat)
    (acc x : BitVec 32)
    (hget : l[k]? = some x) :
    spanFold (l.drop k) acc =
      match checkedAddI32 acc x with
      | .error e => .error e
      | .ok a => spanFold (l.drop (k + 1)) a := by
  conv => lhs; rw [spanFold_drop]
  simp [hget]

/-- Unfolding the suffix fold past the end. -/
theorem spanFold_nil (l : List (BitVec 32)) (k : Nat)
    (acc : BitVec 32)
    (hget : l[k]? = none) :
    spanFold (l.drop k) acc = .ok acc := by
  conv => lhs; rw [spanFold_drop]
  simp [hget]

/-- Loop correctness: folds the checked-add suffix, exits with
    `i = length` (fuel-generalized; the `+1` absorbs the final exit
    iteration, so the zero-fuel case is vacuous — the S3a
    `skipWhile_correct` shape). -/
theorem spanWhile_correct (l : List (BitVec 32))
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ l.length) (hl64 : l.length < 2 ^ 64)
    (hF : l.length - k + 1 ≤ F) :
    evalStmtFuel F spanWhile (mkSpanEnv l k acc) =
      match spanFold (l.drop k) acc with
      | .error e => .error e
      | .ok acc' => .ok (mkSpanEnv l l.length acc', .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < l.length
    · have hk64 : k < 2 ^ 64 := by omega
      have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hlt
      have hcond : evalExpr (.ult (.var "i") (.spanLen "s"))
            (mkSpanEnv l k acc) = .ok (.b true) := by
        simpa [hlt] using (spanCond_eval l k acc hk64 hl64)
      have hunfold := spanFold_step l k acc l[k] hget
      cases hc : checkedAddI32 acc l[k] with
      | error e =>
        have hbody := spanBody_step_err F l k acc l[k] e hlt hk64 hl64
          hget hc
        have hstep : evalStmtFuel (F + 1) spanWhile (mkSpanEnv l k acc)
            = .error e := by
          simp [spanWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep, hunfold, hc]
      | ok a =>
        have hbody := spanBody_step_ok F l k acc l[k] a hlt hk64 hl64
          hget hc
        have hstep : evalStmtFuel (F + 1) spanWhile (mkSpanEnv l k acc)
            = evalStmtFuel F spanWhile (mkSpanEnv l (k + 1) a) := by
          simp [spanWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep, hunfold, hc]
        exact ih (k + 1) a (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.spanLen "s"))
            (mkSpanEnv l l.length acc) = .ok (.b false) := by
        have hfalse : (decide (l.length < l.length)) = false := by
          simp
        have hk64 : l.length < 2 ^ 64 := hl64
        have h := spanCond_eval l l.length acc hk64 hl64
        rwa [hfalse] at h
      have hnone : l[l.length]? = none :=
        List.getElem?_eq_none (Nat.le_refl _)
      have hnil : spanFold [] acc = .ok acc := rfl
      simp [spanWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil]

/-- `emit_correct` for `span_sum`, fuel-generalized (the S3a
    `evalFuncFuel_skip` shape; the fuel hypothesis is the slice's
    dynamic-length side condition, discharged by `omega` at the
    default fuel for short spans). -/
theorem evalFuncFuel_spanSum (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    evalFuncFuel F spanSumFunc [.spanVal l] = spanSumFwd l := by
  have hbind : bindArgs spanSumFunc.args [.spanVal l] =
      some [("s", .spanVal l)] := rfl
  have hbody : spanSumFunc.body =
      .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq spanWhile
            (.return_ (.var "t")))) := rfl
  have henv : [("i", .u64 (BitVec.ofNat 64 0)),
        ("t", .i32 (BitVec.ofNat 32 0)),
        ("s", .spanVal l)]
      = mkSpanEnv l 0 (BitVec.ofNat 32 0) := rfl
  cases hfold : spanFold l (BitVec.ofNat 32 0) with
  | error e =>
    have hsum0 : spanSumFwd l = .error e := spanSumFwd_err l e hfold
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            spanWhile (mkSpanEnv l 0 (BitVec.ofNat 32 0)) = .error e := by
        have h := spanWhile_correct l 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, spanSumFunc, bindArgs, evalStmtFuel,
        evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopH0, hsum0]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            spanWhile (mkSpanEnv l 0 (BitVec.ofNat 32 0)) = .error e := by
        have h := spanWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, spanSumFunc, bindArgs, evalStmtFuel,
        evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopS, hsum0]
  | ok acc' =>
    have hsret : envLookup (mkSpanEnv l l.length acc') "t" =
        some (.i32 acc') :=
      mkSpanEnv_t l l.length acc'
    have hsum : spanSumFwd l = .ok (.i32 acc') :=
      spanSumFwd_ok l acc' hfold
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            spanWhile (mkSpanEnv l 0 (BitVec.ofNat 32 0)) =
            .ok (mkSpanEnv l l.length acc', .fellThrough) := by
        have h := spanWhile_correct l 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, spanSumFunc, bindArgs, evalStmtFuel,
        evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopH0, hsret, hsum]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            spanWhile (mkSpanEnv l 0 (BitVec.ofNat 32 0)) =
            .ok (mkSpanEnv l l.length acc', .fellThrough) := by
        have h := spanWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hl64
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp [evalFuncFuel, spanSumFunc, bindArgs, evalStmtFuel,
        evalStmtWith, evalExpr, litVal, envExtend,
        henv, hloopS, hsret, hsum]

/-- `emit_correct` for `span_sum` at the default fuel — for short
    spans (the driver only feeds lengths `≤ 8`, far below
    `EVAL_FUEL = 4096`; longer spans need an explicit fuel
    hypothesis, the honest dynamic-length side condition). -/
theorem emit_correct_spanSum (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hlen : l.length + 1 ≤ EVAL_FUEL) :
    evalFunc spanSumFunc [.spanVal l] = spanSumFwd l :=
  evalFuncFuel_spanSum EVAL_FUEL l hl64 hlen
