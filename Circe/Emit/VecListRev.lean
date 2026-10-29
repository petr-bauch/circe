/-
Circe.Emit.VecListRev — J-slice index-linked in-place reversal:
the `list_rev` entry.

The corpus (`tests/cpp/list_rev.cpp`: mut `data` + mut `nxt`
vectors, `u64` head index and node count / end sentinel `n`,
`u64` new head out) captures the entry + the two mut-`at()`
composers + `_M_range_check` + the `size` leaf behind the
guards. The entry functionalizes to a fused seed (all loop
variables initialized: `prev = n`, `cur = head`, `nxt_cur = 0`,
the G5a init-all-loop-vars convention) plus the single
`while_` chase (`cur != n`) whose body reads `nxt[cur]`
(widened into `nxt_cur`), rewires `nxt[cur]` to the predecessor
(narrowed `(int)prev`), and advances. Both vector ops sit
behind their own fused `ult` guard (the single `cir.cmp` is
the drain condition; the loop itself carries no literals and
no branches — the bound checks live in the `at()` callees);
each miss is the `at()`-throw `AssertFail`, including widening
reads that land out of range. The cursor advances are pure
wrapping `u64` (no `usub` — the chase only moves forward
through the links); the dequeue-read widens through
`u64ofI32` (C integer promotion), the rewire store narrows a
genuine `u64` through `i32ofU64` (the G4 cast precedent — no
roundtrip needed).

Termination is by fuel lockstep, not by measure: the forward
threads the same fuel as the evaluator (`while_` is the only
consumer, one per iteration; zero fuel exits cleanly on a
false condition and aborts loudly on a live one — the S3a fuel
contract). Cyclic input simply exhausts fuel (no visited set
is needed — the chase is purely structural on fuel), and
agreement with native is pinned by spec edges plus the Diff
fuzz.
-/
import Circe.Emit.VecStackPush

/-! ## J: `list_rev` entry -/

/-- Mangled name of the reversal entry. -/
def revName : String :=
  "_Z8list_revRSt6vectorIiSaIiEES2_mm"

/-- The fused entry seed: all loop variables initialized. -/
def revSeed : CStmt :=
  .seq (.let_ "prev" (.u 64) (.var "n"))
  (.seq (.let_ "cur" (.u 64) (.var "head"))
  (.let_ "nxt_cur" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0)))))

/-- One chase iteration: guarded widening link read, guarded
    rewire store at the same index, predecessor advance, chase
    advance. -/
def revBody : CStmt :=
  .seq (.if_ (.ult (.var "cur") (.stdVecLen "nxt"))
          (.assign "nxt_cur" (.u64ofI32 (.stdVecAt "nxt" (.var "cur"))))
          .fail)
  (.seq (.if_ (.ult (.var "cur") (.stdVecLen "nxt"))
          (.vecSet "nxt" (.var "cur") (.i32ofU64 (.var "prev")))
          .fail)
  (.seq (.assign "prev" (.var "cur"))
    (.assign "cur" (.var "nxt_cur"))))

/-- The chase: `cur != n`. -/
def revOuter : CStmt :=
  .while_ (.une (.var "cur") (.var "n")) revBody

/-- Canonical CoreIR for `list_rev`: the seed, the chase, and the
    new-head return. -/
def listRevFunc : Func :=
  ⟨revName,
   [{ name := "data", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "nxt", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "head", ty := .u 64, role := .owned },
    { name := "n", ty := .u 64, role := .owned }],
   .u 64,
   (.seq revSeed (.seq revOuter (.return_ (.var "prev"))))⟩

/-- Chase environment: two word lists, dimension, entry, and the
    three cursor words. -/
def mkRevEnv (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64) : Env :=
  [("nxt_cur", .u64 nxtc), ("cur", .u64 cur), ("prev", .u64 prev),
   ("data", .stdVecVal dataL), ("nxt", .stdVecVal nxtL),
   ("head", .u64 head), ("n", .u64 n)]

theorem mkRevEnv_nxt_cur (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64) :
    envLookup (mkRevEnv dataL nxtL n head prev cur nxtc) "nxt_cur" =
      some (.u64 nxtc) := by
  simp [mkRevEnv, envLookup]

theorem mkRevEnv_cur (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64) :
    envLookup (mkRevEnv dataL nxtL n head prev cur nxtc) "cur" =
      some (.u64 cur) := by
  simp [mkRevEnv, envLookup]

theorem mkRevEnv_prev (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64) :
    envLookup (mkRevEnv dataL nxtL n head prev cur nxtc) "prev" =
      some (.u64 prev) := by
  simp [mkRevEnv, envLookup,
    show ("nxt_cur" : String) ≠ "prev" by decide,
    show ("cur" : String) ≠ "prev" by decide]

theorem mkRevEnv_data (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64) :
    envLookup (mkRevEnv dataL nxtL n head prev cur nxtc) "data" =
      some (.stdVecVal dataL) := by
  simp [mkRevEnv, envLookup,
    show ("nxt_cur" : String) ≠ "data" by decide,
    show ("cur" : String) ≠ "data" by decide,
    show ("prev" : String) ≠ "data" by decide]

theorem mkRevEnv_nxt (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64) :
    envLookup (mkRevEnv dataL nxtL n head prev cur nxtc) "nxt" =
      some (.stdVecVal nxtL) := by
  simp [mkRevEnv, envLookup,
    show ("nxt_cur" : String) ≠ "nxt" by decide,
    show ("cur" : String) ≠ "nxt" by decide,
    show ("prev" : String) ≠ "nxt" by decide,
    show ("data" : String) ≠ "nxt" by decide]

theorem mkRevEnv_head (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64) :
    envLookup (mkRevEnv dataL nxtL n head prev cur nxtc) "head" =
      some (.u64 head) := by
  simp [mkRevEnv, envLookup,
    show ("nxt_cur" : String) ≠ "head" by decide,
    show ("cur" : String) ≠ "head" by decide,
    show ("prev" : String) ≠ "head" by decide,
    show ("data" : String) ≠ "head" by decide,
    show ("nxt" : String) ≠ "head" by decide]

theorem mkRevEnv_n (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64) :
    envLookup (mkRevEnv dataL nxtL n head prev cur nxtc) "n" =
      some (.u64 n) := by
  simp [mkRevEnv, envLookup,
    show ("nxt_cur" : String) ≠ "n" by decide,
    show ("cur" : String) ≠ "n" by decide,
    show ("prev" : String) ≠ "n" by decide,
    show ("data" : String) ≠ "n" by decide,
    show ("nxt" : String) ≠ "n" by decide,
    show ("head" : String) ≠ "n" by decide]

/-- Fuel-threaded chase forward: mirrors `revOuter` iteration for
    iteration (same fuel, same guard order). The read and the
    store share one list read (same index, unmutated list), so a
    single match covers both guard sites. Zero fuel exits cleanly
    on a spent bound and aborts loudly on a live one — the S3a
    fuel contract. -/
def revOuterFwd (F : Nat) (nxtL : List (BitVec 32))
    (n prev cur : BitVec 64) :
    Result (List (BitVec 32) × BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if cur != n then .error .AssertFail
    else .ok (nxtL, prev, cur)
  | F + 1 =>
    if cur != n then
      match nxtL[cur.toNat]? with
      | none => .error .AssertFail
      | some w =>
        revOuterFwd F (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
          n cur (w.signExtend 64)
    else .ok (nxtL, prev, cur)

/-- Entry mirror: seed the sentinels, then the chase; the
    predecessor is the return. -/
def revFwd (F : Nat) (dataL nxtL : List (BitVec 32))
    (head n : BitVec 64) : Result Value :=
  match revOuterFwd F nxtL n n head with
  | .error e => .error e
  | .ok (_, prev, _) => .ok (.u64 prev)

/-- One chase iteration with the guard holding: widening link
    read, rewire store at the same index, predecessor advance,
    chase advance (any fuel). -/
theorem revBody_ok (F : Nat) (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64)
    (w : BitVec 32) (hget : nxtL[cur.toNat]? = some w)
    (hg : (cur.ult (BitVec.ofNat 64 nxtL.length)) = true) :
    evalStmtFuel F revBody
      (mkRevEnv dataL nxtL n head prev cur nxtc) =
      .ok (mkRevEnv dataL (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
        n head cur (w.signExtend 64) (w.signExtend 64), .fellThrough) := by
  have hbody : revBody =
      .seq (.if_ (.ult (.var "cur") (.stdVecLen "nxt"))
              (.assign "nxt_cur"
                (.u64ofI32 (.stdVecAt "nxt" (.var "cur"))))
              .fail)
      (.seq (.if_ (.ult (.var "cur") (.stdVecLen "nxt"))
              (.vecSet "nxt" (.var "cur") (.i32ofU64 (.var "prev")))
              .fail)
      (.seq (.assign "prev" (.var "cur"))
        (.assign "cur" (.var "nxt_cur")))) := rfl
  have hcur : evalExpr (.var "cur")
      (mkRevEnv dataL nxtL n head prev cur nxtc) =
      .ok (.u64 cur) :=
    evalExpr_var_hit _ _ _
      (mkRevEnv_cur dataL nxtL n head prev cur nxtc)
  have hlen : evalExpr (.stdVecLen "nxt")
      (mkRevEnv dataL nxtL n head prev cur nxtc) =
      .ok (.u64 (BitVec.ofNat 64 nxtL.length)) :=
    evalExpr_stdVecLen_some "nxt" _ nxtL
      (mkRevEnv_nxt dataL nxtL n head prev cur nxtc)
  have hguard : evalExpr (.ult (.var "cur") (.stdVecLen "nxt"))
      (mkRevEnv dataL nxtL n head prev cur nxtc) =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ hcur hlen
    rw [hg] at h
    exact h
  have hnxt := mkRevEnv_nxt dataL nxtL n head prev cur nxtc
  have hread : evalExpr (.stdVecAt "nxt" (.var "cur"))
      (mkRevEnv dataL nxtL n head prev cur nxtc) =
      .ok (.i32 w) :=
    evalExpr_stdVecAt_some "nxt" _ _ _ _ _ hnxt hcur hget
  have hwide := evalExpr_u64ofI32_ok _ _ _ hread
  have huv : envUpdate
      (mkRevEnv dataL nxtL n head prev cur nxtc) "nxt_cur"
      (.u64 (w.signExtend 64)) =
      some (mkRevEnv dataL nxtL n head prev cur (w.signExtend 64)) := by
    simp [mkRevEnv, envUpdate]
  have hassignC := evalStmtFuel_assign F "nxt_cur"
    (.u64ofI32 (.stdVecAt "nxt" (.var "cur")))
    (mkRevEnv dataL nxtL n head prev cur nxtc) _ _ hwide huv
  have hcur2 : evalExpr (.var "cur")
      (mkRevEnv dataL nxtL n head prev cur (w.signExtend 64)) =
      .ok (.u64 cur) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkRevEnv,
        show ("nxt_cur" : String) ≠ "cur" by decide])
  have hlen2 : evalExpr (.stdVecLen "nxt")
      (mkRevEnv dataL nxtL n head prev cur (w.signExtend 64)) =
      .ok (.u64 (BitVec.ofNat 64 nxtL.length)) :=
    evalExpr_stdVecLen_some "nxt" _ nxtL
      (mkRevEnv_nxt dataL nxtL n head prev cur (w.signExtend 64))
  have hguard2 : evalExpr (.ult (.var "cur") (.stdVecLen "nxt"))
      (mkRevEnv dataL nxtL n head prev cur (w.signExtend 64)) =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ hcur2 hlen2
    rw [hg] at h
    exact h
  have hprev : evalExpr (.var "prev")
      (mkRevEnv dataL nxtL n head prev cur (w.signExtend 64)) =
      .ok (.u64 prev) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkRevEnv,
        show ("nxt_cur" : String) ≠ "prev" by decide,
        show ("cur" : String) ≠ "prev" by decide])
  have hvalS : evalExpr (.i32ofU64 (.var "prev"))
      (mkRevEnv dataL nxtL n head prev cur (w.signExtend 64)) =
      .ok (.i32 (BitVec.ofNat 32 prev.toNat)) :=
    evalExpr_i32ofU64_ok _ _ _ hprev
  have hnxt2 := mkRevEnv_nxt dataL nxtL n head prev cur (w.signExtend 64)
  have huS : envUpdate
      (mkRevEnv dataL nxtL n head prev cur (w.signExtend 64)) "nxt"
      (.stdVecVal (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))) =
      some (mkRevEnv dataL
        (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
        n head prev cur (w.signExtend 64)) := by
    simp [mkRevEnv, envUpdate,
      show ("nxt_cur" : String) ≠ "nxt" by decide,
      show ("cur" : String) ≠ "nxt" by decide,
      show ("prev" : String) ≠ "nxt" by decide,
      show ("data" : String) ≠ "nxt" by decide]
  have hsetS := evalStmtFuel_vecSet F "nxt" (.var "cur")
    (.i32ofU64 (.var "prev"))
    (mkRevEnv dataL nxtL n head prev cur (w.signExtend 64))
    cur (BitVec.ofNat 32 prev.toNat) nxtL w _ hcur2 hvalS hnxt2 hget huS
  have hcurP : evalExpr (.var "cur")
      (mkRevEnv dataL
        (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
        n head prev cur (w.signExtend 64)) =
      .ok (.u64 cur) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkRevEnv,
        show ("nxt_cur" : String) ≠ "cur" by decide])
  have huP : envUpdate
      (mkRevEnv dataL
        (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
        n head prev cur (w.signExtend 64)) "prev" (.u64 cur) =
      some (mkRevEnv dataL
        (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
        n head cur cur (w.signExtend 64)) := by
    simp [mkRevEnv, envUpdate,
      show ("nxt_cur" : String) ≠ "prev" by decide,
      show ("cur" : String) ≠ "prev" by decide]
  have hassignP := evalStmtFuel_assign F "prev" (.var "cur")
    (mkRevEnv dataL
      (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
      n head prev cur (w.signExtend 64)) _ _ hcurP huP
  have hcur3 : evalExpr (.var "nxt_cur")
      (mkRevEnv dataL
        (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
        n head cur cur (w.signExtend 64)) =
      .ok (.u64 (w.signExtend 64)) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkRevEnv])
  have huC : envUpdate
      (mkRevEnv dataL
        (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
        n head cur cur (w.signExtend 64)) "cur"
      (.u64 (w.signExtend 64)) =
      some (mkRevEnv dataL
        (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
        n head cur (w.signExtend 64) (w.signExtend 64)) := by
    simp [mkRevEnv, envUpdate,
      show ("nxt_cur" : String) ≠ "cur" by decide]
  have hassignC2 := evalStmtFuel_assign F "cur" (.var "nxt_cur")
    (mkRevEnv dataL
      (nxtL.set cur.toNat (BitVec.ofNat 32 prev.toNat))
      n head cur cur (w.signExtend 64)) _ _ hcur3 huC
  have hifR := (evalStmtFuel_if_true F _
    (.assign "nxt_cur" (.u64ofI32 (.stdVecAt "nxt" (.var "cur")))) .fail _
    hguard).trans hassignC
  have hifS := (evalStmtFuel_if_true F _
    (.vecSet "nxt" (.var "cur") (.i32ofU64 (.var "prev"))) .fail _
    hguard2).trans hsetS
  have htail := (evalStmtFuel_seq_fallthrough F _ _ _ _ hassignP).trans
    hassignC2
  have hmid := (evalStmtFuel_seq_fallthrough F _ _ _ _ hifS).trans htail
  rw [hbody]
  exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hifR).trans hmid

/-- One chase iteration with a dead link slot aborts loudly. -/
theorem revBody_missR (F : Nat) (dataL nxtL : List (BitVec 32))
    (n head prev cur nxtc : BitVec 64)
    (hg : ((cur.ult (BitVec.ofNat 64 nxtL.length))) = false) :
    evalStmtFuel F revBody
      (mkRevEnv dataL nxtL n head prev cur nxtc) =
      .error .AssertFail := by
  have hbody : revBody =
      .seq (.if_ (.ult (.var "cur") (.stdVecLen "nxt"))
              (.assign "nxt_cur"
                (.u64ofI32 (.stdVecAt "nxt" (.var "cur"))))
              .fail)
      (.seq (.if_ (.ult (.var "cur") (.stdVecLen "nxt"))
              (.vecSet "nxt" (.var "cur") (.i32ofU64 (.var "prev")))
              .fail)
      (.seq (.assign "prev" (.var "cur"))
        (.assign "cur" (.var "nxt_cur")))) := rfl
  have hcur : evalExpr (.var "cur")
      (mkRevEnv dataL nxtL n head prev cur nxtc) =
      .ok (.u64 cur) :=
    evalExpr_var_hit _ _ _
      (mkRevEnv_cur dataL nxtL n head prev cur nxtc)
  have hlen : evalExpr (.stdVecLen "nxt")
      (mkRevEnv dataL nxtL n head prev cur nxtc) =
      .ok (.u64 (BitVec.ofNat 64 nxtL.length)) :=
    evalExpr_stdVecLen_some "nxt" _ nxtL
      (mkRevEnv_nxt dataL nxtL n head prev cur nxtc)
  have hguard : evalExpr (.ult (.var "cur") (.stdVecLen "nxt"))
      (mkRevEnv dataL nxtL n head prev cur nxtc) =
      .ok (.b false) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ hcur hlen
    rw [hg] at h
    exact h
  have hif := (evalStmtFuel_if_false F _
    (.assign "nxt_cur" (.u64ofI32 (.stdVecAt "nxt" (.var "cur")))) .fail _
    hguard).trans (evalStmtFuel_fail F _)
  rw [hbody]
  exact evalStmtFuel_seq_err F _ _ _ _ hif
