/-
Circe.Emit.VecCompose.InsertRouter — N7c `_M_insert_rval` router +
`insert` forwarder + the closed `vec_insert_sum` entry (split out of
`Circe.Emit.VecCompose.Insert`, N8b file-size split).

The router is a 2-arm composer over erased `u64` positions:
- space (`len < cap`): at-end (`pos == len`) constructs at `len`,
  else `_M_insert_aux` (construct-last, bump, shift, assign);
- full (`len == cap`): `_M_realloc_insert` at `pos` (the corpus
  passes `begin() + n`, never `end()`; admitted N4d).
-/
import Circe.Emit.Fragment
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose.Base
import Circe.Emit.VecCompose.Realloc
import Circe.Emit.VecCompose.Entry
import Circe.Emit.VecCompose.Reserve
import Circe.Emit.VecCompose.Insert

/-! ## N7c-ii-a: `_M_insert_rval` router + `insert` forwarder -/

/-- `ueq` on two `u64`-valued expressions (the `_M_insert_rval`
    `pos == len` shape; cf. `evalExpr_ult_u64`). -/
theorem evalExpr_ueq_u64_vars (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 64)
    (h₁ : evalExpr e₁ ρ = .ok (.u64 x))
    (h₂ : evalExpr e₂ ρ = .ok (.u64 y)) :
    evalExpr (.ueq e₁ e₂) ρ = .ok (.b (x == y)) := by
  simp [evalExpr, h₁, h₂]

/-- `findFunc` resolves the realloc callee in the grown program. -/
theorem findFunc_stdVecGrowRealloc :
    findFunc vecGrowProg stdVecGrowReallocName =
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

/-- `findFunc` resolves the aux callee in the grown program. -/
theorem findFunc_stdVecInsertAux :
    findFunc vecGrowProg stdVecInsertAuxName =
      some stdVecInsertAuxFunc := by
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
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the rval router in the grown program. -/
theorem findFunc_stdVecInsertRval :
    findFunc vecGrowProg stdVecInsertRvalName =
      some stdVecInsertRvalFunc := by
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
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the insert forwarder in the grown program. -/
theorem findFunc_stdVecInsert :
    findFunc vecGrowProg stdVecInsertName =
      some stdVecInsertFunc := by
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
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the construct leaf in the grown program. -/
theorem findFunc_stdVecConstruct :
    findFunc vecGrowProg stdVecTraitsConstructName =
      some stdVecConstructFunc := by
  unfold vecGrowProg
  rw [findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- Value-level forward for `_M_insert_rval`: with room, construct at
    `end()` when `pos == len`, else the aux composer; full routes to
    the realloc composer at `end()` (cf. `stdVecEmplaceBackFwd`: the
    `Nat`-level dispatch mirrors the shell's word-level guards). -/
def stdVecInsertRvalFwd (b : Vec32) (len cap : Nat) (pos : BitVec 64)
    (x : BitVec 32) : Result Value :=
  if len < cap then
    if pos == BitVec.ofNat 64 len then
      (stdVecConstructFwd b len cap pos x).bind fun cv =>
      (vecGrowOwned cv).bind fun (bC, _, _) =>
      .ok (.stdVecOwned bC (len + 1) cap)
    else stdVecInsertAuxFwd b len cap pos x
  else stdVecGrowReallocFwd b len cap pos x

/-- `emit_correct` for `_M_insert_rval`: the program over the frozen
    leaves plus the proved aux / realloc composers agrees with the
    router forward. Caller-side preconditions: the triple is live with
    room for one more word in the room arms, the position is in range,
    and fuel covers one `callProg` depth plus the aux shift
    (`len + 2 ≤ F`). -/
theorem evalProgFunc_stdVecInsertRval (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hbuf : len + 1 ≤ b.val.length)
    (hpos : pos.toNat ≤ len)
    (hlen1 : 1 ≤ len)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hS64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 2 ≤ F) :
    evalProgFunc vecGrowProg F stdVecInsertRvalFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecInsertRvalFwd b len cap pos x := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down (len + 1) hF
  have hlen64 : len < 2 ^ 64 := by omega
  have hlenT : (BitVec.ofNat 64 len).toNat = len :=
    ofNat64_toNat _ hlen64
  have hcapT : (BitVec.ofNat 64 cap).toNat = cap :=
    ofNat64_toNat _ hcap64
  have hlenp1T : (BitVec.ofNat 64 (len + 1)).toNat = len + 1 :=
    ofNat64_toNat _ (by omega)
  have hbind : bindArgs stdVecInsertRvalFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      some [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] := rfl
  have hbody : stdVecInsertRvalFunc.body =
      (.seq (.let_ "len" (.u 64) (.vgrowLen "t"))
      (.if_ (.ult (.var "len") (.vgrowCap "t"))
        (.if_ (.ueq (.var "pos") (.var "len"))
          (.seq (.callRet "t1" stdVecTraitsConstructName ["t", "pos", "x"])
            (.return_ (.vgrowSetLen "t1"
              (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))))
          (.seq (.callProg "t2" stdVecInsertAuxName ["t", "pos", "x"])
            (.return_ (.var "t2"))))
        (.seq (.callProg "t3" stdVecGrowReallocName ["t", "pos", "x"])
          (.return_ (.var "t3"))))) := rfl
  have ht0 : envLookup [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos), ("x", .i32 x)] "t" =
      some (.stdVecOwned b len cap) := by simp [envLookup]
  have hlenE : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht0
  have elen : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "len" (.u 64) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok ([("len", .u64 (BitVec.ofNat 64 len)),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)], .fellThrough) :=
    (evalProgStmt_let_fb _ _ _ _ _ _).trans
      (evalStmtFuel_let_ _ "len" (.u 64) (.vgrowLen "t")
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (.u64 (BitVec.ofNat 64 len)) hlenE)
  have htL : envLookup
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] "t" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup,
      show ("t" : String) ≠ "len" by decide]
  have hposV : evalExpr (.var "pos")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] = .ok (.u64 pos) := by
    simp [evalExpr, envLookup,
      show ("pos" : String) ≠ "len" by decide,
      show ("pos" : String) ≠ "t" by decide]
  have hlenV : evalExpr (.var "len")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    simp [evalExpr, envLookup]
  have hcapE : evalExpr (.vgrowCap "t")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 cap)) :=
    evalExpr_vgrowCap_some "t" _ b len cap htL
  have hultE : evalExpr (.ult (.var "len") (.vgrowCap "t"))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.b ((BitVec.ofNat 64 len).ult (BitVec.ofNat 64 cap))) :=
    evalExpr_ult_u64 _ _ _ _ _ hlenV hcapE
  have hueqE : evalExpr (.ueq (.var "pos") (.var "len"))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.b (pos == BitVec.ofNat 64 len)) :=
    evalExpr_ueq_u64_vars _ _ _ _ _ hposV hlenV
  have hargsT1 : lookupArgs
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      ["t", "pos", "x"] =
      some [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
    simp [lookupArgs, envLookup,
      show ("t" : String) ≠ "len" by decide,
      show ("pos" : String) ≠ "len" by decide,
      show ("pos" : String) ≠ "t" by decide,
      show ("x" : String) ≠ "len" by decide,
      show ("x" : String) ≠ "t" by decide,
      show ("x" : String) ≠ "pos" by decide]
  cases hroomB : (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 cap) with
  | true =>
    have hroom : len < cap := by
      have h := hroomB
      rw [BitVec.ult_eq_decide, hlenT, hcapT] at h
      exact of_decide_eq_true h
    have hcond : evalExpr (.ult (.var "len") (.vgrowCap "t"))
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] =
        .ok (.b true) := by simp [hultE, hroomB]
    cases heqB : (pos == BitVec.ofNat 64 len) with
    | true =>
      have hcond2 : evalExpr (.ueq (.var "pos") (.var "len"))
          [(("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.b true) := by simp [hueqE, heqB]
      have hcallC1 : evalFuncFuel (F' + 1) stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 pos, .i32 x] =
          stdVecConstructFwd b len cap pos x :=
        evalFuncFuel_stdVecConstruct _ b len cap pos x
      cases hcE : stdVecConstructFwd b len cap pos x with
      | error e =>
        have hcallC1' : evalFuncFuel (F' + 1) stdVecConstructFunc
            [.stdVecOwned b len cap, .u64 pos, .i32 x] = .error e := by
          rw [hcallC1, hcE]
        have hstepT1 := evalProgStmt_callRet_err vecGrowProg (F' + 1)
            "t1" stdVecTraitsConstructName ["t", "pos", "x"] _ _
            stdVecConstructFunc e hargsT1 findFunc_stdVecConstruct
            hcallC1'
        have hfwd : stdVecInsertRvalFwd b len cap pos x = .error e := by
          simp only [stdVecInsertRvalFwd, ite_eq_left hroom, ite_eq_left heqB,
            hcE, vecGrow_bind_err]
        have hstmt : evalProgStmt vecGrowProg (F' + 1)
            stdVecInsertRvalFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] = .error e := by
          rw [hbody]
          exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
            ((evalProgStmt_if_true _ _ _ _ _ _ hcond).trans
              ((evalProgStmt_if_true _ _ _ _ _ _ hcond2).trans
                (evalProgStmt_seq_err _ _ _ _ _ _ hstepT1)))
        simp only [evalProgFunc, hbind, hstmt, hfwd]
      | ok c1v =>
        obtain ⟨bC, hbc, _, _⟩ :=
          stdVecConstructFwd_ok b len cap pos x c1v hcE
        have hstepT1 := evalProgStmt_callRet_ok vecGrowProg (F' + 1)
            "t1" stdVecTraitsConstructName ["t", "pos", "x"] _ _
            stdVecConstructFunc c1v hargsT1 findFunc_stdVecConstruct
            (by rw [hcallC1, hcE])
        have ht1L : envLookup
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] "t1" = some c1v := by
          simp [envLookup]
        have ht1L' : envLookup
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] "t1" =
            some (.stdVecOwned bC len cap) := by
          rw [← hbc]; exact ht1L
        have hlenV1 : evalExpr (.var "len")
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok (.u64 (BitVec.ofNat 64 len)) := by
          simp [evalExpr, envLookup,
            show ("len" : String) ≠ "t1" by decide]
        have hlit1' : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok (.u64 (BitVec.ofNat 64 1)) := by
          simp [evalExpr, litVal]
        have hlenp1E : evalExpr
            (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok (.u64 (BitVec.ofNat 64 (len + 1))) := by
          have h := evalExpr_uadd_u64 _ _ _ _ _ hlenV1 hlit1'
          rwa [ofNat64_add_one len] at h
        have hsetE : evalExpr
            (.vgrowSetLen "t1"
              (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok (.stdVecOwned bC (len + 1) cap) := by
          have h := evalExpr_vgrowSetLen_hit "t1" _ _
            bC len cap (BitVec.ofNat 64 (len + 1)) ht1L' hlenp1E
          rwa [hlenp1T] at h
        have hret : evalProgStmt vecGrowProg (F' + 1)
            (.return_ (.vgrowSetLen "t1"
              (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok ([(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)],
              .returned (.stdVecOwned bC (len + 1) cap)) :=
          evalProgStmt_return _ _ _ _ _ hsetE
        have hfwd : stdVecInsertRvalFwd b len cap pos x =
            .ok (.stdVecOwned bC (len + 1) cap) := by
          simp only [stdVecInsertRvalFwd, ite_eq_left hroom, ite_eq_left heqB,
            hcE, vecGrow_bind_ok, vecGrowOwned, hbc]
        have hstmt : evalProgStmt vecGrowProg (F' + 1)
            stdVecInsertRvalFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok ([(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)],
              .returned (.stdVecOwned bC (len + 1) cap)) := by
          rw [hbody]
          exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
            ((evalProgStmt_if_true _ _ _ _ _ _ hcond).trans
              ((evalProgStmt_if_true _ _ _ _ _ _ hcond2).trans
                ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT1).trans
                  hret)))
        simp only [evalProgFunc, hbind, hstmt, hfwd]
    | false =>
      have hcond2 : evalExpr (.ueq (.var "pos") (.var "len"))
          [(("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.b false) := by simp [hueqE, heqB]
      have hneB : ¬ ((pos == BitVec.ofNat 64 len) = true) := by
        simp [heqB]
      have hcallA : evalProgFunc vecGrowProg F' stdVecInsertAuxFunc
          [.stdVecOwned b len cap, .u64 pos, .i32 x] =
          stdVecInsertAuxFwd b len cap pos x :=
        evalProgFunc_stdVecInsertAux F' b len cap pos x hlive hbuf
          hpos hlen1 hS64 hF'
      cases hA : stdVecInsertAuxFwd b len cap pos x with
      | error e =>
        have hcallA' : evalProgFunc vecGrowProg F' stdVecInsertAuxFunc
            [.stdVecOwned b len cap, .u64 pos, .i32 x] = .error e := by
          rw [hcallA, hA]
        have hstepT2 := evalProgStmt_callProg_err vecGrowProg F' "t2"
            stdVecInsertAuxName ["t", "pos", "x"] _ _
            stdVecInsertAuxFunc e hargsT1 findFunc_stdVecInsertAux
            hcallA'
        have hfwd : stdVecInsertRvalFwd b len cap pos x = .error e := by
          simp only [stdVecInsertRvalFwd, ite_eq_left hroom, ite_eq_right hneB, hA]
        have hstmt : evalProgStmt vecGrowProg (F' + 1)
            stdVecInsertRvalFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] = .error e := by
          rw [hbody]
          exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
            ((evalProgStmt_if_true _ _ _ _ _ _ hcond).trans
              ((evalProgStmt_if_false _ _ _ _ _ _ hcond2).trans
                (evalProgStmt_seq_err _ _ _ _ _ _ hstepT2)))
        simp only [evalProgFunc, hbind, hstmt, hfwd]
      | ok v =>
        have hcallA' : evalProgFunc vecGrowProg F' stdVecInsertAuxFunc
            [.stdVecOwned b len cap, .u64 pos, .i32 x] = .ok v := by
          rw [hcallA, hA]
        have hstepT2 := evalProgStmt_callProg_ok vecGrowProg F' "t2"
            stdVecInsertAuxName ["t", "pos", "x"] _ _
            stdVecInsertAuxFunc v hargsT1 findFunc_stdVecInsertAux
            hcallA'
        have hvarT2 : evalExpr (.var "t2")
            [(("t2", v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] = .ok v := by
          simp [evalExpr, envLookup]
        have hret : evalProgStmt vecGrowProg (F' + 1)
            (.return_ (.var "t2"))
            [(("t2", v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok ([(("t2", v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)], .returned v) :=
          evalProgStmt_return _ _ _ _ _ hvarT2
        have hfwd : stdVecInsertRvalFwd b len cap pos x = .ok v := by
          simp only [stdVecInsertRvalFwd, ite_eq_left hroom, ite_eq_right hneB, hA]
        have hstmt : evalProgStmt vecGrowProg (F' + 1)
            stdVecInsertRvalFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok ([(("t2", v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)], .returned v) := by
          rw [hbody]
          exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
            ((evalProgStmt_if_true _ _ _ _ _ _ hcond).trans
              ((evalProgStmt_if_false _ _ _ _ _ _ hcond2).trans
                ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT2).trans
                  hret)))
        simp only [evalProgFunc, hbind, hstmt, hfwd]
  | false =>
    have hroom : ¬ len < cap := by
      intro hlt
      have h := hroomB
      rw [BitVec.ult_eq_decide, hlenT, hcapT] at h
      simp [hlt] at h
    have hcond : evalExpr (.ult (.var "len") (.vgrowCap "t"))
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] =
        .ok (.b false) := by simp [hultE, hroomB]
    have hargsT3 : lookupArgs
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        ["t", "pos", "x"] =
        some [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
      simp [lookupArgs, envLookup,
        show ("t" : String) ≠ "len" by decide,
        show ("pos" : String) ≠ "len" by decide,
        show ("pos" : String) ≠ "t" by decide,
        show ("x" : String) ≠ "len" by decide,
        show ("x" : String) ≠ "t" by decide,
        show ("x" : String) ≠ "pos" by decide]
    have hcallR : evalProgFunc vecGrowProg F' stdVecGrowReallocFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] =
        stdVecGrowReallocFwd b len cap pos x :=
      evalProgFunc_stdVecGrowRealloc F' b len cap pos x hlive hmax
        hpos (by omega) hS64 (by omega) (by omega)
    cases hR : stdVecGrowReallocFwd b len cap pos x with
    | error e =>
      have hcallR' : evalProgFunc vecGrowProg F' stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 pos, .i32 x] = .error e := by
        rw [hcallR, hR]
      have hstepT3 := evalProgStmt_callProg_err vecGrowProg F' "t3"
          stdVecGrowReallocName ["t", "pos", "x"] _ _
          stdVecGrowReallocFunc e hargsT3 findFunc_stdVecGrowRealloc
          hcallR'
      have hfwd : stdVecInsertRvalFwd b len cap pos x = .error e := by
        simp only [stdVecInsertRvalFwd, ite_eq_right hroom, hR]
      have hstmt : evalProgStmt vecGrowProg (F' + 1)
          stdVecInsertRvalFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] = .error e := by
        rw [hbody]
        exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
          ((evalProgStmt_if_false _ _ _ _ _ _ hcond).trans
            (evalProgStmt_seq_err _ _ _ _ _ _ hstepT3))
      simp only [evalProgFunc, hbind, hstmt, hfwd]
    | ok v =>
      have hcallR' : evalProgFunc vecGrowProg F' stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 pos, .i32 x] = .ok v := by
        rw [hcallR, hR]
      have hstepT3 := evalProgStmt_callProg_ok vecGrowProg F' "t3"
          stdVecGrowReallocName ["t", "pos", "x"] _ _
          stdVecGrowReallocFunc v hargsT3 findFunc_stdVecGrowRealloc
          hcallR'
      have hvarT3 : evalExpr (.var "t3")
          [(("t3", v)),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] = .ok v := by
        simp [evalExpr, envLookup]
      have hret : evalProgStmt vecGrowProg (F' + 1)
          (.return_ (.var "t3"))
          [(("t3", v)),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok ([(("t3", v)),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)], .returned v) :=
        evalProgStmt_return _ _ _ _ _ hvarT3
      have hfwd : stdVecInsertRvalFwd b len cap pos x = .ok v := by
        simp only [stdVecInsertRvalFwd, ite_eq_right hroom, hR]
      have hstmt : evalProgStmt vecGrowProg (F' + 1)
          stdVecInsertRvalFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok ([(("t3", v)),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)], .returned v) := by
        rw [hbody]
        exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ elen).trans
          ((evalProgStmt_if_false _ _ _ _ _ _ hcond).trans
            ((evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepT3).trans
              hret))
      simp only [evalProgFunc, hbind, hstmt, hfwd]

/-- Value-level forward for the `insert` forwarder: delegate to
    `_M_insert_rval` (cf. `stdVecPushBackFwd`). -/
def stdVecInsertFwd (b : Vec32) (len cap : Nat) (pos : BitVec 64)
    (x : BitVec 32) : Result Value :=
  stdVecInsertRvalFwd b len cap pos x

/-- `emit_correct` for the `insert` forwarder: the program over the
    grown program agrees with the rval forward. Fuel covers one
    `callProg` depth plus the rval layer (`len + 3 ≤ F`). -/
theorem evalProgFunc_stdVecInsert (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hbuf : len + 1 ≤ b.val.length)
    (hpos : pos.toNat ≤ len)
    (hlen1 : 1 ≤ len)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hS64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 3 ≤ F) :
    evalProgFunc vecGrowProg F stdVecInsertFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecInsertFwd b len cap pos x := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down (len + 2) hF
  have hFwd : stdVecInsertFwd b len cap pos x =
      stdVecInsertRvalFwd b len cap pos x := rfl
  have hbind : bindArgs stdVecInsertFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      some [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] := rfl
  have hbody : stdVecInsertFunc.body =
      (.seq (.callProg "t1" stdVecInsertRvalName ["t", "pos", "x"])
        (.return_ (.var "t1"))) := rfl
  have hargs : lookupArgs [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos), ("x", .i32 x)]
      ["t", "pos", "x"] = some [.stdVecOwned b len cap, .u64 pos,
        .i32 x] := by
    simp [lookupArgs, envLookup,
      show ("pos" : String) ≠ "t" by decide,
      show ("x" : String) ≠ "t" by decide,
      show ("x" : String) ≠ "pos" by decide]
  have hcall : evalProgFunc vecGrowProg F' stdVecInsertRvalFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecInsertRvalFwd b len cap pos x :=
    evalProgFunc_stdVecInsertRval F' b len cap pos x hlive hbuf
      hpos hlen1 hmax hS64 hcap64 hF'
  cases hR : stdVecInsertRvalFwd b len cap pos x with
  | error e =>
    have hcall' : evalProgFunc vecGrowProg F' stdVecInsertRvalFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] = .error e := by
      rw [hcall, hR]
    have hstepCall := evalProgStmt_callProg_err vecGrowProg F' "t1"
        stdVecInsertRvalName ["t", "pos", "x"] _ _
        stdVecInsertRvalFunc e hargs findFunc_stdVecInsertRval hcall'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstepCall]
    simp only [hFwd, hR]
  | ok v =>
    have hcall' : evalProgFunc vecGrowProg F' stdVecInsertRvalFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] = .ok v := by
      rw [hcall, hR]
    have hstepCall := evalProgStmt_callProg_ok vecGrowProg F' "t1"
        stdVecInsertRvalName ["t", "pos", "x"] _ _
        stdVecInsertRvalFunc v hargs findFunc_stdVecInsertRval hcall'
    have hvar : evalExpr (.var "t1")
        [(("t1", v)), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] = .ok v := by
      simp [evalExpr, envLookup]
    have hret : evalProgStmt vecGrowProg (F' + 1)
        (.return_ (.var "t1"))
        [(("t1", v)), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] =
        .ok ([(("t1", v)), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)], .returned v) :=
      evalProgStmt_return _ _ _ _ _ hvar
    have hfwd : stdVecInsertFwd b len cap pos x = .ok v := by
      simp only [stdVecInsertFwd, hR]
    have hstmt : evalProgStmt vecGrowProg (F' + 1)
        stdVecInsertFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] =
        .ok ([(("t1", v)), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)], .returned v) := by
      rw [hbody]
      exact (evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCall).trans
        hret
    simp only [evalProgFunc, hbind, hstmt, hfwd]

/-! ## N7c-ii-b: `vec_insert_sum` entry -/

/-- Mangled name of the `vec_insert_sum` entry. -/
def vecInsertSumEntryName : String := "_Z14vec_insert_sumv"

/-- Canonical CoreIR for `tests/cpp/vec_insert_sum.cpp`: default ctor,
    `reserve(10)` via `callProg`, two fast-path `push_back`s (`1` then
    `3`), `begin` + `operator+ 1` for the position, the `insert`
    forwarder via `callProg` (the const-iterator converting ctor fuses:
    it is the identity copy of the offset), three indexed reads, two
    `nsw` adds, dtor, `trap`-less return of `6`. -/
def vecInsertSumEntryFunc : Func :=
  ⟨vecInsertSumEntryName, [], .i 32,
   .seq (.callRet "v0" stdVecCtorName [])
   (.seq (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
   (.seq (.callProg "v1" stdVecReserveName ["v0", "n"])
   (.seq (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
   (.seq (.callProg "v2" stdVecPushBackName ["v1", "c0"])
   (.seq (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
   (.seq (.callProg "v3" stdVecPushBackName ["v2", "c1"])
   (.seq (.callRet "bpos" stdVecBeginName ["v3"])
   (.seq (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.callRet "p1" stdVecPlusElName ["bpos", "one"])
   (.seq (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
   (.seq (.callProg "v4" stdVecInsertName ["v3", "p1", "c2"])
   (.seq (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq (.callRet "e0" stdVecGrowIndexName ["v4", "n0"])
   (.seq (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.callRet "e1" stdVecGrowIndexName ["v4", "n1"])
   (.seq (.let_ "s01" (.i 32) (.add (.var "e0") (.var "e1")))
   (.seq (.let_ "n2" (.u 64) (.lit (.u64 (BitVec.ofNat 64 2))))
   (.seq (.callRet "e2" stdVecGrowIndexName ["v4", "n2"])
   (.seq (.let_ "s" (.i 32) (.add (.var "s01") (.var "e2")))
   (.seq (.callRet "v5" stdVecDtorName ["v4"])
     (.return_ (.var "s"))))))))))))))))))))))⟩

/-- Value-level forward for `vec_insert_sum`: `reserve(10)` over the
    empty triple, two fast-path pushes (`1`, `3`), `begin` + one step,
    the `insert` forwarder at position `1`, three indexed reads,
    `checkedAddI32` twice, destructor, return `6`. -/
def vecInsertSumEntryFwd : Result Value :=
  (stdVecReserveFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 64 10)).bind fun v1 =>
  (vecGrowOwned v1).bind fun (b1, l1, c1) =>
  (stdVecPushBackFwd b1 l1 c1 (BitVec.ofNat 32 1)).bind fun v2 =>
  (vecGrowOwned v2).bind fun (b2, l2, c2) =>
  (stdVecPushBackFwd b2 l2 c2 (BitVec.ofNat 32 3)).bind fun v3 =>
  (vecGrowOwned v3).bind fun (b3, l3, c3) =>
  (stdVecBeginFwd).bind fun bgv =>
  (vecGrowU64 bgv).bind fun bpos =>
  (stdVecPlusElFwd bpos (BitVec.ofNat 64 1)).bind fun p1v =>
  (vecGrowU64 p1v).bind fun p1 =>
  (stdVecInsertFwd b3 l3 c3 p1 (BitVec.ofNat 32 2)).bind fun v4 =>
  (vecGrowOwned v4).bind fun (b4, l4, c4) =>
  (stdVecGrowIndexFwd b4 l4 (BitVec.ofNat 64 0)).bind fun e0v =>
  (vecGrowI32 e0v).bind fun e0 =>
  (stdVecGrowIndexFwd b4 l4 (BitVec.ofNat 64 1)).bind fun e1v =>
  (vecGrowI32 e1v).bind fun e1 =>
  (checkedAddI32 e0 e1).bind fun s01 =>
  (stdVecGrowIndexFwd b4 l4 (BitVec.ofNat 64 2)).bind fun e2v =>
  (vecGrowI32 e2v).bind fun e2 =>
  (checkedAddI32 s01 e2).bind fun s =>
  (stdVecDtorFwd b4 l4 c4).bind fun _ =>
  .ok (.i32 s)

/-- Second fast-path push writes `3` at index `1`. -/
theorem vecInsertPush2_eq :
    stdVecPushBackFwd
      ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10
      (BitVec.ofNat 32 3) =
      .ok (.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10) := rfl

/-- Iterator advance computes `0 + 1`. -/
theorem vecInsertPlusEl_eq :
    stdVecPlusElFwd (BitVec.ofNat 64 0) (BitVec.ofNat 64 1) =
      .ok (.u64 (BitVec.ofNat 64 1)) := rfl

/-- The `insert` at position `1` shifts `[1, 3)` right and writes `2`. -/
theorem vecInsertStep_eq :
    stdVecInsertFwd
      ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 3)), false⟩ 2 10
      (BitVec.ofNat 64 1) (BitVec.ofNat 32 2) =
      .ok (.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10) := rfl

/-- Indexed reads pin the three words. -/
theorem vecInsertRead0_eq :
    stdVecGrowIndexFwd
      ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), false⟩ 3
      (BitVec.ofNat 64 0) =
      .ok (.i32 (BitVec.ofNat 32 1)) := rfl

/-- Indexed reads pin the three words. -/
theorem vecInsertRead1_eq :
    stdVecGrowIndexFwd
      ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), false⟩ 3
      (BitVec.ofNat 64 1) =
      .ok (.i32 (BitVec.ofNat 32 2)) := rfl

/-- Indexed reads pin the three words. -/
theorem vecInsertRead2_eq :
    stdVecGrowIndexFwd
      ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), false⟩ 3
      (BitVec.ofNat 64 2) =
      .ok (.i32 (BitVec.ofNat 32 3)) := rfl

/-- The second `nsw` add computes `6`. -/
theorem vecInsertAdd2_eq :
    checkedAddI32 (BitVec.ofNat 32 3) (BitVec.ofNat 32 3) =
      .ok (BitVec.ofNat 32 6) := rfl

/-- The destructor frees the three-word triple. -/
theorem vecInsertDtor_eq :
    stdVecDtorFwd
      ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), false⟩ 3 10 =
      .ok (.stdVecOwned
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), true⟩
        3 10) := rfl

/-- `emit_correct` for `vec_insert_sum`: the closed entry over the
    grown program agrees with the compute-to-`6` forward.

    N8b: this was a ~1330-line hand evaluation (one `have` per script
    step with fully transcribed envs). Both sides are closed terms —
    `#eval` reduces each to `.ok 6` — so the proof is a single
    kernel-checked native computation. `rfl` cannot see through the
    well-founded recursion in `evalProgFunc`
    (`termination_by (fuel, 1, f.body)`), hence `native_decide`,
    which needs the lawful `DecidableEq (Result Value)` instance in
    `Circe.Eval.Core`. Stated at the concrete fuel the script needs
    (`6`); a fuel-general statement would need a fuel-monotonicity
    lemma we do not have — and no consumer needs general `F`
    (entries are proof-graph leaves). -/
theorem evalProgFunc_vecInsertSumEntry :
    evalProgFunc vecGrowProg 6 vecInsertSumEntryFunc [] =
      vecInsertSumEntryFwd := by
  cir_eval_closed
