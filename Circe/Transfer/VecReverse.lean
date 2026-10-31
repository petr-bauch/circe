/-
Circe.Transfer.VecReverse — R2 transfer for `std::vector<int32_t>`
in-place reverse (countdown two-pointer swaps).

Mirrors `evalProgFunc_vecReverse` step for step on the memory layer:
the frozen `size` / checked-`at()` callees communicate by value
(caller `Mem`/`Layout` thread through unchanged), the two `vecSet`
stores thread through `memStore` in lockstep (the `+ 1` skips the
reified length word), and the loop re-inducts over `(ρ, m, π)` with
the find-characterized memory invariant (`memFind m 0` pins the
`(1 + n)`-word snapshot; stores prepend shadowing blocks, so the
invariant is by-find, never by-equality).
-/
import Circe.Transfer.Slice
import Circe.Emit.VecReverse

/-! ## Memory bridges (program level) -/

/-- Program-level memory `assign` (leaves delegate). -/
theorem memRevAssign (prog : Prog) (F : Nat) (x : String) (e : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (v : Value) (ρ' : Env)
    (h : memEvalExpr e ρ m π = .ok v)
    (hv : evalExpr e ρ = .ok v) (hu : envUpdate ρ x v = some ρ') :
    memEvalProgStmt prog F (.assign x e) ρ m π =
      .ok ((ρ', m, π), .fellThrough) := by
  have hag : memEvalExpr e ρ m π = evalExpr e ρ := by rw [h, hv]
  simpa [memEvalProgStmt] using
    (memEvalStmtFuel_assign F x e ρ m π v ρ' hag hv hu)

/-- Program-level memory `let_` (binds, extends; memory untouched;
    pure right-hand sides only, via `memEvalStmtFuel_let_pure`). -/
theorem memRevLet (prog : Prog) (F : Nat) (x : String) (ty : CType)
    (e : CExpr) (ρ : Env) (m : Mem) (π : Layout) (v : Value)
    (hnot : ∀ se, e ≠ .vnew se)
    (hnotBox : ∀ se, e ≠ .boxNew se)
    (hnotGrow : ∀ ce, e ≠ .vgrowNew ce)
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v) :
    memEvalProgStmt prog F (.let_ x ty e) ρ m π =
      .ok ((envExtend ρ x v, m, π), .fellThrough) := by
  rw [memEvalProgStmt_let_fb prog F x ty e ρ m π]
  exact memEvalStmtFuel_let_pure F x ty e ρ m π v
    hnot hnotBox hnotGrow h hv

/-- Program-level memory borrowed store (leaves delegate). -/
theorem memRevVecSet (prog : Prog) (F : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (m : Mem) (π : Layout)
    (i : BitVec 64) (xv : BitVec 32) (a t : Nat)
    (l : List (BitVec 32)) (w : BitVec 32) (m' : Mem) (ρ' : Env)
    (hi : memEvalExpr ie ρ m π = .ok (.u64 i))
    (hv : memEvalExpr ve ρ m π = .ok (.i32 xv))
    (hvec : envLookup ρ x = some (.stdVecVal l))
    (hlay : layoutLookup π x = some (a, t))
    (hget : l[i.toNat]? = some w)
    (hmstore : memStore m a t (i.toNat + 1) xv = .ok m')
    (hu : envUpdate ρ x (.stdVecVal (l.set i.toNat xv)) = some ρ') :
    memEvalProgStmt prog F (.vecSet x ie ve) ρ m π =
      .ok ((ρ', m', π), .fellThrough) := by
  simpa [memEvalProgStmt] using
    (memEvalStmtFuel_vecSet F x ie ve ρ m π i xv a t l w m' ρ'
      hi hv hvec hlay hget hmstore hu)

/-- The renamed `at()` leaf evaluates like `stdVecAtFunc` on memory
    (only the name differs; `memEvalFuncFuel` never inspects it). -/
theorem memRevAtBridge (F : Nat) (l : List (BitVec 32)) (n : BitVec 64) :
    memEvalFuncFuel F { stdVecAtFunc with name := stdVecAtMutName }
      [.stdVecVal l, .u64 n] =
      memEvalFuncFuel F stdVecAtFunc [.stdVecVal l, .u64 n] := by
  cases F <;> rfl

/-- The renamed `at()` leaf agrees with `stdVecAtFwd` on memory. -/
theorem memRevAtEval (F : Nat) (l : List (BitVec 32)) (n : BitVec 64)
    (hlen64 : l.length < 2 ^ 64) :
    memEvalFuncFuel F { stdVecAtFunc with name := stdVecAtMutName }
      [.stdVecVal l, .u64 n] = stdVecAtFwd l n := by
  rw [memRevAtBridge]
  exact memEvalFuncFuel_stdVecAt F l n hlen64

/-! ## Memory store threading -/

/-- A successful store on the reified snapshot shape yields the
    shadow-prepended memory (closed form for lockstep threading). -/
theorem revMemStore_ok (m : Mem) (words : List (BitVec 32)) (k : Nat)
    (x : BitVec 32)
    (hfind : memFind m 0 = some ⟨0, true, words⟩)
    (hlt : k < words.length) :
    memStore m 0 0 k x =
      .ok ⟨m.next, (0, ⟨0, true, words.set k x⟩) :: m.blocks,
        m.blocks64⟩ := by
  unfold memStore
  simp only [hfind]
  rw [ite_eq_right (by decide : ¬ ((0 != 0) = true)),
    ite_eq_right (by decide : ¬ ((!true) = true)), dite_eq_left hlt]

/-- One body iteration on memory: the env threads exactly as on the
    value side while the two stores prepend shadowing snapshot blocks
    (layout stays pinned; the length word is never touched). -/
theorem memBody_hit (F : Nat) (ρ : Env) (m : Mem) (π : Layout)
    (orig l : List (BitVec 32)) (n i j : Nat)
    (iB jB : BitVec 64) (a b : BitVec 32)
    (hinv : RevInv orig l n i j)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (hlt : i < j)
    (ha : l[i]? = some a) (hb : l[j - 1]? = some b)
    (hn64 : n < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hlay : layoutLookup π "v" = some (0, 0))
    (hmem : memFind m 0 =
      some ⟨0, true, (BitVec.ofNat 32 n) :: l⟩) :
    ∃ ρ' m', memEvalProgStmt vecReverseProg F vecReverseBody ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal ((l.set i b).set (j - 1) a)) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      envLookup ρ' "j" = some (.u64 (jB - 1)) ∧
      memFind m' 0 = some ⟨0, true, (BitVec.ofNat 32 n) ::
        ((l.set i b).set (j - 1) a)⟩ ∧
      RevInv orig ((l.set i b).set (j - 1) a) n (i + 1) (j - 1) := by
  obtain ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩ := hinv
  have hn : l.length = n := hlen
  have hlen64 : l.length < 2 ^ 64 := by omega
  have hL0 : ((BitVec.ofNat 32 n) :: l).length = l.length + 1 := rfl
  have hL1 : ((BitVec.ofNat 32 n) :: l.set i b).length =
      (l.set i b).length + 1 := rfl
  have hlenS : (l.set i b).length = n := by
    rw [List.length_set]; exact hn
  -- `--j` (memory untouched).
  have vexpr_j : evalExpr (.usub (.var "j") (.lit (.u64 1))) ρ =
      .ok (.u64 (jB - 1)) :=
    evalExpr_u64_usub _ _ _ _
      (evalExpr_var_hit _ _ _ hj)
  have mexpr_j : memEvalExpr (.usub (.var "j") (.lit (.u64 1)))
      ρ m π = .ok (.u64 (jB - 1)) := by
    rw [memEvalExpr_usub_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)]
    exact vexpr_j
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "j" (.u64 jB)
    (.u64 (jB - 1)) hj
  have hstep_j := memRevAssign vecReverseProg F "j"
    (.usub (.var "j") (.lit (.u64 1))) ρ m π (.u64 (jB - 1)) ρ₁
    mexpr_j vexpr_j hu₁
  have hj₁ : envLookup ρ₁ "j" = some (.u64 (jB - 1)) :=
    envLookup_update_hit _ _ _ _ hu₁
  have hv₁ : envLookup ρ₁ "v" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "j" by decide) hu₁]
    exact hv
  have hi₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "j" by decide) hu₁]
    exact hi
  -- `a ← at(v, i)` (callee communicates by value).
  have hai : l[iB.toNat]? = some a := by rw [hiN]; exact ha
  have hlt_i : iB.toNat < l.length := by omega
  have hargs_a : lookupArgs ρ₁ ["v", "i"] =
      some [.stdVecVal l, .u64 iB] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₁
      (lookupArgs_cons_hit _ _ _ _ _ hi₁ (lookupArgs_nil _))
  have hcall_a : memEvalFuncFuel F
      { stdVecAtFunc with name := stdVecAtMutName }
      [.stdVecVal l, .u64 iB] = .ok (.i32 a) := by
    rw [memRevAtEval F l iB hlen64]
    exact stdVecAtFwd_ok l iB a hlt_i hai
  have hstep_a := memEvalProgStmt_callRet_ok vecReverseProg F "a"
    stdVecAtMutName ["v", "i"] ρ₁ m π [.stdVecVal l, .u64 iB]
    { stdVecAtFunc with name := stdVecAtMutName } (.i32 a)
    hargs_a revFindAt hcall_a
  have ha₂ : envLookup (envExtend ρ₁ "a" (.i32 a)) "a" =
      some (.i32 a) :=
    envExtend_hit _ _ _
  have hv₂ : envLookup (envExtend ρ₁ "a" (.i32 a)) "v" =
      some (.stdVecVal l) :=
    envLookup_extend_miss _ _ _ _ _ hv₁ (by decide)
  have hi₂ : envLookup (envExtend ρ₁ "a" (.i32 a)) "i" =
      some (.u64 iB) :=
    envLookup_extend_miss _ _ _ _ _ hi₁ (by decide)
  have hj₂ : envLookup (envExtend ρ₁ "a" (.i32 a)) "j" =
      some (.u64 (jB - 1)) :=
    envLookup_extend_miss _ _ _ _ _ hj₁ (by decide)
  -- `b ← at(v, j)` (`j` already decremented).
  have hpred : (jB - 1).toNat = j - 1 := by
    rw [revU64_pred_toNat jB (by omega), hjN]
  have hbj : l[(jB - 1).toNat]? = some b := by
    rw [hpred]; exact hb
  have hlt_j : (jB - 1).toNat < l.length := by omega
  have hargs_b : lookupArgs (envExtend ρ₁ "a" (.i32 a)) ["v", "j"] =
      some [.stdVecVal l, .u64 (jB - 1)] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₂
      (lookupArgs_cons_hit _ _ _ _ _ hj₂ (lookupArgs_nil _))
  have hcall_b : memEvalFuncFuel F
      { stdVecAtFunc with name := stdVecAtMutName }
      [.stdVecVal l, .u64 (jB - 1)] = .ok (.i32 b) := by
    rw [memRevAtEval F l (jB - 1) hlen64]
    exact stdVecAtFwd_ok l (jB - 1) b hlt_j hbj
  have hstep_b := memEvalProgStmt_callRet_ok vecReverseProg F "b"
    stdVecAtMutName ["v", "j"] (envExtend ρ₁ "a" (.i32 a)) m π
    [.stdVecVal l, .u64 (jB - 1)]
    { stdVecAtFunc with name := stdVecAtMutName } (.i32 b)
    hargs_b revFindAt hcall_b
  have hb₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "b" = some (.i32 b) :=
    envExtend_hit _ _ _
  have hv₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "v" = some (.stdVecVal l) :=
    envLookup_extend_miss _ _ _ _ _ hv₂ (by decide)
  have hi₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "i" = some (.u64 iB) :=
    envLookup_extend_miss _ _ _ _ _ hi₂ (by decide)
  have hj₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "j" = some (.u64 (jB - 1)) :=
    envLookup_extend_miss _ _ _ _ _ hj₂ (by decide)
  have ha₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "a" = some (.i32 a) :=
    envLookup_extend_miss _ _ _ _ _ ha₂ (by decide)
  -- `v[i] := b` (first shadowing store).
  obtain ⟨ρ₄, hu₄⟩ := envUpdate_some_of_lookup
    (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b)) "v"
    (.stdVecVal l) (.stdVecVal (l.set iB.toNat b)) hv₃
  have mvexpr_i : memEvalExpr (.var "i")
      (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b)) m π =
      .ok (.u64 iB) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ hi₃
  have mvexpr_b : memEvalExpr (.var "b")
      (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b)) m π =
      .ok (.i32 b) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ hb₃
  have hlt_s1 : iB.toNat + 1 < ((BitVec.ofNat 32 n) :: l).length := by
    omega
  have hmstore₁ := revMemStore_ok m ((BitVec.ofNat 32 n) :: l)
    (iB.toNat + 1) b hmem hlt_s1
  have hwords₁ : ((BitVec.ofNat 32 n) :: l).set (iB.toNat + 1) b =
      (BitVec.ofNat 32 n) :: l.set i b := by
    rw [show iB.toNat + 1 = i + 1 from by omega]
    exact List.set_cons_succ
  have hstep_s1 := memRevVecSet vecReverseProg F "v" (.var "i") (.var "b")
    (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b)) m π
    iB b 0 0 l a
    ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
      (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ ρ₄
    mvexpr_i mvexpr_b hv₃ hlay hai hmstore₁ hu₄
  have hmem₁ : memFind ⟨m.next, (0, ⟨0, true,
      ((BitVec.ofNat 32 n) :: l).set (iB.toNat + 1) b⟩) ::
      m.blocks, m.blocks64⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 n) :: l.set i b⟩ := by
    rw [hwords₁]
    exact memFind_cons_hit _ _ _ _ _
  have hv₄ : envLookup ρ₄ "v" =
      some (.stdVecVal (l.set iB.toNat b)) :=
    envLookup_update_hit _ _ _ _ hu₄
  have hi₄ : envLookup ρ₄ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₄]
    exact hi₃
  have hj₄ : envLookup ρ₄ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "v" by decide) hu₄]
    exact hj₃
  have ha₄ : envLookup ρ₄ "a" = some (.i32 a) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "v" by decide) hu₄]
    exact ha₃
  -- `v[j] := a` (second shadowing store).
  have hlen1 : (l.set iB.toNat b).length = l.length := List.length_set
  have hsetI : l.set iB.toNat b = l.set i b := by rw [hiN]
  have hjL2 : (jB - 1).toNat + 1 <
      ((BitVec.ofNat 32 n) :: l.set i b).length := by omega
  have hcur : (l.set iB.toNat b)[(jB - 1).toNat]? =
      some ((l.set iB.toNat b)[(jB - 1).toNat]) := by
    have hjL1 : (jB - 1).toNat < (l.set iB.toNat b).length := by omega
    exact List.getElem?_eq_getElem hjL1
  obtain ⟨ρ₅, hu₅⟩ := envUpdate_some_of_lookup ρ₄ "v"
    (.stdVecVal (l.set iB.toNat b))
    (.stdVecVal ((l.set iB.toNat b).set (jB - 1).toNat a)) hv₄
  have mvexpr_j : memEvalExpr (.var "j") ρ₄
      ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
        (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ π =
      .ok (.u64 (jB - 1)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ hj₄
  have mvexpr_a : memEvalExpr (.var "a") ρ₄
      ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
        (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ π =
      .ok (.i32 a) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ ha₄
  have hmstore₂ := revMemStore_ok
    ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
      (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩
    ((BitVec.ofNat 32 n) :: l.set i b) ((jB - 1).toNat + 1) a
    hmem₁ (by omega)
  have hwords₂ : ((BitVec.ofNat 32 n) :: l.set i b).set
      ((jB - 1).toNat + 1) a =
      (BitVec.ofNat 32 n) :: (l.set i b).set (j - 1) a := by
    rw [show (jB - 1).toNat + 1 = (j - 1) + 1 from by omega]
    exact List.set_cons_succ
  have hstep_s2 := memRevVecSet vecReverseProg F "v" (.var "j") (.var "a")
    ρ₄ ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
      (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ π
    (jB - 1) a 0 0 (l.set iB.toNat b)
    ((l.set iB.toNat b)[(jB - 1).toNat])
    ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l.set i b).set
      ((jB - 1).toNat + 1) a⟩) ::
      (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
        (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ ρ₅
    mvexpr_j mvexpr_a hv₄ hlay hcur hmstore₂ hu₅
  have hmem₂ : memFind ⟨m.next, (0, ⟨0, true,
      ((BitVec.ofNat 32 n) :: l.set i b).set ((jB - 1).toNat + 1) a⟩) ::
      (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
        (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 n) ::
        (l.set i b).set (j - 1) a⟩ := by
    rw [hwords₂]
    exact memFind_cons_hit _ _ _ _ _
  have hv₅ : envLookup ρ₅ "v" =
      some (.stdVecVal ((l.set iB.toNat b).set (jB - 1).toNat a)) :=
    envLookup_update_hit _ _ _ _ hu₅
  have hi₅ : envLookup ρ₅ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₅]
    exact hi₄
  have hj₅ : envLookup ρ₅ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "v" by decide) hu₅]
    exact hj₄
  -- `++i` (memory untouched).
  have vexpr_i : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₅ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hi₅) (by simp [evalExpr, litVal])
  have mexpr_i : memEvalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₅
      ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l.set i b).set
        ((jB - 1).toNat + 1) a⟩) ::
        (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
          (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ π =
      .ok (.u64 (iB + 1)) := by
    rw [memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)]
    exact vexpr_i
  obtain ⟨ρ₆, hu₆⟩ := envUpdate_some_of_lookup ρ₅ "i" (.u64 iB)
    (.u64 (iB + 1)) hi₅
  have hstep_i := memRevAssign vecReverseProg F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₅
    ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l.set i b).set
      ((jB - 1).toNat + 1) a⟩) ::
      (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
        (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ π
    (.u64 (iB + 1)) ρ₆ mexpr_i vexpr_i hu₆
  have hi₆ : envLookup ρ₆ "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₆
  have hv₆ : envLookup ρ₆ "v" =
      some (.stdVecVal ((l.set iB.toNat b).set (jB - 1).toNat a)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu₆]
    exact hv₅
  have hj₆ : envLookup ρ₆ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "i" by decide) hu₆]
    exact hj₅
  -- Assemble the sequential body.
  have hbody : vecReverseBody =
      (.seq (.assign "j" (.usub (.var "j") (.lit (.u64 1))))
        (.seq (.callRet "a" stdVecAtMutName ["v", "i"])
          (.seq (.callRet "b" stdVecAtMutName ["v", "j"])
            (.seq (.vecSet "v" (.var "i") (.var "b"))
              (.seq (.vecSet "v" (.var "j") (.var "a"))
                (.assign "i"
                  (.uadd (.var "i") (.lit (.u64 1))))))))) := rfl
  have heval : memEvalProgStmt vecReverseProg F vecReverseBody ρ m π =
      .ok ((ρ₆, ⟨m.next, (0, ⟨0, true,
        ((BitVec.ofNat 32 n) :: l.set i b).set ((jB - 1).toNat + 1) a⟩) ::
        (0, ⟨0, true, ((BitVec.ofNat 32 n) :: l).set
          (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩, π),
        .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_j,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_a,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_b,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_s1,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_s2,
      hstep_i]
  -- BitVec indices back to Nat indices.
  have hfinal : ((l.set iB.toNat b).set (jB - 1).toNat a) =
      ((l.set i b).set (j - 1) a) := by
    rw [hsetI, hpred]
  have hstep := RevInv_step orig l n i j a b
    ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩ hlt ha hb
  refine ⟨ρ₆, _, heval, ?_, ?_, ?_, ?_, ?_⟩
  · exact hfinal ▸ hv₆
  · exact hi₆
  · exact hj₆
  · exact hfinal ▸ hmem₂
  · exact hfinal ▸ hstep

/-! ## Memory loop -/

/-- The countdown loop on memory evaluates to the fully-reversed words
    (fuel induction against `revIters`, mirroring `revWhile_ok`; the
    memory invariant threads the shadowing snapshots alongside). -/
theorem memWhile_ok (F : Nat) (ρ : Env) (m : Mem) (π : Layout)
    (orig l : List (BitVec 32)) (n i j : Nat)
    (iB jB : BitVec 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB)) (hiN : iB.toNat = i)
    (hj : envLookup ρ "j" = some (.u64 jB)) (hjN : jB.toNat = j)
    (hinv : RevInv orig l n i j)
    (hn64 : n < 2 ^ 64)
    (hlay : layoutLookup π "v" = some (0, 0))
    (hmem : memFind m 0 =
      some ⟨0, true, (BitVec.ofNat 32 n) :: l⟩)
    (hF : revIters i j + 1 ≤ F) :
    ∃ ρ' m', memEvalProgStmt vecReverseProg F vecReverseWhile ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal orig.reverse) := by
  induction F generalizing ρ m π l i j iB jB with
  | zero =>
    have hfalse : False := by
      have hpos : 0 < revIters i j + 1 := Nat.succ_pos _
      omega
    exact hfalse.elim
  | succ F ih =>
    by_cases h : i < j
    · -- Live iteration: guard true, body swaps, recurse on the window.
      have hguardV : evalExpr (.ult (.var "i") (.var "j")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.var "j") ρ iB jB
          (evalExpr_var_hit _ _ _ hi) (evalExpr_var_hit _ _ _ hj)
        have htb : (iB.ult jB) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      have hguard : memEvalExpr (.ult (.var "i") (.var "j")) ρ m π =
          .ok (.b true) := by
        rw [memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)]
        exact hguardV
      obtain ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩ := hinv
      have hiL : i < l.length := by omega
      have hjL : j - 1 < l.length := by omega
      obtain ⟨ρ₆, m₆, heval, hv₆, hi₆, hj₆, hmem₆, hinv₆⟩ :=
        memBody_hit F ρ m π orig l n i j iB jB l[i] l[j - 1]
          ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩
          hiN hjN h
          (List.getElem?_eq_getElem hiL)
          (List.getElem?_eq_getElem hjL)
          hn64 hv hi hj hlay hmem
      have hR : revIters i j = revIters (i + 1) (j - 1) + 1 :=
        (revIters_step i j h).symm
      have hF' : revIters (i + 1) (j - 1) + 1 ≤ F := by omega
      have hiN₆ : (iB + 1).toNat = i + 1 := by
        rw [revU64_succ_toNat iB n (by omega) hn64, hiN]
      have hjN₆ : (jB - 1).toNat = j - 1 := by
        rw [revU64_pred_toNat jB (by omega), hjN]
      obtain ⟨ρ', m', hloop, hv'⟩ :=
        ih ρ₆ m₆ π ((l.set i l[j - 1]).set (j - 1) l[i])
          (i + 1) (j - 1) (iB + 1) (jB - 1)
          hv₆ hi₆ hiN₆ hj₆ hjN₆ hinv₆ hlay hmem₆ hF'
      refine ⟨ρ', m', ?_, hv'⟩
      have hwhile : memEvalProgStmt vecReverseProg (F + 1)
          vecReverseWhile ρ m π =
          memEvalProgStmt vecReverseProg F vecReverseWhile ρ₆ m₆ π := by
        cir_unfold_prog (vecReverseWhile, vecReverseProg, F, hguard, heval)
      rw [hwhile]
      exact hloop
    · -- Exit: guard false, state exits; the value invariant (threaded
      -- alongside) closes to `reverse`.
      have hguardV : evalExpr (.ult (.var "i") (.var "j")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.var "j") ρ iB jB
          (evalExpr_var_hit _ _ _ hi) (evalExpr_var_hit _ _ _ hj)
        have hfb : (iB.ult jB) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hguard : memEvalExpr (.ult (.var "i") (.var "j")) ρ m π =
          .ok (.b false) := by
        rw [memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)]
        exact hguardV
      have hexit : memEvalProgStmt vecReverseProg (F + 1)
          vecReverseWhile ρ m π =
          .ok ((ρ, m, π), .fellThrough) := by
        simp only [vecReverseWhile,
          memEvalProgStmt_while_false vecReverseProg _ _ _ _ _ _
            hguard]
      have hrev : l = orig.reverse :=
        RevInv_exit orig l n i j hinv (by omega)
      have hvrev : envLookup ρ "v" = some (.stdVecVal orig.reverse) := by
        rw [← hrev]; exact hv
      exact ⟨ρ, m, hexit, hvrev⟩

/-! ## Entry bridge (`memEval` + transfer) -/

/-- `memEval` for `vec_reverse`: program evaluation over the frozen
    `size` / checked-`at()` leaves agrees with list reversal on memory
    (mirrors `evalProgFunc_vecReverse`; caller memory threads through
    the calls, stores lockstep through `memStore`). -/
theorem memEvalProgFunc_vecReverse (F : Nat) (l : List (BitVec 32))
    (hn64 : l.length < 2 ^ 64)
    (hF : revIters 0 l.length + 1 ≤ F) :
    memEvalProgFunc vecReverseProg F vecReverseFunc [.stdVecVal l] =
      vecReverseFwd l := by
  have hb : bindMemArgs vecReverseFunc.args [.stdVecVal l] emptyMem =
      some ([("v", .stdVecVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) :=
    bindMemArgs_stdVecVal "v" stdVecObjTy l
  have hbind := hb
  have hbody : vecReverseFunc.body =
      (.seq (.callRet "m" stdVecSizeName ["v"])
        (.seq (.let_ "i" (.u 64) (.lit (.u64 0)))
          (.seq (.let_ "j" (.u 64) (.var "m"))
            (.seq (.let_ "t" (.i 32) (.lit (.i32 0)))
              (.seq vecReverseWhile
                (.return_ (.var "v"))))))) := rfl
  have hlay₀ : layoutLookup [("v", 0, 0)] "v" = some (0, 0) := by
    simp [layoutLookup]
  have hmem₀ : memFind ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  -- `m ← size(v)` (callee communicates by value).
  have hargs_m : lookupArgs [("v", .stdVecVal l)] ["v"] =
      some [.stdVecVal l] :=
    lookupArgs_cons_hit _ _ _ _ _
      (by simp [envLookup]) (lookupArgs_nil _)
  have hcall_m : memEvalFuncFuel F stdVecSizeFunc [.stdVecVal l] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [memEvalFuncFuel_stdVecSize]
    rfl
  have hstep_m := memEvalProgStmt_callRet_ok vecReverseProg F "m"
    stdVecSizeName ["v"] [("v", .stdVecVal l)]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
    [.stdVecVal l] stdVecSizeFunc (.u64 (BitVec.ofNat 64 l.length))
    hargs_m revFindSize hcall_m
  -- `i ← 0`, `j ← m`, `t ← 0`.
  have hstep_i := memRevLet vecReverseProg F "i" (.u 64)
    (.lit (.u64 0)) (envExtend [("v", .stdVecVal l)] "m"
      (.u64 (BitVec.ofNat 64 l.length)))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
    (.u64 0) (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (memEvalExpr_lit _ _ _ _)
    (by simp [evalExpr, litVal])
  have hm₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "i" (.u64 0)) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envExtend_miss _ _ _ _
      (show ("m" : String) ≠ "i" by decide)]
    exact envExtend_hit _ _ _
  have hstep_j := memRevLet vecReverseProg F "j" (.u 64) (.var "m")
    (envExtend (envExtend [("v", .stdVecVal l)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "i" (.u64 0))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
    (.u64 (BitVec.ofNat 64 l.length))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (memEvalExpr_var _ _ _ _)
    (evalExpr_var_hit _ _ _ hm₂)
  have hstep_t := memRevLet vecReverseProg F "t" (.i 32)
    (.lit (.i32 0)) (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length)))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
    (.i32 0) (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (memEvalExpr_lit _ _ _ _)
    (by simp [evalExpr, litVal])
  -- Loop from `(0, n)`.
  have hjN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn64
  have hinv₀ : RevInv l l l.length 0 l.length :=
    ⟨rfl, rfl, by omega, Nat.zero_le _, Nat.le_refl _,
      fun p hp => (Nat.not_lt_zero p hp).elim,
      fun p hp hlt => absurd hlt (by omega),
      fun p _ _ => rfl⟩
  have hv₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length)))
      "t" (.i32 0)) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "t" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "j" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "m" by decide)]
    simp [envLookup]
  have hj₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length)))
      "t" (.i32 0)) "j" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envExtend_miss _ _ _ _
      (show ("j" : String) ≠ "t" by decide)]
    exact envExtend_hit _ _ _
  have hi₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length)))
      "t" (.i32 0)) "i" =
      some (.u64 0) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "t" by decide),
      envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "j" by decide)]
    exact envExtend_hit _ _ _
  obtain ⟨ρ', m', hloop, hv'⟩ :=
    memWhile_ok F (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length)))
      "t" (.i32 0))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
      l l l.length 0 l.length
      0 (BitVec.ofNat 64 l.length)
      hv₄ hi₄ rfl hj₄ hjN
      hinv₀ hn64 hlay₀ hmem₀ hF
  -- `return v`.
  have hretV : memEvalExpr (.var "v") ρ' m' [("v", 0, 0)] =
      evalExpr (.var "v") ρ' := memEvalExpr_var _ _ _ _
  have hret := memEvalProgStmt_return vecReverseProg F (.var "v") ρ' m'
    [("v", 0, 0)] (.stdVecVal l.reverse)
    (by rw [hretV]; exact evalExpr_var_hit _ _ _ hv')
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_m,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_i,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_j,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_t,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
    hret]
  simp [vecReverseFwd]

/-- Transfer for `vec_reverse` (program level). -/
theorem memTransferProg_vecReverse (F : Nat) (l : List (BitVec 32))
    (hn64 : l.length < 2 ^ 64)
    (hF : revIters 0 l.length + 1 ≤ F)
    (_h : oracleNoalias vecReverseFunc [.stdVecVal l]) :
    memEvalProgFunc vecReverseProg F vecReverseFunc [.stdVecVal l] =
      evalProgFunc vecReverseProg F vecReverseFunc [.stdVecVal l] := by
  rw [memEvalProgFunc_vecReverse F l hn64 hF,
    evalProgFunc_vecReverse F l hn64 hF]
