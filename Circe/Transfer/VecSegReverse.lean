/-
Circe.Transfer.VecSegReverse — S3 transfer for `std::vector<int32_t>`
in-place segment reverse (countdown two-pointer swaps over `[lo, hi)`).

Mirrors `evalProgFunc_vecSegReverse` step for step on the memory layer:
the checked-`at()` callees communicate by value (caller `Mem`/`Layout`
thread through unchanged), the two `vecSet` stores thread through
`memStore` in lockstep (the `+ 1` skips the reified length word), and
the loop re-inducts over `(ρ, m, π)` with the find-characterized memory
invariant (`memFind m 0` pins the `(1 + n)`-word snapshot; stores
prepend shadowing blocks, so the invariant is by-find, never
by-equality). The length word is `l.length` throughout (no `size`
call, no `n` parameter — the S2 `SegInv` generalization).
-/
import Circe.Transfer.Slice
import Circe.Transfer.VecReverse
import Circe.Emit.VecSegReverse

/-! ## Memory body -/

/-- One body iteration on memory: the env threads exactly as on the
    value side while the two stores prepend shadowing snapshot blocks
    (layout stays pinned; the length word is never touched). -/
theorem segMemBody_hit (prog : Prog) (F : Nat) (ρ : Env) (m : Mem)
    (π : Layout)
    (orig l : List (BitVec 32)) (lo hiW i j : Nat)
    (iB jB : BitVec 64) (a b : BitVec 32)
    (hinv : SegInv orig l lo hiW i j)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (hlt : i < j)
    (ha : l[i]? = some a) (hb : l[j - 1]? = some b)
    (hlen64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hlay : layoutLookup π "v" = some (0, 0))
    (hmem : memFind m 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)
    (hfind : findFunc prog stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName }) :
    ∃ ρ' m', memEvalProgStmt prog F vecReverseBody ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal ((l.set i b).set (j - 1) a)) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      envLookup ρ' "j" = some (.u64 (jB - 1)) ∧
      memFind m' 0 = some ⟨0, true, (BitVec.ofNat 32 l.length) ::
        ((l.set i b).set (j - 1) a)⟩ ∧
      SegInv orig ((l.set i b).set (j - 1) a) lo hiW (i + 1)
        (j - 1) := by
  obtain ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid,
    houtL, houtR⟩ := hinv
  have hL0 : ((BitVec.ofNat 32 l.length) :: l).length =
      l.length + 1 := rfl
  have hL1 : ((BitVec.ofNat 32 l.length) :: l.set i b).length =
      (l.set i b).length + 1 := rfl
  have hlenS : (l.set i b).length = l.length := List.length_set
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
  have hstep_j := memRevAssign prog F "j"
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
  have hstep_a := memEvalProgStmt_callRet_ok prog F "a"
    stdVecAtMutName ["v", "i"] ρ₁ m π [.stdVecVal l, .u64 iB]
    { stdVecAtFunc with name := stdVecAtMutName } (.i32 a)
    hargs_a hfind hcall_a
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
  have hstep_b := memEvalProgStmt_callRet_ok prog F "b"
    stdVecAtMutName ["v", "j"] (envExtend ρ₁ "a" (.i32 a)) m π
    [.stdVecVal l, .u64 (jB - 1)]
    { stdVecAtFunc with name := stdVecAtMutName } (.i32 b)
    hargs_b hfind hcall_b
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
  have hlt_s1 : iB.toNat + 1 <
      ((BitVec.ofNat 32 l.length) :: l).length := by
    omega
  have hmstore₁ := revMemStore_ok m ((BitVec.ofNat 32 l.length) :: l)
    (iB.toNat + 1) b hmem hlt_s1
  have hwords₁ : ((BitVec.ofNat 32 l.length) :: l).set (iB.toNat + 1) b =
      (BitVec.ofNat 32 l.length) :: l.set i b := by
    rw [show iB.toNat + 1 = i + 1 from by omega]
    exact List.set_cons_succ
  have hstep_s1 := memRevVecSet prog F "v" (.var "i")
    (.var "b")
    (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b)) m π
    iB b 0 0 l a
    ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
      (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ ρ₄
    mvexpr_i mvexpr_b hv₃ hlay hai hmstore₁ hu₄
  have hmem₁ : memFind ⟨m.next, (0, ⟨0, true,
      ((BitVec.ofNat 32 l.length) :: l).set (iB.toNat + 1) b⟩) ::
      m.blocks, m.blocks64⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l.set i b⟩ := by
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
      ((BitVec.ofNat 32 l.length) :: l.set i b).length := by omega
  have hcur : (l.set iB.toNat b)[(jB - 1).toNat]? =
      some ((l.set iB.toNat b)[(jB - 1).toNat]) := by
    have hjL1 : (jB - 1).toNat < (l.set iB.toNat b).length := by omega
    exact List.getElem?_eq_getElem hjL1
  obtain ⟨ρ₅, hu₅⟩ := envUpdate_some_of_lookup ρ₄ "v"
    (.stdVecVal (l.set iB.toNat b))
    (.stdVecVal ((l.set iB.toNat b).set (jB - 1).toNat a)) hv₄
  have mvexpr_j : memEvalExpr (.var "j") ρ₄
      ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
        (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ π =
      .ok (.u64 (jB - 1)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ hj₄
  have mvexpr_a : memEvalExpr (.var "a") ρ₄
      ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
        (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ π =
      .ok (.i32 a) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ ha₄
  have hmstore₂ := revMemStore_ok
    ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
      (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩
    ((BitVec.ofNat 32 l.length) :: l.set i b) ((jB - 1).toNat + 1) a
    hmem₁ (by omega)
  have hwords₂ : ((BitVec.ofNat 32 l.length) :: l.set i b).set
      ((jB - 1).toNat + 1) a =
      (BitVec.ofNat 32 l.length) :: (l.set i b).set (j - 1) a := by
    rw [show (jB - 1).toNat + 1 = (j - 1) + 1 from by omega]
    exact List.set_cons_succ
  have hstep_s2 := memRevVecSet prog F "v" (.var "j")
    (.var "a")
    ρ₄ ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
      (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ π
    (jB - 1) a 0 0 (l.set iB.toNat b)
    ((l.set iB.toNat b)[(jB - 1).toNat])
    ⟨m.next, (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l.set i b).set
      ((jB - 1).toNat + 1) a⟩) ::
      (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
        (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ ρ₅
    mvexpr_j mvexpr_a hv₄ hlay hcur hmstore₂ hu₅
  have hmem₂ : memFind ⟨m.next, (0, ⟨0, true,
      ((BitVec.ofNat 32 l.length) :: l.set i b).set
        ((jB - 1).toNat + 1) a⟩) ::
      (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
        (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) ::
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
      ⟨m.next, (0, ⟨0, true,
        ((BitVec.ofNat 32 l.length) :: l.set i b).set
          ((jB - 1).toNat + 1) a⟩) ::
        (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
          (iB.toNat + 1) b⟩) :: m.blocks, m.blocks64⟩ π =
      .ok (.u64 (iB + 1)) := by
    rw [memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)]
    exact vexpr_i
  obtain ⟨ρ₆, hu₆⟩ := envUpdate_some_of_lookup ρ₅ "i" (.u64 iB)
    (.u64 (iB + 1)) hi₅
  have hstep_i := memRevAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₅
    ⟨m.next, (0, ⟨0, true,
      ((BitVec.ofNat 32 l.length) :: l.set i b).set
        ((jB - 1).toNat + 1) a⟩) ::
      (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
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
  have heval : memEvalProgStmt prog F vecReverseBody ρ m π =
      .ok ((ρ₆, ⟨m.next, (0, ⟨0, true,
        ((BitVec.ofNat 32 l.length) :: l.set i b).set
          ((jB - 1).toNat + 1) a⟩) ::
        (0, ⟨0, true, ((BitVec.ofNat 32 l.length) :: l).set
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
  have hstep := SegInv_step orig l lo hiW i j a b
    ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid, houtL,
      houtR⟩ hlt ha hb
  refine ⟨ρ₆, _, heval, ?_, ?_, ?_, ?_, ?_⟩
  · exact hfinal ▸ hv₆
  · exact hi₆
  · exact hj₆
  · exact hfinal ▸ hmem₂
  · exact hfinal ▸ hstep

/-! ## Memory loop -/

/-- The countdown loop on memory evaluates to the window-reversed
    words (fuel induction against `revIters`, mirroring
    `segWhile_ok`; the memory invariant threads the shadowing
    snapshots alongside). -/
theorem segMemWhile_ok (prog : Prog) (F : Nat) (ρ : Env) (m : Mem)
    (π : Layout)
    (orig l : List (BitVec 32)) (lo hiW i j : Nat)
    (iB jB : BitVec 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB)) (hiN : iB.toNat = i)
    (hj : envLookup ρ "j" = some (.u64 jB)) (hjN : jB.toNat = j)
    (hinv : SegInv orig l lo hiW i j)
    (hlen64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "v" = some (0, 0))
    (hmem : memFind m 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)
    (hF : revIters i j + 1 ≤ F)
    (hfind : findFunc prog stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName }) :
    ∃ ρ' m', memEvalProgStmt prog F vecReverseWhile ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal (segReverseWindow orig lo hiW)) := by
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
      obtain ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid,
        houtL, houtR⟩ := hinv
      have hiL : i < l.length := by omega
      have hjL : j - 1 < l.length := by omega
      obtain ⟨ρ₆, m₆, heval, hv₆, hi₆, hj₆, hmem₆, hinv₆⟩ :=
        segMemBody_hit prog F ρ m π orig l lo hiW i j iB jB l[i] l[j - 1]
          ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid, houtL,
            houtR⟩
          hiN hjN h
          (List.getElem?_eq_getElem hiL)
          (List.getElem?_eq_getElem hjL)
          hlen64 hv hi hj hlay hmem hfind
      have hR : revIters i j = revIters (i + 1) (j - 1) + 1 :=
        (revIters_step i j h).symm
      have hF' : revIters (i + 1) (j - 1) + 1 ≤ F := by omega
      have hiN₆ : (iB + 1).toNat = i + 1 := by
        rw [revU64_succ_toNat iB l.length (by omega) hlen64, hiN]
      have hjN₆ : (jB - 1).toNat = j - 1 := by
        rw [revU64_pred_toNat jB (by omega), hjN]
      have hlen64' :
          ((l.set i l[j - 1]).set (j - 1) l[i]).length < 2 ^ 64 := by
        rw [List.length_set, List.length_set]
        exact hlen64
      have hlenU : ((l.set i l[j - 1]).set (j - 1) l[i]).length =
          l.length := by
        rw [List.length_set, List.length_set]
      have hmem₆' : memFind m₆ 0 = some ⟨0, true,
          (BitVec.ofNat 32
            (((l.set i l[j - 1]).set (j - 1) l[i]).length)) ::
            ((l.set i l[j - 1]).set (j - 1) l[i])⟩ := by
        rw [hlenU]; exact hmem₆
      obtain ⟨ρ', m', hloop, hv'⟩ :=
        ih ρ₆ m₆ π ((l.set i l[j - 1]).set (j - 1) l[i])
          (i + 1) (j - 1) (iB + 1) (jB - 1)
          hv₆ hi₆ hiN₆ hj₆ hjN₆ hinv₆ hlen64' hlay hmem₆' hF'
      refine ⟨ρ', m', ?_, hv'⟩
      have hwhile : memEvalProgStmt prog (F + 1)
          vecReverseWhile ρ m π =
          memEvalProgStmt prog F vecReverseWhile ρ₆ m₆ π := by
        cir_unfold_prog (vecReverseWhile, prog, F, hguard, heval)
      rw [hwhile]
      exact hloop
    · -- Exit: guard false, state exits; the value invariant (threaded
      -- alongside) closes to the window.
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
      have hexit : memEvalProgStmt prog (F + 1)
          vecReverseWhile ρ m π =
          .ok ((ρ, m, π), .fellThrough) := by
        simp only [vecReverseWhile,
          memEvalProgStmt_while_false prog _ _ _ _ _ _
            hguard]
      have hwin : l = segReverseWindow orig lo hiW :=
        SegInv_exit orig l lo hiW i j hinv (by omega)
      have hvwin : envLookup ρ "v" =
          some (.stdVecVal (segReverseWindow orig lo hiW)) := by
        rw [← hwin]; exact hv
      exact ⟨ρ, m, hexit, hvwin⟩

/-! ## Entry bridge (`memEval` + transfer) -/

/-- `memEval` for `vec_seg_reverse`: program evaluation over the
    frozen checked-`at()` leaves agrees with window reversal on
    memory (mirrors `evalProgFunc_vecSegReverse`; the owned `u64`
    bounds bind by value, stores lockstep through `memStore`). -/
theorem segMemEvalProgFunc (prog : Prog) (F : Nat)
    (l : List (BitVec 32))
    (lo hi : Nat) (loB hiB : BitVec 64)
    (hloB : loB.toNat = lo) (hhiB : hiB.toNat = hi)
    (hlo : lo ≤ hi) (hhi : hi ≤ l.length)
    (hlen64 : l.length < 2 ^ 64)
    (hF : revIters lo hi + 1 ≤ F)
    (hfind : findFunc prog stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName }) :
    memEvalProgFunc prog F vecSegReverseFunc
      [.stdVecVal l, .u64 loB, .u64 hiB] =
      vecSegReverseFwd l loB hiB := by
  have hb : bindMemArgs vecSegReverseFunc.args
      [.stdVecVal l, .u64 loB, .u64 hiB] emptyMem =
      some ([("v", .stdVecVal l), ("lo", .u64 loB),
        ("hi", .u64 hiB)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) :=
    bindMemArgs_vecSegReverse l loB hiB
  have hbind := hb
  have hbody : vecSegReverseFunc.body =
      (.seq (.let_ "i" (.u 64) (.var "lo"))
        (.seq (.let_ "j" (.u 64) (.var "hi"))
          (.seq vecReverseWhile
            (.return_ (.var "v"))))) := rfl
  have hlay₀ : layoutLookup [("v", 0, 0)] "v" = some (0, 0) := by
    simp [layoutLookup]
  have hmem₀ : memFind ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  -- `i ← lo`, `j ← hi` (pure copies, memory untouched).
  have hlo₀ : envLookup [("v", .stdVecVal l), ("lo", .u64 loB),
      ("hi", .u64 hiB)] "lo" = some (.u64 loB) := by
    simp [envLookup]
  have hstep_i := memRevLet prog F "i" (.u 64) (.var "lo")
    [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
    (.u64 loB)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (memEvalExpr_var _ _ _ _)
    (evalExpr_var_hit _ _ _ hlo₀)
  have hi₁ : envLookup (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
      ("hi", .u64 hiB)] "i" (.u64 loB)) "i" = some (.u64 loB) :=
    envExtend_hit _ _ _
  have hhi₀ : envLookup (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
      ("hi", .u64 hiB)] "i" (.u64 loB)) "hi" =
      some (.u64 hiB) := by
    rw [envExtend_miss _ _ _ _
      (show ("hi" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hstep_j := memRevLet prog F "j" (.u 64) (.var "hi")
    (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
      ("hi", .u64 hiB)] "i" (.u64 loB))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
    (.u64 hiB)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (memEvalExpr_var _ _ _ _)
    (evalExpr_var_hit _ _ _ hhi₀)
  have hj₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("lo", .u64 loB), ("hi", .u64 hiB)] "i" (.u64 loB)) "j"
      (.u64 hiB)) "j" = some (.u64 hiB) :=
    envExtend_hit _ _ _
  have hv₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("lo", .u64 loB), ("hi", .u64 hiB)] "i" (.u64 loB)) "j"
      (.u64 hiB)) "v" = some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "j" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("lo", .u64 loB), ("hi", .u64 hiB)] "i" (.u64 loB)) "j"
      (.u64 hiB)) "i" = some (.u64 loB) :=
    envLookup_extend_miss _ _ _ _ _ hi₁ (by decide)
  -- Loop from `(lo, hi)`.
  have hinv₀ : SegInv l l lo hi lo hi :=
    ⟨rfl, hlo, hhi, Nat.le_refl _, Nat.le_refl _, rfl,
      fun p _ hp => absurd hp (by omega),
      fun p hp hlt => absurd hlt (by omega),
      fun p _ _ => rfl,
      fun p _ => rfl,
      fun p _ _ => rfl⟩
  obtain ⟨ρ', m', hloop, hv'⟩ :=
    segMemWhile_ok prog F (envExtend (envExtend [("v", .stdVecVal l),
      ("lo", .u64 loB), ("hi", .u64 hiB)] "i" (.u64 loB)) "j"
      (.u64 hiB))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
      l l lo hi lo hi loB hiB
      hv₂ hi₂ hloB hj₂ hhiB hinv₀ hlen64 hlay₀ hmem₀ hF hfind
  -- `return v`.
  have hretV : memEvalExpr (.var "v") ρ' m' [("v", 0, 0)] =
      evalExpr (.var "v") ρ' := memEvalExpr_var _ _ _ _
  have hret := memEvalProgStmt_return prog F (.var "v") ρ'
    m' [("v", 0, 0)] (.stdVecVal (segReverseWindow l lo hi))
    (by rw [hretV]; exact evalExpr_var_hit _ _ _ hv')
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_i,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_j,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
    hret]
  simp only [vecSegReverseFwd]
  rw [hloB, hhiB, if_pos ⟨hlo, hhi⟩]

/-- Transfer for `vec_seg_reverse` (program level). -/
theorem segMemTransferProg (prog : Prog) (F : Nat)
    (l : List (BitVec 32))
    (lo hi : Nat) (loB hiB : BitVec 64)
    (hloB : loB.toNat = lo) (hhiB : hiB.toNat = hi)
    (hlo : lo ≤ hi) (hhi : hi ≤ l.length)
    (hlen64 : l.length < 2 ^ 64)
    (hF : revIters lo hi + 1 ≤ F)
    (_h : oracleNoalias vecSegReverseFunc
      [.stdVecVal l, .u64 loB, .u64 hiB])
    (hfind : findFunc prog stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName }) :
    memEvalProgFunc prog F vecSegReverseFunc
      [.stdVecVal l, .u64 loB, .u64 hiB] =
      evalProgFunc prog F vecSegReverseFunc
        [.stdVecVal l, .u64 loB, .u64 hiB] := by
  rw [segMemEvalProgFunc prog F l lo hi loB hiB hloB hhiB hlo hhi hlen64
      hF hfind,
    evalProgFunc_vecSegReverse prog F l lo hi loB hiB hloB hhiB hlo hhi
      hlen64 hF hfind]
