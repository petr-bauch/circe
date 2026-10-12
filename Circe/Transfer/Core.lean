/-
Circe.Transfer.Core — `sum_array` transfer and whole-function
correctness; the remaining transfers live in `VecLeaves` /
`VecHeap` / `Flow` / `Slice` / `Acc` / `GrowLeaves` / `GrowReloc` /
`GrowRealloc` / `GrowEmplace` / `GrowEntry`.
-/
import Circe.Mem
import Circe.Derived
import Circe.Emit.Sum
import Circe.Emit.SumTwo
import Circe.Emit.Vec
import Circe.Emit.Add
import Circe.Emit.Choose
import Circe.Emit.Struct
import Circe.Emit.Flow
import Circe.Emit.Calls
import Circe.Emit.Vec2
import Circe.Emit.VecRealloc
import Circe.Emit.Vec64
import Circe.Emit.Method
import Circe.Emit.Acc
import Circe.Emit.Move
import Circe.Emit.Box

/-! ## `sum_array` transfer -/

/-- `sum` binding: the array lifts into a fresh block holding its words
    (tag creation at bind); the bound is scalar. -/
theorem bindMemArgs_sum (l : List (BitVec 32)) (nv : BitVec 32) :
    bindMemArgs
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned }]
      [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
  rfl

/-- `sum` entry footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_sum (l : List (BitVec 32)) (nv : BitVec 32) :
    oracleNoalias sumFunc [.arr32 l, .u32 nv] := by
  have hb : bindMemArgs sumFunc.args [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
    show bindMemArgs
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned }]
      [.arr32 l, .u32 nv] emptyMem = _
    exact bindMemArgs_sum l nv
  have hn : LayoutNoAlias [("a", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- One memory body step advances index and accumulator (any fuel:
    loop-free), with `Mem`/`Layout` untouched (reads only). -/
theorem memSumBody_eval (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hklen : k < l.length) (hk32 : k < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalStmtFuel F sumBody (mkSumEnv l nv k acc) m π =
      .ok (((mkSumEnv l nv (k + 1) (acc + l[k]), m, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hklen
  have ha := mkSumEnv_a l nv k acc
  have hii : envLookup (mkSumEnv l nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := mkSumEnv_i l nv k acc
  have hload : memLoad m 0 0 (BitVec.ofNat 32 k).toNat = .ok l[k] := by
    rw [hkk]
    exact memLoad_hit m 0 0 k ⟨0, true, l⟩ l[k] hmem rfl rfl hget
  have hget' : l[(BitVec.ofNat 32 k).toNat]? = some l[k] := by
    rw [hkk]; exact hget
  have hs : memEvalExpr (.uadd (.var "s") (.idx "a" (.var "i")))
        (mkSumEnv l nv k acc) m π = .ok (.u32 (acc + l[k])) := by
    have h1 := mkSumEnv_s l nv k acc
    simp only [memEvalExpr, h1, hlay, ha, hii,
      hload, hget', beq_self_eq_true, ↓reduceIte]
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkSumEnv l nv k (acc + l[k])) m π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSumEnv_i l nv k (acc + l[k])
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up1 := sumEnv_update_s l nv k acc (acc + l[k])
  have up2 := sumEnv_update_i l nv k (k + 1) (acc + l[k])
  cases F <;>
    simp only [sumBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hs, hi2, up1, up2]

/-- The memory OOB step: at `k = length` the memory read fails loudly
    too (block data = value words, so bounds fail on both sides). -/
theorem memSumBody_oob (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (acc : BitVec 32) (m : Mem) (π : Layout)
    (h32 : l.length < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalStmtFuel F sumBody (mkSumEnv l nv l.length acc) m π =
      .error .OOB := by
  have hkk : (BitVec.ofNat 32 l.length).toNat = l.length :=
    ofNat32_toNat _ h32
  have hget : l[l.length]? = none :=
    List.getElem?_eq_none (Nat.le_refl _)
  have ha := mkSumEnv_a l nv l.length acc
  have hii : envLookup (mkSumEnv l nv l.length acc) "i" =
      some (.u32 (BitVec.ofNat 32 l.length)) :=
    mkSumEnv_i l nv l.length acc
  have hload : memLoad m 0 0 (BitVec.ofNat 32 l.length).toNat =
      .error .OOB := by
    rw [hkk]
    simp [memLoad, hmem]
  have hs : memEvalExpr (.uadd (.var "s") (.idx "a" (.var "i")))
        (mkSumEnv l nv l.length acc) m π = .error .OOB := by
    have h1 := mkSumEnv_s l nv l.length acc
    have hget' : l[(BitVec.ofNat 32 l.length).toNat]? = none := by
      rw [hkk]; exact hget
    simp only [memEvalExpr, h1, hlay, ha, hii, hload, hget']
  cases F <;>
    simp [sumBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hs]

/-- The memory loop condition reads the index against the bound
    (memory untouched — the condition is pure). -/
theorem memSumCond_eval (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n")) (mkSumEnv l nv k acc) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSumEnv_i l nv k acc
  have hn := mkSumEnv_n l nv k acc
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- Memory loop correctness, in-range: the memory loop folds the
    remaining suffix, leaving `Mem`/`Layout` untouched. -/
theorem memSumWhile_correct (l : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hlen : nv.toNat ≤ l.length)
    (h32 : nv.toNat < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩)
    (hF : nv.toNat - k ≤ F) :
    memEvalStmtFuel F sumWhile (mkSumEnv l nv k acc) m π =
      .ok (((mkSumEnv l nv nv.toNat
        (acc + prefixSumU32 (l.drop k) (nv.toNat - k)), m, π)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
        (mkSumEnv l nv nv.toNat acc) m π = .ok (.b false) := by
      simpa using (memSumCond_eval l nv nv.toNat acc m π h32)
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    have hpre : prefixSumU32 (l.drop nv.toNat) 0 = 0 := prefixSumU32_zero _
    simp [sumWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith, hcond, hsub, hpre]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < l.length := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv k acc) m π = .ok (.b true) := by
        simpa [hlt] using (memSumCond_eval l nv k acc m π hk32)
      have hbody := memSumBody_eval F l nv k acc m π hklen hk32 hlay hmem
      have hstep : memEvalStmtFuel (F + 1) sumWhile (mkSumEnv l nv k acc)
            m π
          = memEvalStmtFuel F sumWhile (mkSumEnv l nv (k + 1) (acc + l[k]))
            m π := by
        simp [sumWhile, memEvalStmtFuel, memEvalSuccHandler, memEvalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hrec := ih (k + 1) (acc + l[k]) (by omega) (by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hdrop : l.drop k = l[k] :: l.drop (k + 1) :=
        drop_cons_getElem l k hklen
      have hacc : (acc + l[k]) +
            prefixSumU32 (l.drop (k + 1)) (nv.toNat - (k + 1))
          = acc + prefixSumU32 (l.drop k) (nv.toNat - k) := by
        rw [hkk1, hdrop, prefixSumU32_cons]
        exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv nv.toNat acc) m π = .ok (.b false) := by
        simpa using (memSumCond_eval l nv nv.toNat acc m π h32)
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      have hpre : prefixSumU32 (l.drop nv.toNat) 0 = 0 := prefixSumU32_zero _
      simp [sumWhile, memEvalStmtFuel, memEvalSuccHandler, memEvalStmtWith,
        hcond, hsub, hpre]

/-- Memory loop correctness, out-of-range: the memory loop reports
    `OOB` at the end (same path as `Eval`). -/
theorem memSumWhile_oob (l : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hk : k ≤ l.length)
    (hlt : l.length < nv.toNat)
    (hlen32 : l.length < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩)
    (hF : l.length - k + 1 ≤ F) :
    memEvalStmtFuel F sumWhile (mkSumEnv l nv k acc) m π =
      .error .OOB := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt2 : k < l.length
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv k acc) m π = .ok (.b true) := by
        have hkn : k < nv.toNat := by omega
        simpa [hkn] using (memSumCond_eval l nv k acc m π hk32)
      have hbody := memSumBody_eval F l nv k acc m π hlt2 hk32 hlay hmem
      have hstep : memEvalStmtFuel (F + 1) sumWhile (mkSumEnv l nv k acc)
            m π
          = memEvalStmtFuel F sumWhile (mkSumEnv l nv (k + 1) (acc + l[k]))
            m π := by
        simp [sumWhile, memEvalStmtFuel, memEvalSuccHandler, memEvalStmtWith,
          hcond, hbody]
      rw [hstep]
      exact ih (k + 1) (acc + l[k]) (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv l.length acc) m π = .ok (.b true) := by
        simpa [hlt] using
          (memSumCond_eval l nv l.length acc m π hlen32)
      have hbody := memSumBody_oob F l nv acc m π hlen32 hlay hmem
      simp [sumWhile, memEvalStmtFuel, memEvalSuccHandler, memEvalStmtWith,
        hcond, hbody]

/-! ### Whole-function correctness (fuel-generalized, then transfer) -/

/-- `memEval` for `sum` at any fuel covering `n` (mirrors
    `evalFuncFuel_sum`; memory rides alongside, untouched). -/
theorem memEvalFuncFuel_sum (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    memEvalFuncFuel F sumFunc [.arr32 l, .u32 nv] = sumFwd l nv := by
  have hb := bindMemArgs_sum l nv
  have hlay : layoutLookup [("a", 0, 0)] "a" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memFind ⟨1, [(0, ⟨0, true, l⟩)], []⟩ 0 =
      some ⟨0, true, l⟩ := by
    simp [memFind]
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l), ("n", .u32 nv)]
      = mkSumEnv l nv 0 (BitVec.ofNat 32 0) := rfl
  have hret := mkSumEnv_s l nv nv.toNat (prefixSumU32 l nv.toNat)
  cases F with
  | zero =>
    have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
          ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)]
        = .ok (((mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)])),
            .fellThrough) :=
      memSumWhile_correct l nv 0 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hle h32 hlay hmem (by cir_fuel)
    simp [memEvalFuncFuel, sumFunc, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal,
      sumFwd, hb, henv, hloopH0, hret, hle]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
          ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)]
        = .ok (((mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)])),
            .fellThrough) :=
      memSumWhile_correct l nv (F + 1) 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hle h32 hlay hmem (by cir_fuel)
    simp [memEvalFuncFuel, sumFunc, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, sumFwd, hb, henv,
      hloopS, hret, hle]

/-- OOB corollary at any fuel (mirrors `evalFuncFuel_sum_oob`). -/
theorem memEvalFuncFuel_sum_oob (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hlt : l.length < nv.toNat) (hlen32 : l.length < 2 ^ 32)
    (hF : l.length + 1 ≤ F) :
    memEvalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .error .OOB := by
  have hb := bindMemArgs_sum l nv
  have hlay : layoutLookup [("a", 0, 0)] "a" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memFind ⟨1, [(0, ⟨0, true, l⟩)], []⟩ 0 =
      some ⟨0, true, l⟩ := by
    simp [memFind]
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l), ("n", .u32 nv)]
      = mkSumEnv l nv 0 (BitVec.ofNat 32 0) := rfl
  cases F with
  | zero =>
    have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
          ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] = .error .OOB :=
      memSumWhile_oob l nv 0 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hlt hlen32 hlay hmem (by cir_fuel)
    simp [memEvalFuncFuel, sumFunc, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal,
      henv, hb, hloopH0]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
          ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] = .error .OOB :=
      memSumWhile_oob l nv (F + 1) 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hlt hlen32 hlay hmem (by cir_fuel)
    simp [memEvalFuncFuel, sumFunc, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, henv, hb, hloopS]

/-- Transfer for `sum` (in-range): both sides equal `sumFwd`. -/
theorem memTransfer_sum (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F)
    (_h : oracleNoalias sumFunc [.arr32 l, .u32 nv]) :
    memEvalFuncFuel F sumFunc [.arr32 l, .u32 nv] =
      evalFuncFuel F sumFunc [.arr32 l, .u32 nv] := by
  rw [memEvalFuncFuel_sum F l nv hle h32 hF,
    evalFuncFuel_sum F l nv hle h32 hF]

/-- Transfer for `sum` (OOB): both sides fail loudly. -/
theorem memTransfer_sum_oob (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hlt : l.length < nv.toNat) (hlen32 : l.length < 2 ^ 32)
    (hF : l.length + 1 ≤ F)
    (_h : oracleNoalias sumFunc [.arr32 l, .u32 nv]) :
    memEvalFuncFuel F sumFunc [.arr32 l, .u32 nv] =
      evalFuncFuel F sumFunc [.arr32 l, .u32 nv] := by
  rw [memEvalFuncFuel_sum_oob F l nv hlt hlen32 hF,
    evalFuncFuel_sum_oob F l nv hlt hlen32 hF]

/-! ## `sum_two` transfer (two readers, N2a discipline) -/

/-- One memory body step advances index and accumulator (any fuel:
    loop-free), with `Mem`/`Layout` untouched (reads only). -/
theorem memSumTwoBody_eval (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32) (k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hklen₁ : k < l₁.length) (hklen₂ : k < l₂.length)
    (hk32 : k < 2 ^ 32)
    (hlayA : layoutLookup π "a" = some (1, 1))
    (hlayB : layoutLookup π "b" = some (0, 0))
    (hmemA : memFind m 1 = some ⟨1, true, l₁⟩)
    (hmemB : memFind m 0 = some ⟨0, true, l₂⟩) :
    memEvalStmtFuel F sumTwoBody (mkSumTwoEnv l₁ l₂ nv k acc) m π =
      .ok (((mkSumTwoEnv l₁ l₂ nv (k + 1) (acc + (l₁[k] + l₂[k])), m, π)),
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hget₁ : l₁[k]? = some l₁[k] := List.getElem?_eq_getElem hklen₁
  have hget₂ : l₂[k]? = some l₂[k] := List.getElem?_eq_getElem hklen₂
  have ha := mkSumTwoEnv_a l₁ l₂ nv k acc
  have hb := mkSumTwoEnv_b l₁ l₂ nv k acc
  have hii : envLookup (mkSumTwoEnv l₁ l₂ nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := mkSumTwoEnv_i l₁ l₂ nv k acc
  have hloadA : memLoad m 1 1 (BitVec.ofNat 32 k).toNat = .ok l₁[k] := by
    rw [hkk]
    exact memLoad_hit m 1 1 k ⟨1, true, l₁⟩ l₁[k] hmemA rfl rfl hget₁
  have hloadB : memLoad m 0 0 (BitVec.ofNat 32 k).toNat = .ok l₂[k] := by
    rw [hkk]
    exact memLoad_hit m 0 0 k ⟨0, true, l₂⟩ l₂[k] hmemB rfl rfl hget₂
  have hgetA' : l₁[(BitVec.ofNat 32 k).toNat]? = some l₁[k] := by
    rw [hkk]; exact hget₁
  have hgetB' : l₂[(BitVec.ofNat 32 k).toNat]? = some l₂[k] := by
    rw [hkk]; exact hget₂
  have hs : memEvalExpr (.uadd (.var "s")
        (.uadd (.idx "a" (.var "i")) (.idx "b" (.var "i"))))
        (mkSumTwoEnv l₁ l₂ nv k acc) m π =
        .ok (.u32 (acc + (l₁[k] + l₂[k]))) := by
    have h1 := mkSumTwoEnv_s l₁ l₂ nv k acc
    simp only [memEvalExpr, h1, hlayA, hlayB, ha, hb, hii,
      hloadA, hloadB, hgetA', hgetB', beq_self_eq_true, ↓reduceIte]
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkSumTwoEnv l₁ l₂ nv k (acc + (l₁[k] + l₂[k]))) m π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSumTwoEnv_i l₁ l₂ nv k (acc + (l₁[k] + l₂[k]))
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up1 := sumTwoEnv_update_s l₁ l₂ nv k acc (acc + (l₁[k] + l₂[k]))
  have up2 := sumTwoEnv_update_i l₁ l₂ nv k (k + 1) (acc + (l₁[k] + l₂[k]))
  cases F <;>
    simp only [sumTwoBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hs, hi2, up1, up2]

/-- The memory OOB step on the first array: block data = value
    words, so bounds fail on both sides (first error wins). -/
theorem memSumTwoBody_oob_a (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32) (k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hk32 : k < 2 ^ 32)
    (hlayA : layoutLookup π "a" = some (1, 1))
    (hlayB : layoutLookup π "b" = some (0, 0))
    (hmemA : memFind m 1 = some ⟨1, true, l₁⟩)
    (hget₁ : l₁[k]? = none) :
    memEvalStmtFuel F sumTwoBody
        (mkSumTwoEnv l₁ l₂ nv k acc) m π =
      .error .OOB := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have ha := mkSumTwoEnv_a l₁ l₂ nv k acc
  have hb := mkSumTwoEnv_b l₁ l₂ nv k acc
  have hii : envLookup (mkSumTwoEnv l₁ l₂ nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := mkSumTwoEnv_i l₁ l₂ nv k acc
  have hgetA' : l₁[(BitVec.ofNat 32 k).toNat]? = none := by
    rw [hkk]; exact hget₁
  have hloadA : memLoad m 1 1 (BitVec.ofNat 32 k).toNat = .error .OOB := by
    rw [hkk]
    simp [memLoad, hmemA, hget₁]
  have hs : memEvalExpr (.uadd (.var "s")
        (.uadd (.idx "a" (.var "i")) (.idx "b" (.var "i"))))
        (mkSumTwoEnv l₁ l₂ nv k acc) m π = .error .OOB := by
    have h1 := mkSumTwoEnv_s l₁ l₂ nv k acc
    simp only [memEvalExpr, h1, hlayA, hlayB, ha, hb, hii,
      hloadA, hgetA']
  cases F <;>
    simp [sumTwoBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hs]

/-- The memory OOB step on the second array (`a[i]` loads fine, the
    `b[i]` load fails loudly). -/
theorem memSumTwoBody_oob_b (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32) (k : Nat) (acc x : BitVec 32) (m : Mem) (π : Layout)
    (hk32 : k < 2 ^ 32)
    (hlayA : layoutLookup π "a" = some (1, 1))
    (hlayB : layoutLookup π "b" = some (0, 0))
    (hmemA : memFind m 1 = some ⟨1, true, l₁⟩)
    (hmemB : memFind m 0 = some ⟨0, true, l₂⟩)
    (hget₁ : l₁[k]? = some x) (hget₂ : l₂[k]? = none) :
    memEvalStmtFuel F sumTwoBody
        (mkSumTwoEnv l₁ l₂ nv k acc) m π =
      .error .OOB := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have ha := mkSumTwoEnv_a l₁ l₂ nv k acc
  have hb := mkSumTwoEnv_b l₁ l₂ nv k acc
  have hii : envLookup (mkSumTwoEnv l₁ l₂ nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := mkSumTwoEnv_i l₁ l₂ nv k acc
  have hgetA' : l₁[(BitVec.ofNat 32 k).toNat]? = some x := by
    rw [hkk]; exact hget₁
  have hgetB' : l₂[(BitVec.ofNat 32 k).toNat]? = none := by
    rw [hkk]; exact hget₂
  have hloadA : memLoad m 1 1 (BitVec.ofNat 32 k).toNat = .ok x := by
    rw [hkk]
    exact memLoad_hit m 1 1 k ⟨1, true, l₁⟩ x hmemA rfl rfl hget₁
  have hloadB : memLoad m 0 0 (BitVec.ofNat 32 k).toNat = .error .OOB := by
    rw [hkk]
    simp [memLoad, hmemB, hget₂]
  have hs : memEvalExpr (.uadd (.var "s")
        (.uadd (.idx "a" (.var "i")) (.idx "b" (.var "i"))))
        (mkSumTwoEnv l₁ l₂ nv k acc) m π = .error .OOB := by
    have h1 := mkSumTwoEnv_s l₁ l₂ nv k acc
    simp only [memEvalExpr, h1, hlayA, hlayB, ha, hb, hii,
      hloadA, hloadB, hgetA', hgetB', beq_self_eq_true, ↓reduceIte]
  cases F <;>
    simp [sumTwoBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hs]

/-- The memory loop condition reads the index against the bound
    (memory untouched — the condition is pure). -/
theorem memSumTwoCond_eval (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n"))
      (mkSumTwoEnv l₁ l₂ nv k acc) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSumTwoEnv_i l₁ l₂ nv k acc
  have hn := mkSumTwoEnv_n l₁ l₂ nv k acc
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- Memory loop correctness, in-range: the memory loop folds the
    remaining suffix pair, leaving `Mem`/`Layout` untouched. -/
theorem memSumTwoWhile_correct (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hle₁ : nv.toNat ≤ l₁.length) (hle₂ : nv.toNat ≤ l₂.length)
    (h32 : nv.toNat < 2 ^ 32)
    (hlayA : layoutLookup π "a" = some (1, 1))
    (hlayB : layoutLookup π "b" = some (0, 0))
    (hmemA : memFind m 1 = some ⟨1, true, l₁⟩)
    (hmemB : memFind m 0 = some ⟨0, true, l₂⟩)
    (hF : nv.toNat - k ≤ F) :
    memEvalStmtFuel F sumTwoWhile (mkSumTwoEnv l₁ l₂ nv k acc) m π =
      .ok (((mkSumTwoEnv l₁ l₂ nv nv.toNat
        (acc + pairSum (l₁.drop k) (l₂.drop k) (nv.toNat - k)), m, π)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
        (mkSumTwoEnv l₁ l₂ nv nv.toNat acc) m π = .ok (.b false) := by
      simpa using (memSumTwoCond_eval l₁ l₂ nv nv.toNat acc m π h32)
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    have hpre : pairSum (l₁.drop nv.toNat) (l₂.drop nv.toNat) 0 = 0 :=
      pairSum_zero _ _
    simp [sumTwoWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith, hcond, hsub, hpre]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen₁ : k < l₁.length := by omega
      have hklen₂ : k < l₂.length := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkSumTwoEnv l₁ l₂ nv k acc) m π = .ok (.b true) := by
        simpa [hlt] using (memSumTwoCond_eval l₁ l₂ nv k acc m π hk32)
      have hbody := memSumTwoBody_eval F l₁ l₂ nv k acc m π
        hklen₁ hklen₂ hk32 hlayA hlayB hmemA hmemB
      have hstep : memEvalStmtFuel (F + 1) sumTwoWhile
            (mkSumTwoEnv l₁ l₂ nv k acc) m π
          = memEvalStmtFuel F sumTwoWhile
            (mkSumTwoEnv l₁ l₂ nv (k + 1) (acc + (l₁[k] + l₂[k]))) m π := by
        simp [sumTwoWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hrec := ih (k + 1) (acc + (l₁[k] + l₂[k])) (by omega) (by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hdrop := drop_pair_cons_getElem l₁ l₂ k hklen₁ hklen₂
      obtain ⟨hd₁, hd₂⟩ := hdrop
      have hacc : (acc + (l₁[k] + l₂[k])) +
            pairSum (l₁.drop (k + 1)) (l₂.drop (k + 1)) (nv.toNat - (k + 1))
          = acc + pairSum (l₁.drop k) (l₂.drop k) (nv.toNat - k) := by
        rw [hkk1, hd₁, hd₂, pairSum_cons]
        exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkSumTwoEnv l₁ l₂ nv nv.toNat acc) m π = .ok (.b false) := by
        simpa using (memSumTwoCond_eval l₁ l₂ nv nv.toNat acc m π h32)
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      have hpre : pairSum (l₁.drop nv.toNat) (l₂.drop nv.toNat) 0 = 0 :=
        pairSum_zero _ _
      simp [sumTwoWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hsub, hpre]

/-- Memory loop correctness, out-of-range: the memory loop reports
    `OOB` at the first index past the shorter array (same path as
    `Eval`: block data = value words). -/
theorem memSumTwoWhile_oob (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hk : k ≤ min l₁.length l₂.length)
    (hlt : min l₁.length l₂.length < nv.toNat)
    (hmin32 : min l₁.length l₂.length < 2 ^ 32)
    (hlayA : layoutLookup π "a" = some (1, 1))
    (hlayB : layoutLookup π "b" = some (0, 0))
    (hmemA : memFind m 1 = some ⟨1, true, l₁⟩)
    (hmemB : memFind m 0 = some ⟨0, true, l₂⟩)
    (hF : min l₁.length l₂.length - k + 1 ≤ F) :
    memEvalStmtFuel F sumTwoWhile (mkSumTwoEnv l₁ l₂ nv k acc) m π =
      .error .OOB := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    have hkn : k < nv.toNat := by omega
    have hk32 : k < 2 ^ 32 := by omega
    have hklen₁ : k ≤ l₁.length := by omega
    have hklen₂ : k ≤ l₂.length := by omega
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
        (mkSumTwoEnv l₁ l₂ nv k acc) m π = .ok (.b true) := by
      simpa [hkn] using (memSumTwoCond_eval l₁ l₂ nv k acc m π hk32)
    by_cases hboth : k < l₁.length ∧ k < l₂.length
    · obtain ⟨hk₁, hk₂⟩ := hboth
      have hbody := memSumTwoBody_eval F l₁ l₂ nv k acc m π
        hk₁ hk₂ hk32 hlayA hlayB hmemA hmemB
      have hstep : memEvalStmtFuel (F + 1) sumTwoWhile
            (mkSumTwoEnv l₁ l₂ nv k acc) m π
          = memEvalStmtFuel F sumTwoWhile
            (mkSumTwoEnv l₁ l₂ nv (k + 1) (acc + (l₁[k] + l₂[k]))) m π := by
        simp [sumTwoWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      exact ih (k + 1) (acc + (l₁[k] + l₂[k])) (by omega) (by omega)
    · have hbody : memEvalStmtFuel F sumTwoBody
            (mkSumTwoEnv l₁ l₂ nv k acc) m π = .error .OOB := by
        by_cases hka : k < l₁.length
        · have hnb : ¬ k < l₂.length := fun h => hboth ⟨hka, h⟩
          have hkb : k = l₂.length := by omega
          subst hkb
          have hget₁ : l₁[l₂.length]? = some l₁[l₂.length] :=
            List.getElem?_eq_getElem hka
          have hget₂ : l₂[l₂.length]? = none :=
            List.getElem?_eq_none (Nat.le_refl _)
          exact memSumTwoBody_oob_b F l₁ l₂ nv l₂.length acc l₁[l₂.length]
            m π hk32 hlayA hlayB hmemA hmemB hget₁ hget₂
        · have hkk : k = l₁.length := by omega
          subst hkk
          have hget₁ : l₁[l₁.length]? = none :=
            List.getElem?_eq_none (Nat.le_refl _)
          exact memSumTwoBody_oob_a F l₁ l₂ nv l₁.length acc m π
            hk32 hlayA hlayB hmemA hget₁
      simp [sumTwoWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hbody]

/-! ### Whole-function correctness (fuel-generalized, then transfer) -/

/-- `memEval` for `sum_two` at any fuel covering `n` (mirrors
    `evalFuncFuel_sumTwo`; memory rides alongside, untouched). -/
theorem memEvalFuncFuel_sumTwo (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32)
    (hle₁ : nv.toNat ≤ l₁.length) (hle₂ : nv.toNat ≤ l₂.length)
    (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    memEvalFuncFuel F sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] =
      sumTwoFwd l₁ l₂ nv := by
  have hb := bindMemArgs_sumTwo l₁ l₂ nv
  have hlayA : layoutLookup [("a", 1, 1), ("b", 0, 0)] "a" = some (1, 1) :=
    layoutLookup_hit "a" 1 1 _
  have hlayB : layoutLookup [("a", 1, 1), ("b", 0, 0)] "b" = some (0, 0) := by
    simp [layoutLookup, show ("b" : String) ≠ "a" by decide]
  have hmemA : memFind ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩ 1 =
      some ⟨1, true, l₁⟩ := by
    simp [memFind]
  have hmemB : memFind ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩ 0 =
      some ⟨0, true, l₂⟩ := by
    have h01 : (0 == 1) = false := by decide
    simp [memFind, h01]
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l₁), ("b", .arr32 l₂), ("n", .u32 nv)]
      = mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0) := rfl
  have hret := mkSumTwoEnv_s l₁ l₂ nv nv.toNat (pairSum l₁ l₂ nv.toNat)
  have hle : nv.toNat ≤ l₁.length ∧ nv.toNat ≤ l₂.length := ⟨hle₁, hle₂⟩
  cases F with
  | zero =>
    have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
          sumTwoWhile (mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0))
          ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩
          [("a", 1, 1), ("b", 0, 0)]
        = .ok (((mkSumTwoEnv l₁ l₂ nv nv.toNat
            (BitVec.ofNat 32 0 + pairSum (l₁.drop 0) (l₂.drop 0)
              (nv.toNat - 0)),
            ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩,
            [("a", 1, 1), ("b", 0, 0)])),
            .fellThrough) :=
      memSumTwoWhile_correct l₁ l₂ nv 0 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hle₁ hle₂ h32 hlayA hlayB hmemA hmemB (by cir_fuel)
    simp [memEvalFuncFuel, sumTwoFunc, twoReaderParams, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal, sumTwoFwd,
      hb, henv, hloopH0, hret, hle]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          sumTwoWhile (mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0))
          ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩
          [("a", 1, 1), ("b", 0, 0)]
        = .ok (((mkSumTwoEnv l₁ l₂ nv nv.toNat
            (BitVec.ofNat 32 0 + pairSum (l₁.drop 0) (l₂.drop 0)
              (nv.toNat - 0)),
            ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩,
            [("a", 1, 1), ("b", 0, 0)])),
            .fellThrough) :=
      memSumTwoWhile_correct l₁ l₂ nv (F + 1) 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hle₁ hle₂ h32 hlayA hlayB hmemA hmemB (by cir_fuel)
    simp [memEvalFuncFuel, sumTwoFunc, twoReaderParams, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, sumTwoFwd,
      hb, henv, hloopS, hret, hle]

/-- OOB corollary at any fuel (mirrors `evalFuncFuel_sumTwo_oob`). -/
theorem memEvalFuncFuel_sumTwo_oob (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32)
    (hlt : min l₁.length l₂.length < nv.toNat)
    (hmin32 : min l₁.length l₂.length < 2 ^ 32)
    (hF : min l₁.length l₂.length + 1 ≤ F) :
    memEvalFuncFuel F sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] =
      .error .OOB := by
  have hb := bindMemArgs_sumTwo l₁ l₂ nv
  have hlayA : layoutLookup [("a", 1, 1), ("b", 0, 0)] "a" = some (1, 1) :=
    layoutLookup_hit "a" 1 1 _
  have hlayB : layoutLookup [("a", 1, 1), ("b", 0, 0)] "b" = some (0, 0) := by
    simp [layoutLookup, show ("b" : String) ≠ "a" by decide]
  have hmemA : memFind ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩ 1 =
      some ⟨1, true, l₁⟩ := by
    simp [memFind]
  have hmemB : memFind ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩ 0 =
      some ⟨0, true, l₂⟩ := by
    have h01 : (0 == 1) = false := by decide
    simp [memFind, h01]
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l₁), ("b", .arr32 l₂), ("n", .u32 nv)]
      = mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0) := rfl
  cases F with
  | zero =>
    have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
          sumTwoWhile (mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0))
          ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩
          [("a", 1, 1), ("b", 0, 0)] = .error .OOB :=
      memSumTwoWhile_oob l₁ l₂ nv 0 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hlt hmin32 hlayA hlayB hmemA hmemB (by cir_fuel)
    simp [memEvalFuncFuel, sumTwoFunc, twoReaderParams, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal,
      henv, hb, hloopH0]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          sumTwoWhile (mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0))
          ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩
          [("a", 1, 1), ("b", 0, 0)] = .error .OOB :=
      memSumTwoWhile_oob l₁ l₂ nv (F + 1) 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hlt hmin32 hlayA hlayB hmemA hmemB (by cir_fuel)
    simp [memEvalFuncFuel, sumTwoFunc, twoReaderParams, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, henv, hb, hloopS]

/-- Transfer for `sum_two` (in-range): both sides equal `sumTwoFwd`. -/
theorem memTransfer_sumTwo (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32)
    (hle₁ : nv.toNat ≤ l₁.length) (hle₂ : nv.toNat ≤ l₂.length)
    (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F)
    (_h : oracleNoalias sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv]) :
    memEvalFuncFuel F sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] =
      evalFuncFuel F sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] := by
  rw [memEvalFuncFuel_sumTwo F l₁ l₂ nv hle₁ hle₂ h32 hF,
    evalFuncFuel_sumTwo F l₁ l₂ nv hle₁ hle₂ h32 hF]

/-- Transfer for `sum_two` (OOB): both sides fail loudly. -/
theorem memTransfer_sumTwo_oob (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32)
    (hlt : min l₁.length l₂.length < nv.toNat)
    (hmin32 : min l₁.length l₂.length < 2 ^ 32)
    (hF : min l₁.length l₂.length + 1 ≤ F)
    (_h : oracleNoalias sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv]) :
    memEvalFuncFuel F sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] =
      evalFuncFuel F sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] := by
  rw [memEvalFuncFuel_sumTwo_oob F l₁ l₂ nv hlt hmin32 hF,
    evalFuncFuel_sumTwo_oob F l₁ l₂ nv hlt hmin32 hF]

