/-
Circe.Transfer — M3a per-leaf transfer (`oracleNoalias → memEval = Eval`).

`Circe.Mem` stays below `Emit` (no imports upward); this module joins
them for the M3a fragment (call-free C leaves live in `Mem` already —
`memTransfer_add/incr` — while `sum_array` / `vec_alloc` need the
canonical `Func`s + loop envs from `Emit`). Each proof mirrors the
corresponding `emit_correct` argument step for step, with the memory
side threaded alongside (reads cross-checked, writes lockstepped, loops
re-inducted with `Mem`/`Layout` constant or lockstepped).
-/
import Circe.Mem
import Circe.Emit.Sum
import Circe.Emit.Vec

/-! ## `sum_array` transfer -/

/-- `sum` binding: the array lifts into a fresh block holding its words
    (tag creation at bind); the bound is scalar. -/
theorem bindMemArgs_sum (l : List (BitVec 32)) (nv : BitVec 32) :
    bindMemArgs
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned }]
      [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)]) := by
  rfl

/-- `sum` entry footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_sum (l : List (BitVec 32)) (nv : BitVec 32) :
    oracleNoalias sumFunc [.arr32 l, .u32 nv] := by
  have hb : bindMemArgs sumFunc.args [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)]) := by
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
  have hmem : memFind ⟨1, [(0, ⟨0, true, l⟩)]⟩ 0 =
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
          ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)]
        = .ok (((mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)])),
            .fellThrough) :=
      memSumWhile_correct l nv 0 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hle h32 hlay hmem (by cir_fuel)
    simp [memEvalFuncFuel, sumFunc, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal,
      sumFwd, hb, henv, hloopH0, hret, hle]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
          ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)]
        = .ok (((mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)])),
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
  have hmem : memFind ⟨1, [(0, ⟨0, true, l⟩)]⟩ 0 =
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
          ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] = .error .OOB :=
      memSumWhile_oob l nv 0 0 (BitVec.ofNat 32 0) _ _
        (Nat.zero_le _) hlt hlen32 hlay hmem (by cir_fuel)
    simp [memEvalFuncFuel, sumFunc, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal,
      henv, hb, hloopH0]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
          ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] = .error .OOB :=
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

/-! ## `vec_alloc` transfer -/

/-- `vec_alloc` binding: the bound is owned scalar, empty layout. -/
theorem bindMemArgs_vec (nv : BitVec 32) :
    bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] ⟨0, []⟩ =
      some ([("n", .u32 nv)], ⟨0, []⟩, []) := by
  rfl

/-- `vec_alloc` entry footprints are empty (trivially disjoint). -/
theorem oracleNoalias_vec (nv : BitVec 32) :
    oracleNoalias vecFunc [.u32 nv] := by
  have hb : bindMemArgs vecFunc.args [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := by
    show bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] ⟨0, []⟩ = some ([("n", .u32 nv)], ⟨0, []⟩, [])
    exact bindMemArgs_vec nv
  have hn : LayoutNoAlias ([] : Layout) := layoutNoAlias_nil
  exact ⟨_, _, _, hb, hn⟩

/-- One memory fill step stores the index and advances (any fuel:
    loop-free), lockstepping value and memory. -/
theorem memVecFillBody_eval (F : Nat) (blk : Vec32) (nv : BitVec 32)
    (k : Nat) (sv jv : BitVec 32) (blkMid : Vec32)
    (m : Mem) (a : Addr) (π : Layout) (mMid : Mem)
    (_hklen : k < blk.val.length) (hk32 : k < 2 ^ 32)
    (_hlive : blk.freed = false)
    (hset : vecSet blk k (BitVec.ofNat 32 k) = .ok blkMid)
    (hstore : memStore m a a k (BitVec.ofNat 32 k) = .ok mMid)
    (hlay : layoutLookup π "v" = some (a, a))
    (_hfind : memFind m a = some ⟨a, true, blk.val⟩) :
    memEvalStmtFuel F vecFillBody
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
      .ok (((mkVecEnv blkMid nv (BitVec.ofNat 32 (k + 1)) sv jv,
        mMid, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : memEvalExpr (.var "i")
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
        .ok (.u32 (BitVec.ofNat 32 k)) := by
    have h1 := mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv
    simp [memEvalExpr, h1]
  have harr := mkVecEnv_v blk nv (BitVec.ofNat 32 k) sv jv
  have hset' : vecSet blk (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have hstore' : memStore m a a (BitVec.ofNat 32 k).toNat
      (BitVec.ofNat 32 k) = .ok mMid := by rw [hkk]; exact hstore
  have up1 : envUpdate (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) "v"
      (.vecVal blkMid) =
      some (mkVecEnv blkMid nv (BitVec.ofNat 32 k) sv jv) :=
    vecEnv_update_v blk nv (BitVec.ofNat 32 k) sv jv blkMid
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkVecEnv blkMid nv (BitVec.ofNat 32 k) sv jv) mMid π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_i blkMid nv (BitVec.ofNat 32 k) sv jv
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vecEnv_update_i blkMid nv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) sv jv
  cases F <;>
    simp only [vecFillBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hi, harr, hlay, hset', hstore', up1, hi2, up2]

/-- The memory fill-loop condition reads the index against the bound. -/
theorem memVecFillCond_eval (blk : Vec32) (nv : BitVec 32) (k : Nat)
    (sv jv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv
  have hn := mkVecEnv_n blk nv (BitVec.ofNat 32 k) sv jv
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- Fill-loop correctness on memory: the memory loop runs the `Base`
    fill to completion, lockstepping value and memory (the block always
    mirrors the value). -/
theorem memVecFillWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (sv jv : BitVec 32) (blkOut : Vec32)
    (m : Mem) (a : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hlen : blk.val.length = nv.toNat)
    (hlive : blk.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hfill : vecFillLoopAux blk k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    ∃ mOut, memEvalStmtFuel F vecFillWhile
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
      .ok (((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat) sv jv,
        mOut, π)), .fellThrough) ∧
      memFind mOut a = some ⟨a, true, blkOut.val⟩ ∧
      blkOut.freed = false := by
  induction F generalizing k blk m with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) m π =
        .ok (.b false) := by
      have hc := memVecFillCond_eval blk nv nv.toNat sv jv m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    refine ⟨m, ?_, hfind, hlive⟩
    simp only [vecFillWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
          .ok (.b true) := by
        simpa [hlt] using (memVecFillCond_eval blk nv k sv jv m π hk32)
      have hset : vecSet blk k (BitVec.ofNat 32 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blk k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      obtain ⟨mMid, hstore, hfindMid⟩ := vset_lockstep m a a blk k
        (BitVec.ofNat 32 k) ⟨a, true, blk.val⟩
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩
        hfind rfl rfl rfl hlive hset
      have hbody := memVecFillBody_eval F blk nv k sv jv
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ m a π mMid
        hklen hk32 hlive hset hstore hlay hfind
      have hstep : memEvalStmtFuel (F + 1) vecFillWhile
            (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π
          = memEvalStmtFuel F vecFillWhile
            (mkVecEnv ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ nv
              (BitVec.ofNat 32 (k + 1)) sv jv) mMid π := by
        simp [vecFillWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blk.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      exact ih ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) mMid
        (by omega) hlenMid rfl hfindMid hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) m π =
          .ok (.b false) := by
        have hc := memVecFillCond_eval blk nv nv.toNat sv jv m π hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      refine ⟨m, ?_, hfind, hlive⟩
      simp only [vecFillWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- One memory sum step accumulates the block element and advances
    (any fuel), with `Mem`/`Layout` untouched (reads only). -/
theorem memVecSumBody_eval (F : Nat) (blk : Vec32) (nv iv sv : BitVec 32)
    (k : Nat) (m : Mem) (a : Addr) (π : Layout)
    (hk32 : k < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hget : vecGet blk k = .ok (BitVec.ofNat 32 k)) :
    memEvalStmtFuel F vecSumBody
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
      .ok (((mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
        (BitVec.ofNat 32 (k + 1)), m, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hload : memLoad m a a (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by
    rw [hkk]
    exact memLoad_of_vecGet m a blk k hfind hget
  have hget' : vecGet blk (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hs0 := mkVecEnv_s blk nv iv sv (BitVec.ofNat 32 k)
  have harr := mkVecEnv_v blk nv iv sv (BitVec.ofNat 32 k)
  have hs : memEvalExpr (.uadd (.var "s") (.vget "v" (.var "j")))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
        .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [memEvalExpr, hs0, hlay, harr, hj, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hj2 : memEvalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
        (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
          (BitVec.ofNat 32 k)) m π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_j blk nv iv (sv + BitVec.ofNat 32 k)
      (BitVec.ofNat 32 k)
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vecEnv_update_s blk nv iv sv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k)
  have up2 := vecEnv_update_j blk nv iv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k) (BitVec.ofNat 32 (k + 1))
  cases F <;>
    simp only [vecSumBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hs, hj2, up1, up2]

/-- The memory sum-loop condition reads the index against the bound. -/
theorem memVecSumCond_eval (blk : Vec32) (nv iv sv : BitVec 32) (k : Nat)
    (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hn := mkVecEnv_n blk nv iv sv (BitVec.ofNat 32 k)
  simp only [memEvalExpr, hj, hn, ofNat32_ult k nv h]

/-- Sum-loop correctness on memory: the memory loop runs the `Base`
    sum to completion, leaving `Mem`/`Layout` untouched. -/
theorem memVecSumWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv sv : BitVec 32) (sout : BitVec 32)
    (m : Mem) (a : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet blk j = .ok (BitVec.ofNat 32 j))
    (hn32 : nv.toNat < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hsum : vecSumLoopAux blk k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    memEvalStmtFuel F vecSumWhile
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
      .ok (((mkVecEnv blk nv iv sout (BitVec.ofNat 32 nv.toNat), m, π)),
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) m π =
        .ok (.b false) := by
      have hc := memVecSumCond_eval blk nv iv sv nv.toNat m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vecSumWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
          .ok (.b true) := by
        simpa [hlt] using (memVecSumCond_eval blk nv iv sv k m π hk32)
      have hgetk : vecGet blk k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := memVecSumBody_eval F blk nv iv sv k m a π hk32
        hlay hfind hgetk
      have hstep : memEvalStmtFuel (F + 1) vecSumWhile
            (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π
          = memEvalStmtFuel F vecSumWhile
            (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
              (BitVec.ofNat 32 (k + 1))) m π := by
        simp [vecSumWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      have hgetk' : vecGet blk k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      simp only [vecSumLoopAux, hgetk'] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) m π =
          .ok (.b false) := by
        have hc := memVecSumCond_eval blk nv iv sv nv.toNat m π hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vecSumWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- `memEval` for `vec_alloc` at any fuel covering `n` (mirrors
    `evalFuncFuel_vec`; memory locksteps the value). -/
theorem memEvalFuncFuel_vec (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32) :
    memEvalFuncFuel F vecFunc [.u32 nv] =
      .ok (.u32 (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
        nv.toNat)) := by
  have hb := bindMemArgs_vec nv
  have hfresh : (⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ : Vec32).val.length =
      0 + nv.toNat := by simp
  obtain ⟨blkOut, hfill0⟩ := vecFillLoopAux_fresh_ok
    (List.replicate nv.toNat (BitVec.ofNat 32 0)) 0 nv.toNat (by simp)
  have hliveOut : blkOut.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hfill0
  have hgetOut : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + nv.toNat := by omega
    exact vecFillLoopAux_get _ 0 nv.toNat _ rfl hfresh hfill0 j hjlo hjhi'
  have hsum0 := vecSumLoopAux_correct blkOut 0 nv.toNat 0 (by
    intro j hjlo hjhi
    exact hgetOut j hjlo (by omega))
  have hrange : List.range' 0 nv.toNat = List.range nv.toNat := by
    simp [List.range_eq_range']
  rw [hrange] at hsum0
  have h0 : (0 : BitVec 32) + prefixSumU32 ((List.range nv.toNat).map
      (BitVec.ofNat 32)) nv.toNat
      = prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat :=
    BitVec.zero_add _
  rw [h0] at hsum0
  have hlayV : layoutLookup [("v", 0, 0)] "v" = some (0, 0) := by
    simp [layoutLookup]
  have hfindV : memFind ⟨1, [(0, ⟨0, true,
      List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)]⟩ 0 =
      some ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩ := by
    simp [memFind]
  have hn0 : envLookup [("n", .u32 nv)] "n" = some (.u32 nv) := rfl
  have hfree0 : vecFree blkOut = .ok ⟨blkOut.val, true⟩ :=
    vecFree_ok blkOut hliveOut
  cases F with
  | zero =>
    obtain ⟨mFill, hfillLoop, hfindFill, _hliveFill⟩ :=
      memVecFillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv 0 0
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkOut
        ⟨1, [(0, ⟨0, true,
          List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)]⟩ 0 [("v", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayV hfindV hfill0 (by cir_fuel)
    have hloopF0 : memEvalStmtWith memEvalStmtZeroHandler
          vecFillWhile
          [("j", .u32 0), ("s", .u32 0), ("i", .u32 0),
           ("v", .vecVal ⟨List.replicate nv.toNat 0, false⟩),
           ("n", .u32 nv)]
          ⟨1, [(0, ⟨0, true, List.replicate nv.toNat 0⟩)]⟩
          [("v", 0, 0)]
        = .ok ((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    have hloopS0 : memEvalStmtWith memEvalStmtZeroHandler
          vecSumWhile
          (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mFill [("v", 0, 0)]
        = .ok ((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      memVecSumWhile_correct blkOut nv 0 0 (BitVec.ofNat 32 nv.toNat) _ _
        mFill 0 [("v", 0, 0)]
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hlayV
        hfindFill hsum0 (by cir_fuel)
    obtain ⟨mFree, hmfree, _hfindFree⟩ := vfree_lockstep mFill 0 0 blkOut
      ⟨0, true, blkOut.val⟩ ⟨blkOut.val, true⟩ hfindFill rfl rfl rfl
      hliveOut hfree0
    have huv := vecEnv_update_v blkOut nv (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat) ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat)
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat)
    simp only [memEvalFuncFuel, vecFunc, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal, hn0, vecNew,
      memAllocData, Nat.reduceAdd]
    simp only [hloopF0, hloopS0, hfree0,
      hmfree, huv, harv, hars, hlayV]
  | succ F =>
    obtain ⟨mFill, hfillLoop, hfindFill, _hliveFill⟩ :=
      memVecFillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (F + 1) 0
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkOut
        ⟨1, [(0, ⟨0, true,
          List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)]⟩ 0 [("v", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayV hfindV hfill0 (by cir_fuel)
    have hloopFS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vecFillWhile
          [("j", .u32 0), ("s", .u32 0), ("i", .u32 0),
           ("v", .vecVal ⟨List.replicate nv.toNat 0, false⟩),
           ("n", .u32 nv)]
          ⟨1, [(0, ⟨0, true, List.replicate nv.toNat 0⟩)]⟩
          [("v", 0, 0)]
        = .ok ((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    have hloopSS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vecSumWhile
          (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mFill [("v", 0, 0)]
        = .ok ((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      memVecSumWhile_correct blkOut nv (F + 1) 0 (BitVec.ofNat 32 nv.toNat)
        _ _ mFill 0 [("v", 0, 0)] (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hlayV
        hfindFill hsum0 (by cir_fuel)
    obtain ⟨mFree, hmfree, _hfindFree⟩ := vfree_lockstep mFill 0 0 blkOut
      ⟨0, true, blkOut.val⟩ ⟨blkOut.val, true⟩ hfindFill rfl rfl rfl
      hliveOut hfree0
    have huv := vecEnv_update_v blkOut nv (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat) ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat)
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat)
    simp only [memEvalFuncFuel, vecFunc, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, hn0, vecNew,
      memAllocData, Nat.reduceAdd]
    simp only [hloopFS, hloopSS, hfree0,
      hmfree, huv, harv, hars, hlayV]

/-- Transfer for `vec_alloc`: both sides equal the prefix sum. -/
theorem memTransfer_vec (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32)
    (_h : oracleNoalias vecFunc [.u32 nv]) :
    memEvalFuncFuel F vecFunc [.u32 nv] =
      evalFuncFuel F vecFunc [.u32 nv] := by
  rw [memEvalFuncFuel_vec F nv hn hn32, evalFuncFuel_vec F nv hn hn32]
