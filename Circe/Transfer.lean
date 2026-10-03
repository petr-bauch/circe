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
import Circe.Derived
import Circe.Emit.Sum
import Circe.Emit.Vec
import Circe.Emit.Add
import Circe.Emit.Choose
import Circe.Emit.Struct
import Circe.Emit.Flow
import Circe.Emit.Calls
import Circe.Emit.Vec2

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

/-! ## M3c heap transfer: `vec_copy_sum` (two live blocks) -/

/-- Memory fill-loop condition reads `i` against the bound. -/
theorem memVec2FillCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (jv kv sv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n"))
      (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVec2Env_i blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  have hn := mkVec2Env_n blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- Memory copy-loop condition reads `j` against the bound. -/
theorem memVec2CopyCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (iv sv kv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "j") (.var "n"))
      (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hn := mkVec2Env_n blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  simp only [memEvalExpr, hj, hn, ofNat32_ult k nv h]

/-- Memory sum-loop condition reads `k` against the bound. -/
theorem memVec2SumCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (iv jv sv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "k") (.var "n"))
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hk := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hn := mkVec2Env_n blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  simp only [memEvalExpr, hk, hn, ofNat32_ult k nv h]

/-- One memory fill step stores the index into `a` and advances (any
    fuel), with `Mem`/`Layout` lockstepped on `a` (the `b` pin is
    untouched — preservation is the loop's job). -/
theorem memVec2FillBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (jv kv sv : BitVec 32) (blkMid : Vec32)
    (m : Mem) (aA : Addr) (π : Layout) (mMid : Mem)
    (hk32 : k < 2 ^ 32)
    (hset : vecSet blkA k (BitVec.ofNat 32 k) = .ok blkMid)
    (hstore : memStore m aA aA k (BitVec.ofNat 32 k) = .ok mMid)
    (hlay : layoutLookup π "a" = some (aA, aA)) :
    memEvalStmtFuel F vec2FillBody
      (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (((mkVec2Env blkMid blkB nv (BitVec.ofNat 32 (k + 1)) jv kv sv,
        mMid, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : memEvalExpr (.var "i")
      (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (.u32 (BitVec.ofNat 32 k)) := by
    have h1 := mkVec2Env_i blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
    simp [memEvalExpr, h1]
  have harr := mkVec2Env_a blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  have hset' : vecSet blkA (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have hstore' : memStore m aA aA (BitVec.ofNat 32 k).toNat
      (BitVec.ofNat 32 k) = .ok mMid := by rw [hkk]; exact hstore
  have up1 := vec2Env_update_a blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
    blkMid
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
      (mkVec2Env blkMid blkB nv (BitVec.ofNat 32 k) jv kv sv) mMid π =
      .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_i blkMid blkB nv (BitVec.ofNat 32 k) jv kv sv
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vec2Env_update_i blkMid blkB nv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) jv kv sv
  cases F <;>
    simp only [vec2FillBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hi, harr, hlay, hset', hstore', up1, hi2, up2]

/-- One memory copy step reads `a[j]`, stores into `b[j]`, advances (any
    fuel): the source block is read through the cross-checked `vget`,
    the target block locksteps value and memory. -/
theorem memVec2CopyBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (iv sv kv : BitVec 32) (blkMid : Vec32)
    (m : Mem) (aA aB : Addr) (π : Layout) (mMid : Mem)
    (hk32 : k < 2 ^ 32)
    (hgetA : vecGet blkA k = .ok (BitVec.ofNat 32 k))
    (hsetB : vecSet blkB k (BitVec.ofNat 32 k) = .ok blkMid)
    (hstoreB : memStore m aB aB k (BitVec.ofNat 32 k) = .ok mMid)
    (hlayA : layoutLookup π "a" = some (aA, aA))
    (hlayB : layoutLookup π "b" = some (aB, aB))
    (hfindA : memFind m aA = some ⟨aA, true, blkA.val⟩) :
    memEvalStmtFuel F vec2CopyBody
      (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (((mkVec2Env blkA blkMid nv iv (BitVec.ofNat 32 (k + 1)) kv sv,
        mMid, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hj : memEvalExpr (.var "j")
      (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (.u32 (BitVec.ofNat 32 k)) := by
    have h1 := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    simp [memEvalExpr, h1]
  have ha := mkVec2Env_a blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hb := mkVec2Env_b blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hloadA : memLoad m aA aA k = .ok (BitVec.ofNat 32 k) :=
    memLoad_of_vecGet m aA blkA k hfindA hgetA
  have hloadA' : memLoad m aA aA (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hloadA
  have hgetA' : vecGet blkA (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hgetA
  have hg : memEvalExpr (.vget "a" (.var "j"))
      (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (.u32 (BitVec.ofNat 32 k)) := by
    -- `hj` (memEvalExpr-headed) would compete with `memEvalExpr`
    -- unfolding and lose, so discharge the index lookup with the
    -- `envLookup`-headed `hjl` instead (no competing rule).
    have hjl := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    simp only [memEvalExpr, hlayA, ha, hjl, hloadA', hgetA',
      beq_self_eq_true, ↓reduceIte]
  have hsetB' : vecSet blkB (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hsetB
  have hstoreB' : memStore m aB aB (BitVec.ofNat 32 k).toNat
      (BitVec.ofNat 32 k) = .ok mMid := by rw [hkk]; exact hstoreB
  have up1 := vec2Env_update_b blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    blkMid
  have hj2 : memEvalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
      (mkVec2Env blkA blkMid nv iv (BitVec.ofNat 32 k) kv sv) mMid π =
      .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_j blkA blkMid nv iv (BitVec.ofNat 32 k) kv sv
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vec2Env_update_j blkA blkMid nv iv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) kv sv
  cases F <;>
    simp only [vec2CopyBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hj, hb, hlayB, hg, hsetB', hstoreB', up1, hj2, up2]

/-- One memory sum step accumulates `b[k]` and advances (any fuel),
    with `Mem`/`Layout` untouched (reads only). -/
theorem memVec2SumBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (iv jv sv : BitVec 32)
    (m : Mem) (aB : Addr) (π : Layout)
    (hk32 : k < 2 ^ 32)
    (hlayB : layoutLookup π "b" = some (aB, aB))
    (hfindB : memFind m aB = some ⟨aB, true, blkB.val⟩)
    (hget : vecGet blkB k = .ok (BitVec.ofNat 32 k)) :
    memEvalStmtFuel F vec2SumBody
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (((mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 (k + 1))
        (sv + BitVec.ofNat 32 k), m, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hload : memLoad m aB aB (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by
    rw [hkk]
    exact memLoad_of_vecGet m aB blkB k hfindB hget
  have hget' : vecGet blkB (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hk := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hs0 := mkVec2Env_s blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have harr := mkVec2Env_b blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hs : memEvalExpr (.uadd (.var "s") (.vget "b" (.var "k")))
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [memEvalExpr, hs0, hlayB, harr, hk, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hk2 : memEvalExpr (.uadd (.var "k") (.lit (.u32 1#32)))
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k)
        (sv + BitVec.ofNat 32 k)) m π =
      .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k)
      (sv + BitVec.ofNat 32 k)
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vec2Env_update_s blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
    (sv + BitVec.ofNat 32 k)
  have up2 := vec2Env_update_k blkA blkB nv iv jv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) (sv + BitVec.ofNat 32 k)
  cases F <;>
    simp only [vec2SumBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hs, hk2, up1, up2]

/-- Fill-loop correctness on memory: the memory loop runs the `Base`
    fill to completion on `a`, lockstepping value and memory, while the
    `b` pin fact rides alongside untouched (writes cons-shadow, so the
    other address is preserved by `memFind_memStore_other`). -/
theorem memVec2FillWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (jv kv sv : BitVec 32) (blkOut : Vec32)
    (m : Mem) (aA aB : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hlenA : blkA.val.length = nv.toNat)
    (hliveA : blkA.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hlayA : layoutLookup π "a" = some (aA, aA))
    (hfindA : memFind m aA = some ⟨aA, true, blkA.val⟩)
    (hfindB : memFind m aB = some ⟨aB, true, blkB.val⟩)
    (hne : aA ≠ aB)
    (hfill : vecFillLoopAux blkA k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    ∃ mOut, memEvalStmtFuel F vec2FillWhile
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (((mkVec2Env blkOut blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv,
        mOut, π)), .fellThrough) ∧
      memFind mOut aA = some ⟨aA, true, blkOut.val⟩ ∧
      blkOut.freed = false ∧
      memFind mOut aB = some ⟨aB, true, blkB.val⟩ := by
  induction F generalizing k blkA m with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv) m π =
        .ok (.b false) := by
      have hc := memVec2FillCond_eval blkA blkB nv nv.toNat jv kv sv m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    refine ⟨m, ?_, hfindA, hliveA, hfindB⟩
    simp only [vec2FillWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blkA.val.length := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
          .ok (.b true) := by
        simpa [hlt] using
          (memVec2FillCond_eval blkA blkB nv k jv kv sv m π hk32)
      have hset : vecSet blkA k (BitVec.ofNat 32 k) =
          .ok ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blkA k _ hliveA hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      obtain ⟨mMid, hstore, hfindMid⟩ := vset_lockstep m aA aA blkA k
        (BitVec.ofNat 32 k) ⟨aA, true, blkA.val⟩
        ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩
        hfindA rfl rfl rfl hliveA hset
      have hfindMidB : memFind mMid aB = some ⟨aB, true, blkB.val⟩ := by
        rw [memFind_memStore_other m mMid aA aB aA k _ hstore
          (Ne.symm hne)]
        exact hfindB
      have hbody := memVec2FillBody_eval F blkA blkB nv k jv kv sv
        ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ m aA π mMid
        hk32 hset hstore hlayA
      have hstep : memEvalStmtFuel (F + 1) vec2FillWhile
            (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π
          = memEvalStmtFuel F vec2FillWhile
            (mkVec2Env ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ blkB nv
              (BitVec.ofNat 32 (k + 1)) jv kv sv) mMid π := by
        simp [vec2FillWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blkA.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      exact ih ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) mMid
        (by omega) hlenMid rfl hfindMid hfindMidB hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVec2Env blkA blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv) m π =
          .ok (.b false) := by
        have hc := memVec2FillCond_eval blkA blkB nv nv.toNat jv kv sv m π
          hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      refine ⟨m, ?_, hfindA, hliveA, hfindB⟩
      simp only [vec2FillWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- Copy-loop correctness on memory: `blkA` is the fixed read-only
    source (its pin fact is preserved over writes to `b`); `blkB`
    accumulates the copy in lockstep. -/
theorem memVec2CopyWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv sv kv : BitVec 32) (blkOut : Vec32)
    (m : Mem) (aA aB : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hlenB : blkB.val.length = nv.toNat)
    (hliveB : blkB.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hlayA : layoutLookup π "a" = some (aA, aA))
    (hlayB : layoutLookup π "b" = some (aB, aB))
    (hfindA : memFind m aA = some ⟨aA, true, blkA.val⟩)
    (hfindB : memFind m aB = some ⟨aB, true, blkB.val⟩)
    (hne : aA ≠ aB)
    (hpre : ∀ t, t < k → vecGet blkB t = .ok (BitVec.ofNat 32 t))
    (hsrc : ∀ t, t < nv.toNat → vecGet blkA t = .ok (BitVec.ofNat 32 t))
    (hcopy : vecCopyLoopAux blkA blkB k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    ∃ mOut, memEvalStmtFuel F vec2CopyWhile
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (((mkVec2Env blkA blkOut nv iv (BitVec.ofNat 32 nv.toNat) kv sv,
        mOut, π)), .fellThrough) ∧
      memFind mOut aA = some ⟨aA, true, blkA.val⟩ ∧
      memFind mOut aB = some ⟨aB, true, blkOut.val⟩ ∧
      blkOut.freed = false := by
  induction F generalizing k blkB m with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 nv.toNat) kv sv) m π =
        .ok (.b false) := by
      have hc := memVec2CopyCond_eval blkA blkB nv nv.toNat iv sv kv m π
        hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hcopy
    simp only [vecCopyLoopAux] at hcopy
    cases hcopy
    refine ⟨m, ?_, hfindA, hfindB, hliveB⟩
    simp only [vec2CopyWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklenB : k < blkB.val.length := by omega
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
            (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
            .ok (.b true) := by
        simpa [hlt] using
          (memVec2CopyCond_eval blkA blkB nv k iv sv kv m π hk32)
      have hgetk : vecGet blkA k = .ok (BitVec.ofNat 32 k) :=
        hsrc k (by omega)
      have hset : vecSet blkB k (BitVec.ofNat 32 k) =
          .ok ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blkB k _ hliveB hklenB
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hcopy
      simp only [vecCopyLoopAux, hgetk, hset] at hcopy
      obtain ⟨mMid, hstore, hfindMid⟩ := vset_lockstep m aB aB blkB k
        (BitVec.ofNat 32 k) ⟨aB, true, blkB.val⟩
        ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩
        hfindB rfl rfl rfl hliveB hset
      have hfindMidA : memFind mMid aA = some ⟨aA, true, blkA.val⟩ := by
        rw [memFind_memStore_other m mMid aB aA aB k _ hstore hne]
        exact hfindA
      have hbody := memVec2CopyBody_eval F blkA blkB nv k iv sv kv
        ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ m aA aB π mMid
        hk32 hgetk hset hstore hlayA hlayB hfindA
      have hstep : memEvalStmtFuel (F + 1) vec2CopyWhile
            (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π
          = memEvalStmtFuel F vec2CopyWhile
            (mkVec2Env blkA
              ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ nv iv
              (BitVec.ofNat 32 (k + 1)) kv sv) mMid π := by
        simp [vec2CopyWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blkB.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      have hpre' : ∀ t, t < k + 1 →
          vecGet ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ t =
            .ok (BitVec.ofNat 32 t) := by
        intro t ht
        by_cases htk : t = k
        · subst t
          rw [vecGet_ok _ _ _ rfl]
          exact getElem?_set_self blkB.val k _ hklenB
        · exact vecSet_get_other blkB k t _ _ _ (by omega) hset
            (hpre t (by omega))
      exact ih ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) mMid
        (by omega) hlenMid hliveMid hfindMidA hfindMid hpre' hcopy (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
          (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 nv.toNat) kv sv) m π =
          .ok (.b false) := by
        have hc := memVec2CopyCond_eval blkA blkB nv nv.toNat iv sv kv m π
          hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hcopy
      simp only [vecCopyLoopAux] at hcopy
      cases hcopy
      refine ⟨m, ?_, hfindA, hfindB, hliveB⟩
      simp only [vec2CopyWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- Sum-loop correctness on memory over `b`: the memory loop runs the
    `Base` sum to completion, leaving `Mem`/`Layout` untouched. -/
theorem memVec2SumWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv jv sv : BitVec 32) (sout : BitVec 32)
    (m : Mem) (aA aB : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet blkB j = .ok (BitVec.ofNat 32 j))
    (hn32 : nv.toNat < 2 ^ 32)
    (hlayB : layoutLookup π "b" = some (aB, aB))
    (_hfindA : memFind m aA = some ⟨aA, true, blkA.val⟩)
    (hfindB : memFind m aB = some ⟨aB, true, blkB.val⟩)
    (hsum : vecSumLoopAux blkB k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    memEvalStmtFuel F vec2SumWhile
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (((mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sout,
        m, π)), .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "k") (.var "n"))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sv) m π =
        .ok (.b false) := by
      have hc := memVec2SumCond_eval blkA blkB nv nv.toNat iv jv sv m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vec2SumWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "k") (.var "n"))
          (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
          .ok (.b true) := by
        simpa [hlt] using
          (memVec2SumCond_eval blkA blkB nv k iv jv sv m π hk32)
      have hgetk : vecGet blkB k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := memVec2SumBody_eval F blkA blkB nv k iv jv sv
        m aB π hk32 hlayB hfindB hgetk
      have hstep : memEvalStmtFuel (F + 1) vec2SumWhile
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π
          = memEvalStmtFuel F vec2SumWhile
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 (k + 1))
              (sv + BitVec.ofNat 32 k)) m π := by
        simp [vec2SumWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      have hgetk' : vecGet blkB k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      simp only [vecSumLoopAux, hgetk'] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "k") (.var "n"))
          (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sv) m π =
          .ok (.b false) := by
        have hc := memVec2SumCond_eval blkA blkB nv nv.toNat iv jv sv m π
          hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vec2SumWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- `memEval` for `vec_copy_sum` at any fuel covering `n` (mirrors
    `evalFuncFuel_vec2`; both blocks ride alongside in lockstep). -/
theorem memEvalFuncFuel_vec2 (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32) :
    memEvalFuncFuel F vec2Func [.u32 nv] =
      .ok (.u32 (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
        nv.toNat)) := by
  -- Stated unfolded (`⟨0, []⟩`): if `emptyMem` unfolds first, the
  -- `bindMemArgs_vec2` match is destroyed and the closing `simp` stalls.
  have hb : bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] (⟨0, []⟩ : Mem) =
      some ([("n", .u32 nv)], (⟨0, []⟩ : Mem), []) :=
    bindMemArgs_vec2 nv
  have hfresh : (⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ : Vec32).val.length =
      0 + nv.toNat := by simp
  obtain ⟨blkAOut, hfill0⟩ := vecFillLoopAux_fresh_ok
    (List.replicate nv.toNat (BitVec.ofNat 32 0)) 0 nv.toNat (by simp)
  have hliveAOut : blkAOut.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hfill0
  have hlenAOut : blkAOut.val.length = nv.toNat := by
    have h := vecFillLoopAux_length _ _ _ _ hfill0
    simp at h
    exact h
  have hgetA : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkAOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + nv.toNat := by omega
    exact vecFillLoopAux_get _ 0 nv.toNat _ rfl hfresh hfill0 j hjlo hjhi'
  obtain ⟨blkBOut, hcopy0⟩ := vecCopyLoopAux_fresh_ok blkAOut
    ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ 0 nv.toNat
    hliveAOut rfl (by rw [hlenAOut]; simp) (by omega)
    (fun t ht => hgetA t (by omega) (by omega))
  have hliveBOut : blkBOut.freed = false :=
    vecCopyLoopAux_live _ _ _ _ _ rfl hcopy0
  have hlenBOut : blkBOut.val.length = nv.toNat := by
    have h := vecCopyLoopAux_length _ _ _ _ _ hcopy0
    simp at h
    exact h
  have hgetB : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkBOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + (nv.toNat - 0) := by omega
    exact vecCopyLoopAux_all blkAOut
      ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ 0
      (nv.toNat - 0) blkBOut rfl (by rw [hlenAOut]; simp) (by omega)
      (fun t ht => absurd ht (by omega))
      (fun t ht => hgetA t (by omega) (by omega)) hcopy0 j hjhi'
  have hsum0 := vecSumLoopAux_correct blkBOut 0 nv.toNat 0 (by
    intro j hjlo hjhi
    exact hgetB j hjlo (by omega))
  have hrange : List.range' 0 nv.toNat = List.range nv.toNat := by
    simp [List.range_eq_range']
  rw [hrange] at hsum0
  have h0 : (0 : BitVec 32) + prefixSumU32 ((List.range nv.toNat).map
      (BitVec.ofNat 32)) nv.toNat
      = prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat :=
    BitVec.zero_add _
  rw [h0] at hsum0
  have hfreeA : vecFree blkAOut = .ok ⟨blkAOut.val, true⟩ :=
    vecFree_ok blkAOut hliveAOut
  have hfreeB : vecFree blkBOut = .ok ⟨blkBOut.val, true⟩ :=
    vecFree_ok blkBOut hliveBOut
  -- The second `vnew` reads `n` past the `a` binding (cf. `evalFuncFuel_vec2`).
  have hna : envLookup [("a", .vecVal
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
      ("n", .u32 nv)] "n" = some (.u32 nv) := by
    simp [envLookup, show ("n" : String) ≠ "a" by decide]
  -- The six lets build the two-block env (stated `ofNat`-headed: simp's
  -- simprocs normalize `0` to `0#32`).
  have henv : [("s", .u32 (BitVec.ofNat 32 0)),
        ("k", .u32 (BitVec.ofNat 32 0)),
        ("j", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("b", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("a", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("n", .u32 nv)]
      = mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0) := rfl
  have hn0 : envLookup [("n", .u32 nv)] "n" = some (.u32 nv) := rfl
  have hlayA : layoutLookup [("b", 1, 1), ("a", 0, 0)] "a" =
      some (0, 0) := by
    simp [layoutLookup, show ("a" : String) ≠ "b" by decide]
  have hlayB : layoutLookup [("b", 1, 1), ("a", 0, 0)] "b" =
      some (1, 1) := by
    simp [layoutLookup]
  have hfindA0 : memFind ⟨2, [(1, ⟨1, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
        (0, ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)]⟩ 0 =
      some ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩ := by
    simp [memFind]
  have hfindB0 : memFind ⟨2, [(1, ⟨1, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
        (0, ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)]⟩ 1 =
      some ⟨1, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩ := by
    simp [memFind]
  cases F with
  | zero =>
    obtain ⟨mFill, hfillLoop, hfindFillA, _hliveFill, hfindFillB⟩ :=
      memVec2FillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv 0 0
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        blkAOut
        ⟨2, [(1, ⟨1, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
          (0, ⟨0, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)]⟩
        0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayA hfindA0 hfindB0
        (by decide) hfill0 (by cir_fuel)
    have hloopF0 : memEvalStmtWith memEvalStmtZeroHandler
          vec2FillWhile
          (mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
          ⟨2, [(1, ⟨1, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
            (0, ⟨0, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)]⟩
          [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill,
            [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    obtain ⟨mCopy, hcopyLoop, hfindCopyA, hfindCopyB, _hliveCopy⟩ :=
      memVec2CopyWhile_correct blkAOut
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv 0 0 nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        blkBOut mFill 0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayA hlayB
        hfindFillA hfindFillB (by decide)
        (fun t ht => absurd ht (by omega))
        (fun t ht => hgetA t (by omega) (by omega)) hcopy0 (by cir_fuel)
    have hloopC0 : memEvalStmtWith memEvalStmtZeroHandler
          vec2CopyWhile
          (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mFill [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut blkBOut nv nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0), mCopy, [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      hcopyLoop
    have hloopS0 : memEvalStmtWith memEvalStmtZeroHandler
          vec2SumWhile
          (mkVec2Env blkAOut blkBOut nv nv nv (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
          mCopy [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut blkBOut nv nv nv
            (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat), mCopy, [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      memVec2SumWhile_correct blkAOut blkBOut nv 0 0 nv nv
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
        mCopy 0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetB j hjlo hjhi) hn32 hlayB
        hfindCopyA hfindCopyB hsum0 (by cir_fuel)
    obtain ⟨mFreeA, hmfreeA, hfindFreeA⟩ := vfree_lockstep mCopy 0 0 blkAOut
      ⟨0, true, blkAOut.val⟩ ⟨blkAOut.val, true⟩ hfindCopyA rfl rfl rfl
      hliveAOut hfreeA
    have hfindB2 : memFind mFreeA 1 = some ⟨1, true, blkBOut.val⟩ := by
      rw [memFind_memFree_other mCopy mFreeA 0 1 0 hmfreeA (by decide)]
      exact hfindCopyB
    obtain ⟨mFreeB, hmfreeB, _hfindFreeB⟩ := vfree_lockstep mFreeA 1 1
      blkBOut ⟨1, true, blkBOut.val⟩ ⟨blkBOut.val, true⟩ hfindB2 rfl rfl
      rfl hliveBOut hfreeB
    have huvA := vec2Env_update_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkAOut.val, true⟩
    have huvB := vec2Env_update_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkBOut.val, true⟩
    have harA := mkVec2Env_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    have harB := mkVec2Env_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    have hars := mkVec2Env_s ⟨blkAOut.val, true⟩ ⟨blkBOut.val, true⟩ nv
      nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    simp [memEvalFuncFuel, vec2Func, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal, hn0, hna,
      vecNew, memAllocData, Nat.reduceAdd, henv,
      hloopF0, hloopC0, hloopS0, hfreeA, hfreeB, hmfreeA, hmfreeB,
      huvA, huvB, harA, harB, hars, hlayA, hlayB]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by cir_fuel
    obtain ⟨mFill, hfillLoop, hfindFillA, _hliveFill, hfindFillB⟩ :=
      memVec2FillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (F + 1) 0
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        blkAOut
        ⟨2, [(1, ⟨1, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
          (0, ⟨0, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)]⟩
        0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayA hfindA0 hfindB0
        (by decide) hfill0 hFS
    have hloopFS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vec2FillWhile
          (mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
          ⟨2, [(1, ⟨1, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
            (0, ⟨0, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)]⟩
          [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill,
            [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    obtain ⟨mCopy, hcopyLoop, hfindCopyA, hfindCopyB, _hliveCopy⟩ :=
      memVec2CopyWhile_correct blkAOut
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (F + 1) 0 nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        blkBOut mFill 0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayA hlayB
        hfindFillA hfindFillB (by decide)
        (fun t ht => absurd ht (by omega))
        (fun t ht => hgetA t (by omega) (by omega)) hcopy0 hFS
    have hloopCS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vec2CopyWhile
          (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mFill [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut blkBOut nv nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0), mCopy, [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      hcopyLoop
    have hloopSS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vec2SumWhile
          (mkVec2Env blkAOut blkBOut nv nv nv (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
          mCopy [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut blkBOut nv nv nv
            (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat), mCopy, [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      memVec2SumWhile_correct blkAOut blkBOut nv (F + 1) 0 nv nv
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
        mCopy 0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetB j hjlo hjhi) hn32 hlayB
        hfindCopyA hfindCopyB hsum0 hFS
    obtain ⟨mFreeA, hmfreeA, hfindFreeA⟩ := vfree_lockstep mCopy 0 0 blkAOut
      ⟨0, true, blkAOut.val⟩ ⟨blkAOut.val, true⟩ hfindCopyA rfl rfl rfl
      hliveAOut hfreeA
    have hfindB2 : memFind mFreeA 1 = some ⟨1, true, blkBOut.val⟩ := by
      rw [memFind_memFree_other mCopy mFreeA 0 1 0 hmfreeA (by decide)]
      exact hfindCopyB
    obtain ⟨mFreeB, hmfreeB, _hfindFreeB⟩ := vfree_lockstep mFreeA 1 1
      blkBOut ⟨1, true, blkBOut.val⟩ ⟨blkBOut.val, true⟩ hfindB2 rfl rfl
      rfl hliveBOut hfreeB
    have huvA := vec2Env_update_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkAOut.val, true⟩
    have huvB := vec2Env_update_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkBOut.val, true⟩
    have harA := mkVec2Env_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    have harB := mkVec2Env_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    have hars := mkVec2Env_s ⟨blkAOut.val, true⟩ ⟨blkBOut.val, true⟩ nv
      nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    simp [memEvalFuncFuel, vec2Func, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, hn0, hna, vecNew,
      memAllocData, Nat.reduceAdd, henv,
      hloopFS, hloopCS, hloopSS, hfreeA, hfreeB, hmfreeA, hmfreeB,
      huvA, huvB, harA, harB, hars, hlayA, hlayB]

/-- Transfer for `vec_copy_sum`: both sides equal the prefix sum. -/
theorem memTransfer_vec2 (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32)
    (_h : oracleNoalias vec2Func [.u32 nv]) :
    memEvalFuncFuel F vec2Func [.u32 nv] =
      evalFuncFuel F vec2Func [.u32 nv] := by
  rw [memEvalFuncFuel_vec2 F nv hn hn32, evalFuncFuel_vec2 F nv hn hn32]

/-! ## M3c loop-free transfers: `choose`, 64-bit widths, `cls`, `translate` -/

/-- Transfer for `choose` (any fuel): the body is a pure `if` over
    functionalized borrows, so memory is untouched and both sides
    select identically. -/
theorem memTransfer_choose (F : Nat) (b : Bool) (x y : BitVec 32)
    (_h : oracleNoalias chooseFunc [.b b, .i32 x, .i32 y]) :
    memEvalFuncFuel F chooseFunc [.b b, .i32 x, .i32 y] =
      evalFuncFuel F chooseFunc [.b b, .i32 x, .i32 y] := by
  have hbf : chooseFunc.args =
      [{ name := "b", ty := .bool, role := .owned },
       { name := "x", ty := .i 32, role := .mutBorrow 0 },
       { name := "y", ty := .i 32, role := .mutBorrow 0 }] := rfl
  have hbody : chooseFunc.body =
      .if_ (.var "b") (.return_ (.var "x")) (.return_ (.var "y")) := rfl
  have hb : bindMemArgs
      [{ name := "b", ty := .bool, role := .owned },
       { name := "x", ty := .i 32, role := .mutBorrow 0 },
       { name := "y", ty := .i 32, role := .mutBorrow 0 }]
      [.b b, .i32 x, .i32 y] emptyMem =
      some ([("b", .b b), ("x", .i32 x), ("y", .i32 y)], emptyMem, []) := rfl
  have hbb : envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "b" =
      some (.b b) := by simp [envLookup]
  have hx : envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "x" =
      some (.i32 x) := by
    simp [envLookup, show ("x" : String) ≠ "b" by decide]
  have hy : envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "y" =
      some (.i32 y) := by
    simp [envLookup, show ("y" : String) ≠ "b" by decide,
      show ("y" : String) ≠ "x" by decide]
  cases b <;> cases F <;>
    simp [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb,
      memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith,
      memEvalExpr, evalExpr, hbb, hx, hy]

/-- Transfer for `add64` (any fuel): same pure shape as `add`, at width
    64 through `checkedAddI64`. -/
theorem memTransfer_add64 (F : Nat) (a b : BitVec 64)
    (_h : oracleNoalias add64Func [.i64 a, .i64 b]) :
    memEvalFuncFuel F add64Func [.i64 a, .i64 b] =
      evalFuncFuel F add64Func [.i64 a, .i64 b] := by
  have hbf : add64Func.args =
      [{ name := "a", ty := .i 64, role := .owned },
       { name := "b", ty := .i 64, role := .owned }] := rfl
  have hbody : add64Func.body =
      .return_ (.add (.var "a") (.var "b")) := rfl
  have hb : bindMemArgs
      [{ name := "a", ty := .i 64, role := .owned },
       { name := "b", ty := .i 64, role := .owned }]
      [.i64 a, .i64 b] emptyMem =
      some ([("a", .i64 a), ("b", .i64 b)], emptyMem, []) := rfl
  have ha : envLookup [("a", .i64 a), ("b", .i64 b)] "a" =
      some (.i64 a) := by simp [envLookup]
  have hbb : envLookup [("a", .i64 a), ("b", .i64 b)] "b" =
      some (.i64 b) := by
    simp [envLookup, show ("b" : String) ≠ "a" by decide]
  simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith, memEvalExpr, evalExpr,
      ha, hbb] <;>
    (cases h : checkedAddI64 a b <;> rfl)

/-- Transfer for `addu64` (any fuel): wrapping unsigned addition never
    fails, so both sides compute the sum directly. -/
theorem memTransfer_addu64 (F : Nat) (a b : BitVec 64)
    (_h : oracleNoalias addu64Func [.u64 a, .u64 b]) :
    memEvalFuncFuel F addu64Func [.u64 a, .u64 b] =
      evalFuncFuel F addu64Func [.u64 a, .u64 b] := by
  have hbf : addu64Func.args =
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }] := rfl
  have hbody : addu64Func.body =
      .return_ (.uadd (.var "a") (.var "b")) := rfl
  have hb : bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := rfl
  have ha : envLookup [("a", .u64 a), ("b", .u64 b)] "a" =
      some (.u64 a) := by simp [envLookup]
  have hbb : envLookup [("a", .u64 a), ("b", .u64 b)] "b" =
      some (.u64 b) := by
    simp [envLookup, show ("b" : String) ≠ "a" by decide]
  simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
  cases F <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith,
      memEvalExpr, evalExpr, ha, hbb]

/-- Transfer for `cls` (any fuel): the switch-as-if-chain is pure, so
    memory is untouched and both sides classify identically. -/
theorem memTransfer_cls (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias clsFunc [.u32 x]) :
    memEvalFuncFuel F clsFunc [.u32 x] =
      evalFuncFuel F clsFunc [.u32 x] := by
  have hbf : clsFunc.args =
      [{ name := "x", ty := .u 32, role := .owned }] := rfl
  have hbody : clsFunc.body =
      .if_ (.ueq (.var "x") (.lit (.u32 0)))
        (.return_ (.lit (.u32 10)))
        (.if_ (.ueq (.var "x") (.lit (.u32 1)))
          (.return_ (.lit (.u32 20)))
          (.return_ (.lit (.u32 30)))) := rfl
  have hb : bindMemArgs
      [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) := by
    simp [envLookup]
  by_cases h0 : x = 0
  · subst h0
    simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
    cases F <;>
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        evalStmtFuel, evalStmtZero, evalStmtWith,
        memEvalExpr, evalExpr, litVal, envLookup]
  · have h0' : x ≠ 0#32 := h0
    by_cases h1 : x = 1
    · subst h1
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup]
    · have h1' : x ≠ 1#32 := h1
      have e0 : (x == 0#32) = false := by simp [h0']
      have e1 : (x == 1#32) = false := by simp [h1']
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup, e0, e1]

/-- Transfer for `translate` (any fuel): field projection + checked
    adds + struct construction are all pure (the struct crosses by
    value), so memory rides alongside untouched. The `Eval` side reuses
    `evalFuncFuel_translate` + the `translateFwd` bridges; the memory
    side computes directly. -/
theorem memTransfer_translate (F : Nat) (px py dx dy : BitVec 32)
    (_h : oracleNoalias translateFunc
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy]) :
    memEvalFuncFuel F translateFunc
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
      evalFuncFuel F translateFunc
        [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] := by
  have hbf : translateFunc.args =
      [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned },
       { name := "dx", ty := .i 32, role := .owned },
       { name := "dy", ty := .i 32, role := .owned }] := rfl
  have hb : bindMemArgs
      [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned },
       { name := "dx", ty := .i 32, role := .owned },
       { name := "dy", ty := .i 32, role := .owned }]
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy]
      emptyMem =
      some ([("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)], emptyMem, []) := rfl
  have hbody : translateFunc.body =
      .seq (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
      (.seq (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
            (.return_ (.pmk (.var "qx") (.var "qy")))) := rfl
  have hp : envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "p" =
      some (.structVal "Point" [("x", px), ("y", py)]) := by
    simp [envLookup]
  have hdx : envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "dx" = some (.i32 dx) := by
    simp [envLookup, show ("dx" : String) ≠ "p" by decide]
  have hdy : envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "dy" = some (.i32 dy) := by
    simp [envLookup, show ("dy" : String) ≠ "p" by decide,
      show ("dy" : String) ≠ "dx" by decide]
  have hfx : fieldLookup [("x", px), ("y", py)] "x" = some px :=
    fieldLookup_translate_x px py
  have hfy : fieldLookup [("x", px), ("y", py)] "y" = some py :=
    fieldLookup_translate_y px py
  have haddx : memEvalExpr (.add (.fget "p" "x") (.var "dx"))
      [("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)] emptyMem [] =
      (checkedAddI32 px dx).map .i32 :=
    memEvalExpr_add_fget_var _ _ _ _ _ _ _ _ _ _ hp hfx hdx
  cases hx : checkedAddI32 px dx with
  | error e =>
    have haddx' : memEvalExpr (.add (.fget "p" "x") (.var "dx"))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] emptyMem [] = .error e := by
      rw [haddx, hx]
      exact i32_map_error e
    have hmem : memEvalFuncFuel F translateFunc
        [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
        .error e := by
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, haddx']
    have heval : evalFuncFuel F translateFunc
        [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
        .error e := by
      rw [evalFuncFuel_translate]
      exact translateFwd_err_x _ _ _ _ _ hx
    rw [hmem, heval]
  | ok x' =>
    have haddx' : memEvalExpr (.add (.fget "p" "x") (.var "dx"))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] emptyMem [] =
        .ok (.i32 x') := by
      rw [haddx, hx]
      exact i32_map_ok x'
    have hobj2 : envLookup (("qx", .i32 x') ::
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)]) "p" =
        some (.structVal "Point" [("x", px), ("y", py)]) := by
      simp [envLookup, show ("p" : String) ≠ "qx" by decide]
    have hvar2 : envLookup (("qx", .i32 x') ::
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)]) "dy" = some (.i32 dy) := by
      simp [envLookup, show ("dy" : String) ≠ "qx" by decide]
    have haddy : memEvalExpr (.add (.fget "p" "y") (.var "dy"))
        (("qx", .i32 x') ::
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)]) emptyMem [] =
        (checkedAddI32 py dy).map .i32 :=
      memEvalExpr_add_fget_var _ _ _ _ _ _ _ _ _ _ hobj2 hfy hvar2
    cases hy : checkedAddI32 py dy with
    | error e =>
      have haddy' : memEvalExpr (.add (.fget "p" "y") (.var "dy"))
          (("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) emptyMem [] =
          .error e := by
        rw [haddy, hy]
        exact i32_map_error e
      have hmem : memEvalFuncFuel F translateFunc
          [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
          .error e := by
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        cases F <;>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
            haddx', haddy']
      have heval : evalFuncFuel F translateFunc
          [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
          .error e := by
        rw [evalFuncFuel_translate]
        exact translateFwd_err_y _ _ _ _ _ _ hx hy
      rw [hmem, heval]
    | ok y' =>
      have haddy' : memEvalExpr (.add (.fget "p" "y") (.var "dy"))
          (("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) emptyMem [] =
          .ok (.i32 y') := by
        rw [haddy, hy]
        exact i32_map_ok y'
      have hqx : evalExpr (.var "qx")
          (("qy", .i32 y') :: ("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) = .ok (.i32 x') := by
        simp [evalExpr, envLookup, show ("qx" : String) ≠ "qy" by decide]
      have hqy : evalExpr (.var "qy")
          (("qy", .i32 y') :: ("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) = .ok (.i32 y') := by
        simp [evalExpr, envLookup]
      have hpmk : memEvalExpr (.pmk (.var "qx") (.var "qy"))
          (("qy", .i32 y') :: ("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) emptyMem [] =
          .ok (.structVal "Point" [("x", x'), ("y", y')]) := by
        have e1 : envLookup
            (("qy", .i32 y') :: ("qx", .i32 x') ::
            [("p", .structVal "Point" [("x", px), ("y", py)]),
              ("dx", .i32 dx), ("dy", .i32 dy)]) "qx" =
            some (.i32 x') := by
          simp [envLookup, show ("qx" : String) ≠ "qy" by decide]
        have e2 : envLookup
            (("qy", .i32 y') :: ("qx", .i32 x') ::
            [("p", .structVal "Point" [("x", px), ("y", py)]),
              ("dx", .i32 dx), ("dy", .i32 dy)]) "qy" =
            some (.i32 y') := by
          simp [envLookup]
        simp [memEvalExpr, e1, e2]
      have hmem : memEvalFuncFuel F translateFunc
          [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
          .ok (.structVal "Point" [("x", x'), ("y", y')]) := by
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        cases F <;>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
            haddx', haddy', hpmk]
      have heval : evalFuncFuel F translateFunc
          [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
          .ok (.structVal "Point" [("x", x'), ("y", y')]) := by
        rw [evalFuncFuel_translate]
        exact translateFwd_ok_bridge _ _ _ _ _ _ hx hy
      rw [hmem, heval]

/-! ## M3c flow transfers: `nested_sum`, `skip_sum` (scalar loops) -/

/-- Inner condition on memory reads `j` against `m` (pure, memory
    untouched — mirrors `nestedCondInner_eval`). -/
theorem memNestedCondInner_eval (nv mv : BitVec 32) (k t : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout) (h : t < 2 ^ 32) :
    memEvalExpr (.ult (.var "j") (.var "m")) (mkNestedEnv nv mv k acc t)
      m π =
      .ok (.b (decide (t < mv.toNat))) := by
  have hj := mkNestedEnv_j nv mv k acc t
  have hm := mkNestedEnv_m nv mv k acc t
  simp only [memEvalExpr, hj, hm, ofNat32_ult t mv h]

/-- Outer condition on memory reads `i` against `n` (pure — mirrors
    `nestedCondOuter_eval`). -/
theorem memNestedCondOuter_eval (nv mv : BitVec 32) (k t : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n")) (mkNestedEnv nv mv k acc t)
      m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkNestedEnv_i nv mv k acc t
  have hn := mkNestedEnv_n nv mv k acc t
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- One memory inner step advances `j` and accumulates `ofNat (k*t)`
    (any fuel: loop-free), with `Mem`/`Layout` untouched — mirrors
    `nestedBodyInner_eval`. -/
theorem memNestedBodyInner_eval (F : Nat) (nv mv : BitVec 32)
    (k t : Nat) (acc : BitVec 32) (m : Mem) (π : Layout) :
    memEvalStmtFuel F nestedBodyInner (mkNestedEnv nv mv k acc t) m π =
      .ok ((mkNestedEnv nv mv k
        (acc + BitVec.ofNat 32 (k * t)) (t + 1), m, π), .fellThrough) := by
  have hs : memEvalExpr (.uadd (.var "s") (.umul (.var "i") (.var "j")))
        (mkNestedEnv nv mv k acc t) m π =
        .ok (.u32 (acc + BitVec.ofNat 32 (k * t))) := by
    have h1 := mkNestedEnv_s nv mv k acc t
    have hii := mkNestedEnv_i nv mv k acc t
    have hj := mkNestedEnv_j nv mv k acc t
    simp only [memEvalExpr, h1, hii, hj, ofNat32_mul]
  have hj2 : memEvalExpr (.uadd (.var "j") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkNestedEnv nv mv k (acc + BitVec.ofNat 32 (k * t)) t) m π =
        .ok (.u32 (BitVec.ofNat 32 (t + 1))) := by
    have hj := mkNestedEnv_j nv mv k (acc + BitVec.ofNat 32 (k * t)) t
    simp only [memEvalExpr, litVal, hj, ofNat32_add_one]
  have up1 := nestedEnv_update_s nv mv k t acc
    (acc + BitVec.ofNat 32 (k * t))
  have up2 := nestedEnv_update_j nv mv k t (t + 1)
    (acc + BitVec.ofNat 32 (k * t))
  cases F <;>
    simp only [nestedBodyInner, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hs, hj2, up1, up2]

/-- Memory inner loop correctness: folds the row suffix, leaving
    `Mem`/`Layout` untouched — mirrors `nestedInner_correct`. -/
theorem memNestedInner_correct (nv mv : BitVec 32)
    (F k t : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (ht32 : t ≤ mv.toNat) (ht2 : t < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : mv.toNat - t ≤ F) :
    memEvalStmtFuel F nestedInner (mkNestedEnv nv mv k acc t) m π =
      .ok (((mkNestedEnv nv mv k
        (acc + rowSuffixU32 k t mv.toNat) mv.toNat, m, π)),
        .fellThrough) := by
  induction F generalizing t acc with
  | zero =>
    have htt : t = mv.toNat := by omega
    subst htt
    have hcond : memEvalExpr (.ult (.var "j") (.var "m"))
          (mkNestedEnv nv mv k acc mv.toNat) m π = .ok (.b false) := by
      simpa using
        (memNestedCondInner_eval nv mv k mv.toNat acc m π
          (by omega : mv.toNat < 2 ^ 32))
    have hnil := rowSuffix_nil k mv.toNat
    simp [nestedInner, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith, hcond, hnil,
      BitVec.add_zero]
  | succ F ih =>
    by_cases hlt : t < mv.toNat
    · have hcond : memEvalExpr (.ult (.var "j") (.var "m"))
          (mkNestedEnv nv mv k acc t) m π = .ok (.b true) := by
        simpa [hlt] using (memNestedCondInner_eval nv mv k t acc m π ht2)
      have hbody := memNestedBodyInner_eval F nv mv k t acc m π
      have hstep : memEvalStmtFuel (F + 1) nestedInner
            (mkNestedEnv nv mv k acc t) m π
          = memEvalStmtFuel F nestedInner
            (mkNestedEnv nv mv k (acc + BitVec.ofNat 32 (k * t)) (t + 1))
            m π := by
        simp [nestedInner, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hrec := ih (t + 1) (acc + BitVec.ofNat 32 (k * t))
        (by omega) (by omega) (by omega)
      rw [hrec]
      have hrow := rowSuffix_step k t mv.toNat hlt
      have hacc : (acc + BitVec.ofNat 32 (k * t)) +
            rowSuffixU32 k (t + 1) mv.toNat
          = acc + rowSuffixU32 k t mv.toNat := by
        rw [hrow]; exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have htt : t = mv.toNat := by omega
      subst htt
      have hcond : memEvalExpr (.ult (.var "j") (.var "m"))
            (mkNestedEnv nv mv k acc mv.toNat) m π = .ok (.b false) := by
        simpa using
          (memNestedCondInner_eval nv mv k mv.toNat acc m π
            (by omega : mv.toNat < 2 ^ 32))
      have hnil := rowSuffix_nil k mv.toNat
      simp [nestedInner, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil, BitVec.add_zero]

/-- Memory outer body: run the inner loop, step `i`, reset `j` —
    mirrors `nestedBodyOuter_eval` (one inner fact covers all fuels). -/
theorem memNestedBodyOuter_eval (F : Nat) (nv mv : BitVec 32)
    (k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hmF : mv.toNat ≤ F)
    (hm32 : mv.toNat < 2 ^ 32) :
    memEvalStmtFuel F nestedBodyOuter (mkNestedEnv nv mv k acc 0) m π =
      .ok (((mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) 0,
        m, π)), .fellThrough) := by
  have hinner : memEvalStmtFuel F nestedInner (mkNestedEnv nv mv k acc 0)
        m π =
        .ok (((mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
          m, π)), .fellThrough) := by
    have h := memNestedInner_correct nv mv F k 0 acc m π
      (Nat.zero_le _) (by omega) hm32 (by omega)
    rwa [rowSuffix_full] at h
  have hincr : memEvalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat) m π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have hii := mkNestedEnv_i nv mv k (acc + rowU32 k mv.toNat) mv.toNat
    simp only [memEvalExpr, litVal, hii, ofNat32_add_one]
  have up1 := nestedEnv_update_i nv mv k (k + 1) mv.toNat
    (acc + rowU32 k mv.toNat)
  have hreset : memEvalExpr (.lit (.u32 (BitVec.ofNat 32 0)))
        (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) mv.toNat)
        m π =
        .ok (.u32 (BitVec.ofNat 32 0)) := rfl
  have up0 := nestedEnv_update_j nv mv (k + 1) mv.toNat 0
    (acc + rowU32 k mv.toNat)
  cases F with
  | zero =>
    have hinner0 : memEvalStmtWith memEvalStmtZeroHandler
          nestedInner (mkNestedEnv nv mv k acc 0) m π =
          .ok (((mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
            m, π)), .fellThrough) := hinner
    simp [nestedBodyOuter, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hinner0, hincr, up1, hreset, up0]
  | succ F =>
    have hinnerS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          nestedInner (mkNestedEnv nv mv k acc 0) m π =
          .ok (((mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
            m, π)), .fellThrough) := hinner
    simp [nestedBodyOuter, memEvalStmtFuel, memEvalStmtWith,
      hinnerS, hincr, up1, hreset, up0]

/-- Memory outer loop correctness: folds the nest suffix — mirrors
    `nestedOuter_correct` (one outer iteration costs `m+1` fuel). -/
theorem memNestedOuter_correct (nv mv : BitVec 32)
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hk : k ≤ nv.toNat) (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : (nv.toNat - k) * (mv.toNat + 1) ≤ F) :
    memEvalStmtFuel F nestedOuter (mkNestedEnv nv mv k acc 0) m π =
      .ok (((mkNestedEnv nv mv nv.toNat
        (acc + nestSuffixU32 k nv.toNat mv.toNat) 0, m, π)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by
      have hpos : 0 < nv.toNat - k ∨ k = nv.toNat := by omega
      rcases hpos with hpos | hkk
      · have hge := Nat.le_mul_of_pos_left (mv.toNat + 1) hpos
        omega
      · exact hkk
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkNestedEnv nv mv nv.toNat acc 0) m π = .ok (.b false) := by
      simpa using (memNestedCondOuter_eval nv mv nv.toNat 0 acc m π hn)
    have hnil := nestSuffix_nil nv.toNat nv.toNat mv.toNat (Nat.le_refl _)
    simp [nestedOuter, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith, hcond, hnil,
      BitVec.add_zero]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkNestedEnv nv mv k acc 0) m π = .ok (.b true) := by
        simpa [hlt] using (memNestedCondOuter_eval nv mv k 0 acc m π hk32)
      have hbody := memNestedBodyOuter_eval F nv mv k acc m π
        (by have hge := Nat.le_mul_of_pos_left (mv.toNat + 1)
              (show 0 < nv.toNat - k by omega)
            omega)
        hm
      have hstep : memEvalStmtFuel (F + 1) nestedOuter
            (mkNestedEnv nv mv k acc 0) m π
          = memEvalStmtFuel F nestedOuter
            (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) 0) m π := by
        simp [nestedOuter, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hsplit : (nv.toNat - k) * (mv.toNat + 1)
          = (nv.toNat - (k + 1)) * (mv.toNat + 1) + (mv.toNat + 1) := by
        have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
        rw [hkk1, Nat.add_mul, Nat.one_mul]
      have hrec := ih (k + 1) (acc + rowU32 k mv.toNat)
        (by omega)
        (show (nv.toNat - (k + 1)) * (mv.toNat + 1) ≤ F by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hnest := nestSuffix_step k nv.toNat mv.toNat hlt
      have hacc : (acc + rowU32 k mv.toNat) +
            nestSuffixU32 (k + 1) nv.toNat mv.toNat
          = acc + nestSuffixU32 k nv.toNat mv.toNat := by
        rw [hnest]; exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkNestedEnv nv mv nv.toNat acc 0) m π = .ok (.b false) := by
        simpa using (memNestedCondOuter_eval nv mv nv.toNat 0 acc m π hn)
      have hnil := nestSuffix_nil nv.toNat nv.toNat mv.toNat (Nat.le_refl _)
      simp [nestedOuter, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil, BitVec.add_zero]

/-- `memEval` for `nested_sum`, fuel-generalized — mirrors
    `evalFuncFuel_nested` (memory rides alongside, untouched). -/
theorem memEvalFuncFuel_nested (F : Nat) (nv mv : BitVec 32)
    (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : nv.toNat * (mv.toNat + 1) ≤ F) :
    memEvalFuncFuel F nestedFunc [.u32 nv, .u32 mv] = nestedFwd nv mv := by
  have hbf : nestedFunc.args =
      [{ name := "n", ty := .u 32, role := .owned },
       { name := "m", ty := .u 32, role := .owned }] := rfl
  have hbody : nestedFunc.body =
      .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "j" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq nestedOuter
            (.return_ (.var "s"))))) := rfl
  have hb : bindMemArgs
      [{ name := "n", ty := .u 32, role := .owned },
       { name := "m", ty := .u 32, role := .owned }]
      [.u32 nv, .u32 mv] emptyMem =
      some ([("n", .u32 nv), ("m", .u32 mv)], emptyMem, []) := rfl
  have henv : [("j", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("n", .u32 nv), ("m", .u32 mv)]
      = mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0 := rfl
  have hfull := nestSuffix_full nv.toNat mv.toNat
  have hsret : envLookup
        (mkNestedEnv nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0)
        "s" = some (.u32 (nestedSumU32 nv.toNat mv.toNat)) :=
    mkNestedEnv_s nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0
  have hret : memEvalExpr (.var "s")
      (mkNestedEnv nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0)
      emptyMem [] = .ok (.u32 (nestedSumU32 nv.toNat mv.toNat)) := by
    simp [memEvalExpr, hsret]
  cases F with
  | zero =>
    have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
          nestedOuter (mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0)
          emptyMem [] =
        .ok (((mkNestedEnv nv mv nv.toNat
            (BitVec.ofNat 32 0 + nestSuffixU32 0 nv.toNat mv.toNat) 0,
            emptyMem, [])), .fellThrough) :=
      memNestedOuter_correct nv mv 0 0 (BitVec.ofNat 32 0) emptyMem []
        (Nat.zero_le _) hn hm (by omega)
    simp only [memEvalFuncFuel, hbf, hbody, hb]
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
      litVal, nestedFwd, henv, hloopH0, hsret, hfull, BitVec.zero_add]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          nestedOuter (mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0)
          emptyMem [] =
        .ok (((mkNestedEnv nv mv nv.toNat
            (BitVec.ofNat 32 0 + nestSuffixU32 0 nv.toNat mv.toNat) 0,
            emptyMem, [])), .fellThrough) :=
      memNestedOuter_correct nv mv (F + 1) 0 (BitVec.ofNat 32 0) emptyMem []
        (Nat.zero_le _) hn hm (by omega)
    simp only [memEvalFuncFuel, hbf, hbody, hb]
    simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr, litVal, nestedFwd,
      henv, hloopS, hsret, hfull, BitVec.zero_add]

/-- Transfer for `nested_sum`: both sides equal `nestedFwd`. -/
theorem memTransfer_nested (F : Nat) (nv mv : BitVec 32)
    (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : nv.toNat * (mv.toNat + 1) ≤ F)
    (_h : oracleNoalias nestedFunc [.u32 nv, .u32 mv]) :
    memEvalFuncFuel F nestedFunc [.u32 nv, .u32 mv] =
      evalFuncFuel F nestedFunc [.u32 nv, .u32 mv] := by
  rw [memEvalFuncFuel_nested F nv mv hn hm hF,
    evalFuncFuel_nested F nv mv hn hm hF]

/-- Memory loop condition reads the index against the bound — mirrors
    `skipCond_eval` (pure). -/
theorem memSkipCond_eval (nv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n")) (mkSkipEnv nv k acc) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSkipEnv_i nv k acc
  have hn := mkSkipEnv_n nv k acc
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- Memory `ueq` against a const decides `Nat` equality — mirrors
    `skipCond_eq` (pure). -/
theorem memSkipCond_eq (nv : BitVec 32) (k c : Nat) (acc : BitVec 32)
    (m : Mem) (π : Layout) (hk : k < 2 ^ 32) (hc : c < 2 ^ 32) :
    memEvalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 c))))
      (mkSkipEnv nv k acc) m π = .ok (.b (decide (k = c))) := by
  have hi := mkSkipEnv_i nv k acc
  simp only [memEvalExpr, hi, litVal, ofNat32_beq k c hk hc]

/-- Memory body at `k = 2`: increment, signal `continued` (any fuel) —
    mirrors `skipBody_continue`. -/
theorem memSkipBody_continue (F : Nat) (nv : BitVec 32) (acc : BitVec 32)
    (m : Mem) (π : Layout) :
    memEvalStmtFuel F skipBody (mkSkipEnv nv 2 acc) m π =
      .ok (((mkSkipEnv nv 3 acc, m, π)), .continued) := by
  have hcond1 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv 2 acc) m π = .ok (.b true) := by
    simpa using (memSkipCond_eq nv 2 2 acc m π (by decide) (by decide))
  have hincr : memEvalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkSkipEnv nv 2 acc) m π = .ok (.u32 (BitVec.ofNat 32 3)) := by
    have hi := mkSkipEnv_i nv 2 acc
    have h3 : BitVec.ofNat 32 2 + BitVec.ofNat 32 1
        = BitVec.ofNat 32 3 :=
      ofNat32_add_one 2
    simp only [memEvalExpr, litVal, hi, h3]
  have upi := skipEnv_update_i nv 2 3 acc
  cases F <;>
    simp [skipBody, skipContBranch, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hcond1, hincr, upi]

/-- Memory body at `k = 8`: signal `broke`, env untouched (any fuel) —
    mirrors `skipBody_break`. -/
theorem memSkipBody_break (F : Nat) (nv : BitVec 32) (acc : BitVec 32)
    (m : Mem) (π : Layout) :
    memEvalStmtFuel F skipBody (mkSkipEnv nv 8 acc) m π =
      .ok (((mkSkipEnv nv 8 acc, m, π)), .broke) := by
  have hcond1 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv 8 acc) m π = .ok (.b false) := by
    have h := memSkipCond_eq nv 8 2 acc m π (by decide) (by decide)
    simpa using h
  have hcond2 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
        (mkSkipEnv nv 8 acc) m π = .ok (.b true) := by
    simpa using (memSkipCond_eq nv 8 8 acc m π (by decide) (by decide))
  cases F <;>
    simp [skipBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hcond1, hcond2]

/-- Memory body elsewhere: accumulate and step (any fuel) — mirrors
    `skipBody_step`. -/
theorem memSkipBody_step (F : Nat) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout)
    (hne2 : k ≠ 2) (hne8 : k ≠ 8) (hk32 : k < 2 ^ 32) :
    memEvalStmtFuel F skipBody (mkSkipEnv nv k acc) m π =
      .ok (((mkSkipEnv nv (k + 1) (acc + BitVec.ofNat 32 k), m, π)),
        .fellThrough) := by
  have hcond1 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv k acc) m π = .ok (.b false) := by
    have h := memSkipCond_eq nv k 2 acc m π hk32 (by decide)
    simpa [hne2] using h
  have hcond2 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
        (mkSkipEnv nv k acc) m π = .ok (.b false) := by
    have h := memSkipCond_eq nv k 8 acc m π hk32 (by decide)
    simpa [hne8] using h
  have hs : memEvalExpr (.uadd (.var "s") (.var "i"))
        (mkSkipEnv nv k acc) m π = .ok (.u32 (acc + BitVec.ofNat 32 k)) := by
    have h1 := mkSkipEnv_s nv k acc
    have hii := mkSkipEnv_i nv k acc
    simp only [memEvalExpr, h1, hii]
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkSkipEnv nv k (acc + BitVec.ofNat 32 k)) m π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSkipEnv_i nv k (acc + BitVec.ofNat 32 k)
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up1 := skipEnv_update_s nv k acc (acc + BitVec.ofNat 32 k)
  have up2 := skipEnv_update_i nv k (k + 1) (acc + BitVec.ofNat 32 k)
  cases F <;>
    simp [skipBody, skipTail, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hcond1, hcond2, hs, hi2, up1, up2]

/-- Memory loop correctness: folds the skip suffix, exits with
    `i = min n 8` — mirrors `skipWhile_correct`. -/
theorem memSkipWhile_correct (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hk : k ≤ min nv.toNat 8)
    (hF : min nv.toNat 8 - k + 1 ≤ F) :
    memEvalStmtFuel F skipWhile (mkSkipEnv nv k acc) m π =
      .ok (((mkSkipEnv nv (min nv.toNat 8)
        (acc + skipSuffixU32 k (min nv.toNat 8)), m, π)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · by_cases h2 : k = 2
      · subst h2
        have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
              (mkSkipEnv nv 2 acc) m π = .ok (.b true) := by
          have hk32 : (2 : Nat) < 2 ^ 32 := by decide
          simpa [hlt] using (memSkipCond_eval nv 2 acc m π hk32)
        have hbody := memSkipBody_continue F nv acc m π
        have hstep : memEvalStmtFuel (F + 1) skipWhile (mkSkipEnv nv 2 acc)
              m π
            = memEvalStmtFuel F skipWhile (mkSkipEnv nv 3 acc) m π := by
          simp [skipWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep]
        have hrec := ih 3 acc (by omega) (by omega)
        rw [hrec]
        have hskip := skipSuffix_skip2 (min nv.toNat 8) (by omega)
        have hacc : acc + skipSuffixU32 3 (min nv.toNat 8)
            = acc + skipSuffixU32 2 (min nv.toNat 8) := by
          rw [hskip]
        rw [hacc]
      · by_cases h8 : k = 8
        · subst h8
          have he : min nv.toNat 8 = 8 := by omega
          have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
                (mkSkipEnv nv 8 acc) m π = .ok (.b true) := by
            have hk32 : (8 : Nat) < 2 ^ 32 := by decide
            simpa [hlt] using (memSkipCond_eval nv 8 acc m π hk32)
          have hbody := memSkipBody_break F nv acc m π
          have hnil8 := skipSuffix_nil 8 8 (Nat.le_refl 8)
          simp [skipWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody, he, hnil8, BitVec.add_zero]
        · have hk32 : k < 2 ^ 32 := by omega
          have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
                (mkSkipEnv nv k acc) m π = .ok (.b true) := by
            simpa [hlt] using (memSkipCond_eval nv k acc m π hk32)
          have hbody := memSkipBody_step F nv k acc m π h2 h8 hk32
          have hstep : memEvalStmtFuel (F + 1) skipWhile (mkSkipEnv nv k acc)
                m π
              = memEvalStmtFuel F skipWhile
                (mkSkipEnv nv (k + 1) (acc + BitVec.ofNat 32 k)) m π := by
            simp [skipWhile, memEvalStmtFuel, memEvalSuccHandler,
              memEvalStmtWith, hcond, hbody]
          rw [hstep]
          have hrec := ih (k + 1) (acc + BitVec.ofNat 32 k)
            (by omega) (by omega)
          rw [hrec]
          have hlt' : k < min nv.toNat 8 := by omega
          have hstep' := skipSuffix_step k (min nv.toNat 8) hlt' h2
          have hacc : (acc + BitVec.ofNat 32 k) +
                skipSuffixU32 (k + 1) (min nv.toNat 8)
              = acc + skipSuffixU32 k (min nv.toNat 8) := by
            rw [hstep']; exact BitVec.add_assoc _ _ _
          rw [hacc]
    · have hkk : k = min nv.toNat 8 := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkSkipEnv nv (min nv.toNat 8) acc) m π = .ok (.b false) := by
        have hfalse : (decide (min nv.toNat 8 < nv.toNat)) = false := by
          have : ¬ min nv.toNat 8 < nv.toNat := by omega
          simp [this]
        have hk32 : min nv.toNat 8 < 2 ^ 32 := by omega
        have h := memSkipCond_eval nv (min nv.toNat 8) acc m π hk32
        rwa [hfalse] at h
      have hnil := skipSuffix_nil (min nv.toNat 8) (min nv.toNat 8)
        (Nat.le_refl _)
      simp [skipWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil, BitVec.add_zero]

/-- `memEval` for `skip_sum`, fuel-generalized — mirrors
    `evalFuncFuel_skip`. -/
theorem memEvalFuncFuel_skip (F : Nat) (nv : BitVec 32)
    (hF : min nv.toNat 8 + 1 ≤ F) :
    memEvalFuncFuel F skipFunc [.u32 nv] = skipFwd nv := by
  have hbf : skipFunc.args =
      [{ name := "n", ty := .u 32, role := .owned }] := rfl
  have hbody : skipFunc.body =
      .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq skipWhile
            (.return_ (.var "s")))) := rfl
  have hb : bindMemArgs
      [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := rfl
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("n", .u32 nv)]
      = mkSkipEnv nv 0 (BitVec.ofNat 32 0) := rfl
  have hfull := skipSuffix_full nv.toNat
  have hsret : envLookup
        (mkSkipEnv nv (min nv.toNat 8) (skipSumU32 nv.toNat)) "s" =
        some (.u32 (skipSumU32 nv.toNat)) :=
    mkSkipEnv_s nv (min nv.toNat 8) (skipSumU32 nv.toNat)
  cases F with
  | zero =>
    have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
          skipWhile (mkSkipEnv nv 0 (BitVec.ofNat 32 0))
          emptyMem [] =
        .ok (((mkSkipEnv nv (min nv.toNat 8)
            (BitVec.ofNat 32 0 + skipSuffixU32 0 (min nv.toNat 8)),
            emptyMem, [])), .fellThrough) :=
      memSkipWhile_correct nv 0 0 (BitVec.ofNat 32 0) emptyMem []
        (Nat.zero_le _) (by omega)
    simp only [memEvalFuncFuel, hbf, hbody, hb]
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
      litVal, skipFwd, henv, hloopH0, hsret, hfull, BitVec.zero_add]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          skipWhile (mkSkipEnv nv 0 (BitVec.ofNat 32 0))
          emptyMem [] =
        .ok (((mkSkipEnv nv (min nv.toNat 8)
            (BitVec.ofNat 32 0 + skipSuffixU32 0 (min nv.toNat 8)),
            emptyMem, [])), .fellThrough) :=
      memSkipWhile_correct nv (F + 1) 0 (BitVec.ofNat 32 0) emptyMem []
        (Nat.zero_le _) (by omega)
    simp only [memEvalFuncFuel, hbf, hbody, hb]
    simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr,
      litVal, skipFwd, henv, hloopS, hsret, hfull, BitVec.zero_add]

/-- Transfer for `skip_sum`: both sides equal `skipFwd`. -/
theorem memTransfer_skip (F : Nat) (nv : BitVec 32)
    (hF : min nv.toNat 8 + 1 ≤ F)
    (_h : oracleNoalias skipFunc [.u32 nv]) :
    memEvalFuncFuel F skipFunc [.u32 nv] =
      evalFuncFuel F skipFunc [.u32 nv] := by
  rw [memEvalFuncFuel_skip F nv hF, evalFuncFuel_skip F nv hF]

/-! ## M3c flow transfer: `find_eq` (single-block stride search) -/

/-- Memory loop condition reads the index against the bound (pure —
    mirrors `findCond_eval`). -/
theorem memFindCond_eval (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (m : Mem) (π : Layout) (h : t < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n")) (mkFindEnv l nv kv t) m π =
      .ok (.b (decide (t < nv.toNat))) := by
  have hi := mkFindEnv_i l nv kv t
  have hn := mkFindEnv_n l nv kv t
  simp only [memEvalExpr, hi, hn, ofNat32_ult t nv h]

/-- Memory body on match: return the index (any fuel) — mirrors
    `findBody_hit` (the `idx` read cross-checks memory against the
    value list, as in `memSumBody_eval`). -/
theorem memFindBody_hit (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (x : BitVec 32) (m : Mem) (π : Layout)
    (hget : l[t]? = some x) (heq : x = kv) (ht32 : t < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalStmtFuel F findBody (mkFindEnv l nv kv t) m π =
      .ok (((mkFindEnv l nv kv t, m, π)),
        .returned (.u32 (BitVec.ofNat 32 t))) := by
  have hkk : (BitVec.ofNat 32 t).toNat = t := ofNat32_toNat t ht32
  have ha := mkFindEnv_a l nv kv t
  have hii := mkFindEnv_i l nv kv t
  have hload : memLoad m 0 0 (BitVec.ofNat 32 t).toNat = .ok x := by
    rw [hkk]
    exact memLoad_hit m 0 0 t ⟨0, true, l⟩ x hmem rfl rfl hget
  have hget' : l[(BitVec.ofNat 32 t).toNat]? = some x := by
    rw [hkk]; exact hget
  have hidx : memEvalExpr (.idx "a" (.var "i")) (mkFindEnv l nv kv t) m π =
        .ok (.u32 x) := by
    simp only [memEvalExpr, hlay, ha, hii, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hk := mkFindEnv_k l nv kv t
  have hcond : memEvalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv t) m π = .ok (.b true) := by
    simp only [memEvalExpr, hlay, ha, hii, hload, hget', hk, heq,
      beq_self_eq_true, ↓reduceIte]
  have hret : memEvalExpr (.var "i") (mkFindEnv l nv kv t) m π =
        .ok (.u32 (BitVec.ofNat 32 t)) := by
    simp [memEvalExpr, hii]
  cases F <;>
    simp [findBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hcond, hret]

/-- Memory body on miss: step the index (any fuel) — mirrors
    `findBody_miss`. -/
theorem memFindBody_miss (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (m : Mem) (π : Layout)
    (hmiss : ∀ x, l[t]? = some x → x ≠ kv)
    (htlen : t < l.length) (ht32 : t < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalStmtFuel F findBody (mkFindEnv l nv kv t) m π =
      .ok (((mkFindEnv l nv kv (t + 1), m, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 t).toNat = t := ofNat32_toNat t ht32
  have hget : l[t]? = some l[t] := List.getElem?_eq_getElem htlen
  have hne : l[t] ≠ kv := hmiss _ hget
  have ha := mkFindEnv_a l nv kv t
  have hii := mkFindEnv_i l nv kv t
  have hload : memLoad m 0 0 (BitVec.ofNat 32 t).toNat = .ok l[t] := by
    rw [hkk]
    exact memLoad_hit m 0 0 t ⟨0, true, l⟩ l[t] hmem rfl rfl hget
  have hget' : l[(BitVec.ofNat 32 t).toNat]? = some l[t] := by
    rw [hkk]; exact hget
  have hidx : memEvalExpr (.idx "a" (.var "i")) (mkFindEnv l nv kv t) m π =
        .ok (.u32 l[t]) := by
    simp only [memEvalExpr, hlay, ha, hii, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hk := mkFindEnv_k l nv kv t
  have hcond : memEvalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv t) m π = .ok (.b false) := by
    simp only [memEvalExpr, hlay, ha, hii, hload, hget', hk,
      beq_self_eq_true, ↓reduceIte]
    simp [hne]
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkFindEnv l nv kv t) m π =
        .ok (.u32 (BitVec.ofNat 32 (t + 1))) := by
    simp only [memEvalExpr, litVal, hii, ofNat32_add_one]
  have up := findEnv_update_i l nv kv t (t + 1)
  cases F <;>
    simp [findBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hcond, hi2, up]

/-- Memory body past the end: the index read fails `OOB` (any fuel) —
    mirrors `findBody_oob` (memory bounds fail in lockstep: block data
    = value words). -/
theorem memFindBody_oob (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (m : Mem) (π : Layout)
    (hlen32 : l.length < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalStmtFuel F findBody (mkFindEnv l nv kv l.length) m π =
      .error .OOB := by
  have hkk : (BitVec.ofNat 32 l.length).toNat = l.length :=
    ofNat32_toNat _ hlen32
  have hget : l[l.length]? = none :=
    List.getElem?_eq_none (Nat.le_refl _)
  have ha := mkFindEnv_a l nv kv l.length
  have hii := mkFindEnv_i l nv kv l.length
  have hload : memLoad m 0 0 (BitVec.ofNat 32 l.length).toNat =
      .error .OOB := by
    rw [hkk]
    simp [memLoad, hmem]
  have herr : memEvalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv l.length) m π = .error .OOB := by
    have hget' : l[(BitVec.ofNat 32 l.length).toNat]? = none := by
      rw [hkk]; exact hget
    simp only [memEvalExpr, hlay, ha, hii, hload, hget']
  cases F <;>
    simp [findBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, herr]

/-- Memory loop correctness, hit — mirrors `findWhile_some`. -/
theorem memFindWhile_some (l : List (BitVec 32)) (nv kv : BitVec 32)
    (F t j : Nat) (m : Mem) (π : Layout)
    (htm : t ≤ min nv.toNat l.length)
    (h32n : nv.toNat < 2 ^ 32)
    (hF : min nv.toNat l.length - t + 1 ≤ F)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩)
    (hfind : findSuffixU32 l t (min nv.toNat l.length) kv = some j) :
    memEvalStmtFuel F findWhile (mkFindEnv l nv kv t) m π =
      .ok (((mkFindEnv l nv kv j, m, π)),
        .returned (.u32 (BitVec.ofNat 32 j))) := by
  induction F generalizing t j with
  | zero => omega
  | succ F ih =>
    by_cases hlt : t < min nv.toNat l.length
    · have htn : t < nv.toNat := by omega
      have htl : t < l.length := by omega
      have ht32 : t < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkFindEnv l nv kv t) m π = .ok (.b true) := by
        simpa [htn] using (memFindCond_eval l nv kv t m π ht32)
      match hget : l[t]? with
      | some x =>
        by_cases heq : x = kv
        · have hbody := memFindBody_hit F l nv kv t x m π hget heq ht32
            hlay hmem
          have hfound := findSuffix_hit l t (min nv.toNat l.length) kv x
            hget heq hlt
          have hjt : t = j := by
            rw [hfound] at hfind
            exact Option.some_inj.mp hfind
          have hstep : memEvalStmtFuel (F + 1) findWhile
                (mkFindEnv l nv kv t) m π
              = .ok (((mkFindEnv l nv kv t, m, π)),
                .returned (.u32 (BitVec.ofNat 32 t))) := by
            simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
              memEvalStmtWith, hcond, hbody]
          rw [← hjt]
          exact hstep
        · have hmiss : ∀ y, l[t]? = some y → y ≠ kv := by
            intro y hy
            rw [hget] at hy
            cases hy
            exact heq
          have hbody := memFindBody_miss F l nv kv t m π hmiss htl ht32
            hlay hmem
          have htail := findSuffix_miss l t (min nv.toNat l.length) kv
            hmiss hlt
          have hstep : memEvalStmtFuel (F + 1) findWhile
                (mkFindEnv l nv kv t) m π
              = memEvalStmtFuel F findWhile (mkFindEnv l nv kv (t + 1))
                m π := by
            simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
              memEvalStmtWith, hcond, hbody]
          rw [hstep]
          rw [htail] at hfind
          exact ih (t + 1) j (by omega) (by omega) hfind
      | none =>
        have hsome : l[t]? = some l[t] := List.getElem?_eq_getElem htl
        rw [hsome] at hget
        simp at hget
    · have htt : t = min nv.toNat l.length := by omega
      subst htt
      have hnil := findSuffix_nil l (min nv.toNat l.length) kv
      rw [hnil] at hfind
      simp at hfind

/-- Memory loop correctness, miss — mirrors `findWhile_none`. -/
theorem memFindWhile_none (l : List (BitVec 32)) (nv kv : BitVec 32)
    (F t : Nat) (m : Mem) (π : Layout)
    (htm : t ≤ min nv.toNat l.length)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length - t + 1 ≤ F)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩)
    (hfind : findSuffixU32 l t (min nv.toNat l.length) kv = none) :
    memEvalStmtFuel F findWhile (mkFindEnv l nv kv t) m π =
      if decide (nv.toNat ≤ l.length) then
        .ok (((mkFindEnv l nv kv nv.toNat, m, π)), .fellThrough)
      else .error .OOB := by
  induction F generalizing t with
  | zero => omega
  | succ F ih =>
    by_cases hlt : t < min nv.toNat l.length
    · have htn : t < nv.toNat := by omega
      have htl : t < l.length := by omega
      have ht32 : t < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkFindEnv l nv kv t) m π = .ok (.b true) := by
        simpa [htn] using (memFindCond_eval l nv kv t m π ht32)
      have hget : l[t]? = some l[t] := List.getElem?_eq_getElem htl
      by_cases heq : l[t] = kv
      · exfalso
        have hfound := findSuffix_hit l t (min nv.toNat l.length) kv l[t]
          hget heq hlt
        rw [hfound] at hfind
        simp at hfind
      · have hmiss : ∀ y, l[t]? = some y → y ≠ kv := by
          intro y hy
          rw [hget] at hy
          cases hy
          exact heq
        have hbody := memFindBody_miss F l nv kv t m π hmiss htl ht32
          hlay hmem
        have htail := findSuffix_miss l t (min nv.toNat l.length) kv
          hmiss hlt
        have hstep : memEvalStmtFuel (F + 1) findWhile
              (mkFindEnv l nv kv t) m π
            = memEvalStmtFuel F findWhile (mkFindEnv l nv kv (t + 1))
              m π := by
          simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep]
        rw [htail] at hfind
        exact ih (t + 1) (by omega) (by omega) hfind
    · have htt : t = min nv.toNat l.length := by omega
      by_cases hnlen : nv.toNat ≤ l.length
      · have htn : t = nv.toNat := by omega
        subst htn
        have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
              (mkFindEnv l nv kv nv.toNat) m π = .ok (.b false) := by
          simpa using (memFindCond_eval l nv kv nv.toNat m π h32n)
        have htrue : (decide (nv.toNat ≤ l.length)) = true := by
          simp [hnlen]
        simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, htrue]
      · have htl2 : t = l.length := by omega
        subst htl2
        have hlt' : l.length < nv.toNat := by omega
        have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
              (mkFindEnv l nv kv l.length) m π = .ok (.b true) := by
          simpa [hlt'] using (memFindCond_eval l nv kv l.length m π h32l)
        have hbody := memFindBody_oob F l nv kv m π h32l hlay hmem
        have hfalse : (decide (nv.toNat ≤ l.length)) = false := by
          simp [hnlen]
        simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody, hfalse]

/-- `memEval` for `find_eq`, fuel-generalized — mirrors
    `evalFuncFuel_find` (memory rides alongside the singleton block). -/
theorem memEvalFuncFuel_findEq (F : Nat) (l : List (BitVec 32))
    (nv kv : BitVec 32)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length + 1 ≤ F) :
    memEvalFuncFuel F findEqFunc [.arr32 l, .u32 nv, .u32 kv] =
      findEqFwd l nv kv := by
  have hbf : findEqFunc.args =
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned },
       { name := "k", ty := .u 32, role := .owned }] := rfl
  have hbody : findEqFunc.body =
      .seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq findWhile
            (.return_ (.var "n"))) := rfl
  have hb := bindMemArgs_findEq l nv kv
  have hlay : layoutLookup [("a", 0, 0)] "a" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memFind ⟨1, [(0, ⟨0, true, l⟩)]⟩ 0 =
      some ⟨0, true, l⟩ := by
    simp [memFind]
  have henv : [("i", .u32 (BitVec.ofNat 32 0)), ("a", .arr32 l),
        ("n", .u32 nv), ("k", .u32 kv)]
      = mkFindEnv l nv kv 0 := rfl
  have hbridge := findSuffix_zero_idx l nv.toNat kv
  match hfi : findIdxU32 l nv.toNat kv with
  | some j =>
    have hloop : ∀ (G : Nat),
        min nv.toNat l.length + 1 ≤ G →
        memEvalStmtFuel G findWhile (mkFindEnv l nv kv 0)
          ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] =
          .ok (((mkFindEnv l nv kv j, ⟨1, [(0, ⟨0, true, l⟩)]⟩,
            [("a", 0, 0)])), .returned (.u32 (BitVec.ofNat 32 j))) := by
      intro G hG
      exact memFindWhile_some l nv kv G 0 j _ _
        (Nat.zero_le _) h32n (by omega) hlay hmem
        (by rw [hbridge, hfi])
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            findWhile (mkFindEnv l nv kv 0)
            ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] =
          .ok (((mkFindEnv l nv kv j, ⟨1, [(0, ⟨0, true, l⟩)]⟩,
            [("a", 0, 0)])), .returned (.u32 (BitVec.ofNat 32 j))) :=
        hloop 0 (by omega)
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
        litVal, findEqFwd, findEqOut, henv, hloopH0, hfi]
    | succ F =>
      have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
            findWhile (mkFindEnv l nv kv 0)
            ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] =
          .ok (((mkFindEnv l nv kv j, ⟨1, [(0, ⟨0, true, l⟩)]⟩,
            [("a", 0, 0)])), .returned (.u32 (BitVec.ofNat 32 j))) :=
        hloop (F + 1) (by omega)
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr,
        litVal, findEqFwd, findEqOut, henv, hloopS, hfi]
  | none =>
    have hloop : ∀ (G : Nat),
        min nv.toNat l.length + 1 ≤ G →
        memEvalStmtFuel G findWhile (mkFindEnv l nv kv 0)
          ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] =
          if decide (nv.toNat ≤ l.length) then
            .ok (((mkFindEnv l nv kv nv.toNat, ⟨1, [(0, ⟨0, true, l⟩)]⟩,
              [("a", 0, 0)])), .fellThrough)
          else .error .OOB := by
      intro G hG
      exact memFindWhile_none l nv kv G 0 _ _
        (Nat.zero_le _) h32n h32l (by omega) hlay hmem
        (by rw [hbridge, hfi])
    by_cases hle : nv.toNat ≤ l.length
    · have htrue : (decide (nv.toNat ≤ l.length)) = true := by simp [hle]
      have hsnret : envLookup (mkFindEnv l nv kv nv.toNat) "n" =
            some (.u32 nv) :=
        mkFindEnv_n l nv kv nv.toNat
      have hinv : BitVec.ofNat 32 nv.toNat = nv := ofNat32_toNat_inv nv
      cases F with
      | zero =>
        have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
              findWhile (mkFindEnv l nv kv 0)
              ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] =
            .ok (((mkFindEnv l nv kv nv.toNat, ⟨1, [(0, ⟨0, true, l⟩)]⟩,
              [("a", 0, 0)])), .fellThrough) := by
          have h := hloop 0 (by omega)
          rwa [htrue] at h
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
          litVal, findEqFwd, findEqOut, henv, hloopH0, hsnret, hfi, htrue,
          hinv]
      | succ F =>
        have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
              findWhile (mkFindEnv l nv kv 0)
              ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] =
            .ok (((mkFindEnv l nv kv nv.toNat, ⟨1, [(0, ⟨0, true, l⟩)]⟩,
              [("a", 0, 0)])), .fellThrough) := by
          have h := hloop (F + 1) (by omega)
          rwa [htrue] at h
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr,
          litVal, findEqFwd, findEqOut, henv, hloopS, hsnret, hfi, htrue,
          hinv]
    · have hfalse : (decide (nv.toNat ≤ l.length)) = false := by
        simp [hle]
      cases F with
      | zero =>
        have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
              findWhile (mkFindEnv l nv kv 0)
              ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] = .error .OOB := by
          have h := hloop 0 (by omega)
          rwa [hfalse] at h
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
          litVal, findEqFwd, findEqOut, henv, hloopH0, hfi, hfalse]
      | succ F =>
        have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
              findWhile (mkFindEnv l nv kv 0)
              ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] = .error .OOB := by
          have h := hloop (F + 1) (by omega)
          rwa [hfalse] at h
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr,
          litVal, findEqFwd, findEqOut, henv, hloopS, hfi, hfalse]

/-- Transfer for `find_eq`: both sides equal `findEqFwd`. -/
theorem memTransfer_findEq (F : Nat) (l : List (BitVec 32))
    (nv kv : BitVec 32)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length + 1 ≤ F)
    (_h : oracleNoalias findEqFunc [.arr32 l, .u32 nv, .u32 kv]) :
    memEvalFuncFuel F findEqFunc [.arr32 l, .u32 nv, .u32 kv] =
      evalFuncFuel F findEqFunc [.arr32 l, .u32 nv, .u32 kv] := by
  rw [memEvalFuncFuel_findEq F l nv kv h32n h32l hF,
    evalFuncFuel_find F l nv kv h32n h32l hF]

/-! ## M3c caller transfers: `add_caller`, `sum_caller` (program layer) -/

/-- `memEval` for the `add` leaf, stated about `addFunc` (the callee
    fact the caller proofs need; cf. `evalFuncFuel_add`). -/
theorem memEvalFuncFuel_add (F : Nat) (a b : BitVec 32) :
    memEvalFuncFuel F addFunc [.i32 a, .i32 b] = addFwd a b := by
  have hbf : addFunc.args =
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }] := rfl
  have hbody : addFunc.body =
      .return_ (.add (.var "a") (.var "b")) := rfl
  have hb : bindMemArgs
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }]
      [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) :=
    bindMemArgs_add a b
  have ha := envLookup_add_a a b
  have hbb := envLookup_add_b a b
  simp only [memEvalFuncFuel, hbf, hbody, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      memEvalExpr, addFwd, ha, hbb] <;>
    (cases checkedAddI32 a b <;> rfl)

/-- `memEval` for `add_caller`: program evaluation over `[addFunc]`
    agrees with the forward (mirrors `evalProgFunc_addCaller`; caller
    `Mem`/`Layout` stay `emptyMem`/`[]` — each callee runs on its own
    fresh entry blocks). -/
theorem memEvalProgFunc_addCaller (F : Nat) (x y z : BitVec 32) :
    memEvalProgFunc [addFunc] F addCallerFunc [.i32 x, .i32 y, .i32 z] =
      addCallerFwd x y z := by
  have hbind : bindMemArgs addCallerFunc.args [.i32 x, .i32 y, .i32 z]
      emptyMem =
      some ([("x", .i32 x), ("y", .i32 y), ("z", .i32 z)], emptyMem, []) :=
    bindMemArgs_addCaller x y z
  have hbody : addCallerFunc.body =
      .seq (.callRet "t" "add" ["x", "y"])
      (.seq (.callRet "r" "add" ["t", "z"])
            (.return_ (.var "r"))) := rfl
  have hx := envLookup_addCaller_x x y z
  have hy := envLookup_addCaller_y x y z
  have hfind : findFunc [addFunc] "add" = some addFunc :=
    findFunc_hit addFunc []
  cases h1 : checkedAddI32 x y with
  | error e =>
    have hc1 : memEvalFuncFuel F addFunc [.i32 x, .i32 y] = .error e := by
      rw [memEvalFuncFuel_add]
      unfold addFwd
      rw [h1]
      exact i32_map_error e
    have hargs1 : lookupArgs [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
        ["x", "y"] = some [.i32 x, .i32 y] := by
      simp [lookupArgs, hx, hy]
    have hstep1 := memEvalProgStmt_callRet_err [addFunc] F "t" "add" ["x", "y"]
      [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] emptyMem []
      [.i32 x, .i32 y] addFunc e hargs1 hfind hc1
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep1]
    simp [addCallerFwd, h1]
  | ok t =>
    have hc1 : memEvalFuncFuel F addFunc [.i32 x, .i32 y] =
        .ok (.i32 t) := by
      rw [memEvalFuncFuel_add]
      unfold addFwd
      rw [h1]
      exact i32_map_ok t
    have hargs1 : lookupArgs [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
        ["x", "y"] = some [.i32 x, .i32 y] := by
      simp [lookupArgs, hx, hy]
    have hstep1 := memEvalProgStmt_callRet_ok [addFunc] F "t" "add" ["x", "y"]
      [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] emptyMem []
      [.i32 x, .i32 y] addFunc (.i32 t) hargs1 hfind hc1
    have htz : envLookup (envExtend [("x", .i32 x), ("y", .i32 y),
        ("z", .i32 z)] "t" (.i32 t)) "t" = some (.i32 t) :=
      envExtend_hit _ _ _
    have htz2 : envLookup (envExtend [("x", .i32 x), ("y", .i32 y),
        ("z", .i32 z)] "t" (.i32 t)) "z" = some (.i32 z) := by
      simp [envExtend, envLookup, show ("z" : String) ≠ "t" by decide]
    cases h2 : checkedAddI32 t z with
    | error e =>
      have hc2 : memEvalFuncFuel F addFunc [.i32 t, .i32 z] = .error e := by
        rw [memEvalFuncFuel_add]
        unfold addFwd
        rw [h2]
        exact i32_map_error e
      have hargs2 : lookupArgs (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) ["t", "z"] =
          some [.i32 t, .i32 z] := by
        simp [lookupArgs, htz, htz2]
      have hstep2 := memEvalProgStmt_callRet_err [addFunc] F "r" "add"
        ["t", "z"] (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) emptyMem []
        [.i32 t, .i32 z] addFunc e hargs2 hfind hc2
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep2]
      simp [addCallerFwd, h1, h2, i32_map_error]
    | ok r =>
      have hc2 : memEvalFuncFuel F addFunc [.i32 t, .i32 z] =
          .ok (.i32 r) := by
        rw [memEvalFuncFuel_add]
        unfold addFwd
        rw [h2]
        exact i32_map_ok r
      have hargs2 : lookupArgs (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) ["t", "z"] =
          some [.i32 t, .i32 z] := by
        simp [lookupArgs, htz, htz2]
      have hstep2 := memEvalProgStmt_callRet_ok [addFunc] F "r" "add"
        ["t", "z"] (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) emptyMem []
        [.i32 t, .i32 z] addFunc (.i32 r) hargs2 hfind hc2
      have hret : memEvalProgStmt [addFunc] F (.return_ (.var "r"))
          (envExtend (envExtend [("x", .i32 x), ("y", .i32 y),
            ("z", .i32 z)] "t" (.i32 t)) "r" (.i32 r)) emptyMem [] =
          .ok (((envExtend (envExtend [("x", .i32 x), ("y", .i32 y),
            ("z", .i32 z)] "t" (.i32 t)) "r" (.i32 r),
            emptyMem, []), .returned (.i32 r))) :=
        memEvalProgStmt_return [addFunc] F (.var "r") _
          _ _ (.i32 r) (by simp [memEvalExpr, envExtend_hit])
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep2, hret]
      simp [addCallerFwd, h1, h2, i32_map_ok]

/-- Transfer for `add_caller` (program level): both sides equal
    `addCallerFwd`. -/
theorem memTransferProg_addCaller (F : Nat) (x y z : BitVec 32)
    (_h : oracleNoalias addCallerFunc [.i32 x, .i32 y, .i32 z]) :
    memEvalProgFunc [addFunc] F addCallerFunc [.i32 x, .i32 y, .i32 z] =
      evalProgFunc [addFunc] F addCallerFunc [.i32 x, .i32 y, .i32 z] := by
  rw [memEvalProgFunc_addCaller, evalProgFunc_addCaller]

/-- `memEval` for `sum_caller`: program evaluation over `[sumFunc]`
    agrees with the delegating forward (mirrors `evalProgFunc_sumCaller`;
    the caller block rides alongside while the callee runs on its own
    fresh entry block). -/
theorem memEvalProgFunc_sumCaller (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    memEvalProgFunc [sumFunc] F sumCallerFunc [.arr32 l, .u32 nv] =
      sumCallerFwd l nv := by
  have hbind : bindMemArgs sumCallerFunc.args [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)]) :=
    bindMemArgs_sumCaller l nv
  have hbody : sumCallerFunc.body =
      .seq (.callRet "s" "sum_array" ["a", "n"])
           (.return_ (.var "s")) := rfl
  have ha := envLookup_sumCaller_a l nv
  have hn := envLookup_sumCaller_n l nv
  have hfind : findFunc [sumFunc] "sum_array" = some sumFunc :=
    findFunc_hit sumFunc []
  have hargs : lookupArgs [("a", .arr32 l), ("n", .u32 nv)] ["a", "n"] =
      some [.arr32 l, .u32 nv] := by
    simp [lookupArgs, ha, hn]
  have hcall := memEvalFuncFuel_sum F l nv hle h32 hF
  cases hsum : sumFwd l nv with
  | error e =>
    have hcall' : memEvalFuncFuel F sumFunc [.arr32 l, .u32 nv] =
        .error e := by
      rw [hcall, hsum]
    have hstep := memEvalProgStmt_callRet_err [sumFunc] F "s" "sum_array"
      ["a", "n"] [("a", .arr32 l), ("n", .u32 nv)]
      ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)]
      [.arr32 l, .u32 nv] sumFunc e hargs hfind hcall'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep]
    simp [sumCallerFwd, hsum]
  | ok v =>
    have hcall' : memEvalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .ok v := by
      rw [hcall, hsum]
    have hstep := memEvalProgStmt_callRet_ok [sumFunc] F "s" "sum_array"
      ["a", "n"] [("a", .arr32 l), ("n", .u32 nv)]
      ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)]
      [.arr32 l, .u32 nv] sumFunc v hargs hfind hcall'
    have hret : memEvalProgStmt [sumFunc] F (.return_ (.var "s"))
        (envExtend [("a", .arr32 l), ("n", .u32 nv)] "s" v)
        ⟨1, [(0, ⟨0, true, l⟩)]⟩ [("a", 0, 0)] =
        .ok (((envExtend [("a", .arr32 l), ("n", .u32 nv)] "s" v,
          ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)]), .returned v)) :=
      memEvalProgStmt_return [sumFunc] F (.var "s") _
        _ _ v (by simp [memEvalExpr, envExtend_hit])
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep, hret]
    simp [sumCallerFwd, hsum]

/-- Transfer for `sum_caller` (program level): both sides equal
    `sumCallerFwd`. -/
theorem memTransferProg_sumCaller (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F)
    (_h : oracleNoalias sumCallerFunc [.arr32 l, .u32 nv]) :
    memEvalProgFunc [sumFunc] F sumCallerFunc [.arr32 l, .u32 nv] =
      evalProgFunc [sumFunc] F sumCallerFunc [.arr32 l, .u32 nv] := by
  rw [memEvalProgFunc_sumCaller F l nv hle h32 hF,
    evalProgFunc_sumCaller F l nv hle h32 hF]
