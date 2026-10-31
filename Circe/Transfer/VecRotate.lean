/-
Circe.Transfer.VecRotate — R3 transfer for `std::vector<int32_t>`
in-place left rotation by `k` (triple entry-over-entry composition).

Mirrors `evalProgFunc_vecRotate` step for step on the memory layer:
the `size` callee and the three admitted segment calls communicate
by value (caller `Mem`/`Layout` thread through unchanged — the body
itself never stores), the pure `z ← 0` threads through `memRevLet`,
and the return assembles through the rotation identity. The owned
`u64` count binds by value at entry.
-/
import Circe.Transfer.Slice
import Circe.Transfer.VecSegReverse
import Circe.Emit.VecRotate
import Circe.Hoare.Rules
import Circe.Specs

/-! ## Entry bridge (`memEval` + transfer) -/

/-- `memEval` for `vec_rotate`: program evaluation over the frozen
    leaves threads three admitted segment reversals and agrees with
    left rotation on memory (mirrors `evalProgFunc_vecRotate`; fuel
    covers each countdown plus the composition step). -/
theorem rotMemEvalProgFunc (F : Nat) (l : List (BitVec 32))
    (k : Nat) (kB : BitVec 64)
    (hkB : kB.toNat = k)
    (hk : k ≤ l.length)
    (hlen64 : l.length < 2 ^ 64)
    (hF : (revIters 0 k + 1) + (revIters k l.length + 1) +
      (revIters 0 l.length + 1) + 1 ≤ F) :
    memEvalProgFunc vecRotateProg F vecRotateFunc
      [.stdVecVal l, .u64 kB] =
      vecRotateFwd l kB := by
  obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  have hb : bindMemArgs vecRotateFunc.args
      [.stdVecVal l, .u64 kB] emptyMem =
      some ([("v", .stdVecVal l), ("k", .u64 kB)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) :=
    bindMemArgs_vecRotate l kB
  have hbind := hb
  have hbody : vecRotateFunc.body =
      (.seq (.callRet "m" stdVecSizeName ["v"])
        (.seq (.let_ "z" (.u 64) (.lit (.u64 0)))
          (.seq (.callProg "v" vecSegReverseName ["v", "z", "k"])
            (.seq (.callProg "v" vecSegReverseName ["v", "k", "m"])
              (.seq (.callProg "v" vecSegReverseName ["v", "z", "m"])
                (.return_ (.var "v"))))))) := rfl
  have hlay₀ : layoutLookup [("v", 0, 0)] "v" = some (0, 0) := by
    simp [layoutLookup]
  have hmem₀ : memFind ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hnN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlen64
  have hz0 : (0 : BitVec 64).toNat = 0 := rfl
  -- `m ← size(v)` (callee communicates by value).
  have hargs_m : lookupArgs [("v", .stdVecVal l), ("k", .u64 kB)]
      ["v"] = some [.stdVecVal l] :=
    lookupArgs_cons_hit _ _ _ _ _
      (by simp [envLookup]) (lookupArgs_nil _)
  have hcall_m : memEvalFuncFuel (G + 1) stdVecSizeFunc
      [.stdVecVal l] = .ok (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [memEvalFuncFuel_stdVecSize]
    rfl
  have hstep_m := memEvalProgStmt_callRet_ok vecRotateProg (G + 1)
    "m" stdVecSizeName ["v"] [("v", .stdVecVal l), ("k", .u64 kB)]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
    [.stdVecVal l] stdVecSizeFunc (.u64 (BitVec.ofNat 64 l.length))
    hargs_m rotFindSize hcall_m
  have hm₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envExtend_hit _ _ _
  have hv₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "m" by decide)]
    simp [envLookup]
  have hk₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "k" =
      some (.u64 kB) := by
    rw [envExtend_miss _ _ _ _
      (show ("k" : String) ≠ "m" by decide)]
    simp [envLookup]
  -- `z ← 0` (pure copy, memory untouched).
  have hstep_z := memRevLet vecRotateProg (G + 1) "z" (.u 64)
    (.lit (.u64 0)) (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length)))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
    (.u64 0)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (memEvalExpr_lit _ _ _ _)
    (by simp [evalExpr, litVal])
  have hz₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "z" = some (.u64 0) :=
    envExtend_hit _ _ _
  have hm₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₁ (by decide)
  have hv₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "v" = some (.stdVecVal l) :=
    envLookup_extend_miss _ _ _ _ _ hv₁ (by decide)
  have hk₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "k" = some (.u64 kB) :=
    envLookup_extend_miss _ _ _ _ _ hk₁ (by decide)
  -- First window `[0, k)`.
  have hF₁ : revIters 0 k + 1 ≤ G := by omega
  have hcall1 := segMemEvalProgFunc vecRotateProg G l 0 k
    0 kB hz0 hkB (by omega) (by omega) hlen64 hF₁ rotFindAt
  have hfw1 : vecSegReverseFwd l 0 kB
      = .ok (.stdVecVal (segReverseWindow l 0 kB.toNat)) := by
    simp only [vecSegReverseFwd]
    rw [hz0, hkB, if_pos ⟨Nat.zero_le _, hk⟩]
  rw [hfw1, hkB] at hcall1
  have hargs_c1 : lookupArgs (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0))
      ["v", "z", "k"] =
      some [.stdVecVal l, .u64 0, .u64 kB] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₂
      (lookupArgs_cons_hit _ _ _ _ _ hz₂
        (lookupArgs_cons_hit _ _ _ _ _ hk₂ (lookupArgs_nil _)))
  have hstep_c1 : memEvalProgStmt vecRotateProg (G + 1)
      (.callProg "v" vecSegReverseName ["v", "z", "k"])
      (envExtend (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
        "m" (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)] =
      .ok ((envExtend (envExtend (envExtend [("v", .stdVecVal l),
        ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
        "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩, [("v", 0, 0)]),
        .fellThrough) :=
    memEvalProgStmt_callProg_ok vecRotateProg G "v" vecSegReverseName
      ["v", "z", "k"] (envExtend (envExtend [("v", .stdVecVal l),
        ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
        "z" (.u64 0))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
      [.stdVecVal l, .u64 0, .u64 kB]
      vecSegReverseFunc (.stdVecVal (segReverseWindow l 0 k))
      hargs_c1 rotFindSeg hcall1
  have hv₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v" =
      some (.stdVecVal (segReverseWindow l 0 k)) :=
    envExtend_hit _ _ _
  have hk₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "k" =
      some (.u64 kB) :=
    envLookup_extend_miss _ _ _ _ _ hk₂ (by decide)
  have hm₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₂ (by decide)
  -- Second window `[k, n)` (memory still untouched).
  have hlen1w : (segReverseWindow l 0 k).length = l.length :=
    segReverseWindow_length l 0 k (Nat.zero_le _) hk
  have hlen64w1 : (segReverseWindow l 0 k).length < 2 ^ 64 := by
    rw [hlen1w]; exact hlen64
  have hF₂ : revIters k l.length + 1 ≤ G := by omega
  have hcall2 := segMemEvalProgFunc vecRotateProg G
    (segReverseWindow l 0 k) k l.length kB
    (BitVec.ofNat 64 l.length) hkB hnN (by omega)
    (by omega) hlen64w1 hF₂ rotFindAt
  have hfw2 : vecSegReverseFwd (segReverseWindow l 0 k) kB
      (BitVec.ofNat 64 l.length)
      = .ok (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        kB.toNat (BitVec.ofNat 64 l.length).toNat)) := by
    simp only [vecSegReverseFwd]
    rw [hkB, hnN, hlen1w, if_pos ⟨hk, Nat.le_refl _⟩]
  rw [hfw2, hkB, hnN] at hcall2
  have hargs_c2 : lookupArgs (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) ["v", "k", "m"] =
      some [.stdVecVal (segReverseWindow l 0 k), .u64 kB,
        .u64 (BitVec.ofNat 64 l.length)] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₃
      (lookupArgs_cons_hit _ _ _ _ _ hk₃
        (lookupArgs_cons_hit _ _ _ _ _ hm₃ (lookupArgs_nil _)))
  have hstep_c2 : memEvalProgStmt vecRotateProg (G + 1)
      (.callProg "v" vecSegReverseName ["v", "k", "m"])
      (envExtend (envExtend (envExtend [("v", .stdVecVal l),
        ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
        "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)] =
      .ok ((envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩, [("v", 0, 0)]),
        .fellThrough) :=
    memEvalProgStmt_callProg_ok vecRotateProg G "v" vecSegReverseName
      ["v", "k", "m"] (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
      [.stdVecVal (segReverseWindow l 0 k), .u64 kB,
        .u64 (BitVec.ofNat 64 l.length)]
      vecSegReverseFunc
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))
      hargs_c2 rotFindSeg hcall2
  have hv₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "v" =
      some (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length)) :=
    envExtend_hit _ _ _
  have hz₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "z" =
      some (.u64 0) :=
    envLookup_extend_miss _ _ _ _ _ hz₂ (by decide)
  have hz₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "z" = some (.u64 0) :=
    envLookup_extend_miss _ _ _ _ _ hz₃ (by decide)
  have hk₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "k" = some (.u64 kB) := by
    have hk₃' : envLookup (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "k" =
        some (.u64 kB) :=
      hk₃
    rw [envExtend_miss _ _ _ _
      (show ("k" : String) ≠ "v" by decide)]
    exact hk₃'
  have hm₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₃ (by decide)
  -- Third window `[0, n)`.
  have hlen2w : (segReverseWindow (segReverseWindow l 0 k)
      k l.length).length = l.length := by
    have h := segReverseWindow_length (segReverseWindow l 0 k)
      k l.length hk (by omega)
    rwa [hlen1w] at h
  have hlen64w2 : (segReverseWindow (segReverseWindow l 0 k)
      k l.length).length < 2 ^ 64 := by
    rw [hlen2w]; exact hlen64
  have hF₃ : revIters 0 l.length + 1 ≤ G := by omega
  have hcall3 := segMemEvalProgFunc vecRotateProg G
    (segReverseWindow (segReverseWindow l 0 k) k l.length)
    0 l.length 0 (BitVec.ofNat 64 l.length) hz0 hnN
    (by omega) (by omega) hlen64w2 hF₃ rotFindAt
  have hfw3 : vecSegReverseFwd
      (segReverseWindow (segReverseWindow l 0 k) k l.length) 0
      (BitVec.ofNat 64 l.length)
      = .ok (.stdVecVal (segReverseWindow
        (segReverseWindow (segReverseWindow l 0 k) k l.length)
        0 (BitVec.ofNat 64 l.length).toNat)) := by
    simp only [vecSegReverseFwd]
    rw [hz0, hnN, hlen2w, if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
  rw [hfw3, hnN] at hcall3
  have hargs_c3 : lookupArgs (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) ["v", "z", "m"] =
      some [.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length), .u64 0, .u64 (BitVec.ofNat 64 l.length)] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₄
      (lookupArgs_cons_hit _ _ _ _ _ hz₄
        (lookupArgs_cons_hit _ _ _ _ _ hm₄ (lookupArgs_nil _)))
  have hstep_c3 : memEvalProgStmt vecRotateProg (G + 1)
      (.callProg "v" vecSegReverseName ["v", "z", "m"])
      (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow
          (segReverseWindow l 0 k) k l.length) 0 l.length)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩, [("v", 0, 0)]),
        .fellThrough) :=
    memEvalProgStmt_callProg_ok vecRotateProg G "v" vecSegReverseName
      ["v", "z", "m"] (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
      [.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length), .u64 0, .u64 (BitVec.ofNat 64 l.length)]
      vecSegReverseFunc
      (.stdVecVal (segReverseWindow (segReverseWindow
        (segReverseWindow l 0 k) k l.length) 0 l.length))
      hargs_c3 rotFindSeg hcall3
  -- `return v` over the thrice-reversed words.
  have hrot := segWindow_rotate3 l k hk
  have hretV : memEvalExpr (.var "v")
      (envExtend (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow
          (segReverseWindow l 0 k) k l.length) 0 l.length)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)] =
      evalExpr (.var "v")
        (envExtend (envExtend (envExtend (envExtend (envExtend
          [("v", .stdVecVal l), ("k", .u64 kB)] "m"
          (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
          (.stdVecVal (segReverseWindow l 0 k))) "v"
          (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
            k l.length))) "v"
          (.stdVecVal (segReverseWindow (segReverseWindow
            (segReverseWindow l 0 k) k l.length) 0 l.length))) :=
    memEvalExpr_var _ _ _ _
  have hv₅ : envLookup (envExtend (envExtend (envExtend (envExtend
      (envExtend [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow
        (segReverseWindow l 0 k) k l.length) 0 l.length))) "v" =
      some (.stdVecVal ((l.drop kB.toNat) ++ l.take kB.toNat)) := by
    rw [hkB, ← hrot]
    exact envExtend_hit _ _ _
  have hret := memEvalProgStmt_return vecRotateProg (G + 1) (.var "v")
    (envExtend (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow
        (segReverseWindow l 0 k) k l.length) 0 l.length)))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ [("v", 0, 0)]
    (.stdVecVal ((l.drop kB.toNat) ++ l.take kB.toNat))
    (by rw [hretV]; exact evalExpr_var_hit _ _ _ hv₅)
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_m,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_z,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_c1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_c2,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_c3,
    hret]
  simp only [vecRotateFwd]
  rw [hkB, if_pos hk]

/-- F1 rule application: the rotate spine's `fellThrough` prefix
    (size call, `z` let, three admitted segment calls) composes
    from its leaf triples by four nested `htripleProg_seq`
    applications. The leaves stay hypotheses — F2 discharges the
    three call leaves from callee contracts; the trailing
    `return_` needs the deferred prog-level seq-return equation,
    so the prefix stops at the third call. -/
theorem hoare_rotateSpine_seq (prog : Prog)
    (P0 P1 P2 P3 P4 P5 : Env × Mem × Layout → Prop)
    (hsize : HTripleProg prog P0 (.callRet "m" stdVecSizeName ["v"])
      (fun st o => o = .fellThrough ∧ P1 st))
    (hz : HTripleProg prog P1 (.let_ "z" (.u 64) (.lit (.u64 0)))
      (fun st o => o = .fellThrough ∧ P2 st))
    (hc1 : HTripleProg prog P2
      (.callProg "v" vecSegReverseName ["v", "z", "k"])
      (fun st o => o = .fellThrough ∧ P3 st))
    (hc2 : HTripleProg prog P3
      (.callProg "v" vecSegReverseName ["v", "k", "m"])
      (fun st o => o = .fellThrough ∧ P4 st))
    (hc3 : HTripleProg prog P4
      (.callProg "v" vecSegReverseName ["v", "z", "m"])
      (fun st o => o = .fellThrough ∧ P5 st)) :
    HTripleProg prog P0
      (.seq (.callRet "m" stdVecSizeName ["v"])
        (.seq (.let_ "z" (.u 64) (.lit (.u64 0)))
          (.seq (.callProg "v" vecSegReverseName ["v", "z", "k"])
            (.seq (.callProg "v" vecSegReverseName ["v", "k", "m"])
              (.callProg "v" vecSegReverseName ["v", "z", "m"])))))
      (fun st o => o = .fellThrough ∧ P5 st) := by
  have s45 := htripleProg_seq prog P3 P4 _ _ _ hc2 hc3
  have s345 := htripleProg_seq prog P2 P3 _ _ _ hc1 s45
  have s2345 := htripleProg_seq prog P1 P2 _ _ _ hz s345
  exact htripleProg_seq prog P0 P1 _ _ _ hsize s2345

/-- F2 rule application: the rotate prefix as a closed triple —
    all five leaves discharged, no admitted hypotheses. The size
    and `z` leaves wrap their transfer equations directly; each
    seg-call leaf applies `htripleProg_callProg_at` with `hcall`
    from transfer (`segMemEvalProgFunc`) rewritten by the U2
    callee contract (`vecSegReverse_correct`) — the contract is
    consumed, never re-verified. Four `htripleProg_seq_at`
    applications compose the spine at the shared fuel `G + 1`.
    The trailing `return_` stays out (deferred seq-return
    equation), so this is the prefix triple, not the entry. -/
theorem hoare_rotateSpine_closed (G : Nat) (l : List (BitVec 32))
    (k : Nat) (kB : BitVec 64)
    (hkB : kB.toNat = k)
    (hk : k ≤ l.length)
    (hlen64 : l.length < 2 ^ 64)
    (hF₁ : revIters 0 k + 1 ≤ G)
    (hF₂ : revIters k l.length + 1 ≤ G)
    (hF₃ : revIters 0 l.length + 1 ≤ G) :
    HTripleProgAt vecRotateProg (G + 1)
      (fun st => st = ([("v", .stdVecVal l), ("k", .u64 kB)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]))
      (.seq (.callRet "m" stdVecSizeName ["v"])
        (.seq (.let_ "z" (.u 64) (.lit (.u64 0)))
          (.seq (.callProg "v" vecSegReverseName ["v", "z", "k"])
            (.seq (.callProg "v" vecSegReverseName ["v", "k", "m"])
              (.callProg "v" vecSegReverseName ["v", "z", "m"])))))
      (fun st o => o = .fellThrough ∧ st = (envExtend (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow
          (segReverseWindow l 0 k) k l.length) 0 l.length)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)])) := by
  have hnN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlen64
  have hz0 : (0 : BitVec 64).toNat = 0 := rfl
  -- `m ← size(v)` (callee communicates by value).
  have hargs_m : lookupArgs [("v", .stdVecVal l), ("k", .u64 kB)]
      ["v"] = some [.stdVecVal l] :=
    lookupArgs_cons_hit _ _ _ _ _
      (by simp [envLookup]) (lookupArgs_nil _)
  have hcall_m : memEvalFuncFuel (G + 1) stdVecSizeFunc
      [.stdVecVal l] = .ok (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [memEvalFuncFuel_stdVecSize]
    rfl
  have leaf_size : HTripleProgAt vecRotateProg (G + 1)
      (fun st => st = ([("v", .stdVecVal l), ("k", .u64 kB)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]))
      (.callRet "m" stdVecSizeName ["v"])
      (fun st o => o = .fellThrough ∧ st = (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)])) := by
    intro ρ m π hP
    simp only [Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl, rfl⟩ := hP
    exact ⟨_, _, _, _,
      memEvalProgStmt_callRet_ok vecRotateProg (G + 1) "m"
        stdVecSizeName ["v"] _ _ _ [.stdVecVal l] stdVecSizeFunc
        (.u64 (BitVec.ofNat 64 l.length)) hargs_m rotFindSize hcall_m,
      rfl, rfl⟩
  -- Lookup chain after `m` and `z` (copied from `rotMemEvalProgFunc`).
  have hm₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envExtend_hit _ _ _
  have hv₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "m" by decide)]
    simp [envLookup]
  have hk₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "k" =
      some (.u64 kB) := by
    rw [envExtend_miss _ _ _ _
      (show ("k" : String) ≠ "m" by decide)]
    simp [envLookup]
  have leaf_z : HTripleProgAt vecRotateProg (G + 1)
      (fun st => st = (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]))
      (.let_ "z" (.u 64) (.lit (.u64 0)))
      (fun st o => o = .fellThrough ∧ st = (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)])) := by
    intro ρ m π hP
    simp only [Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl, rfl⟩ := hP
    exact ⟨_, _, _, _,
      memRevLet vecRotateProg (G + 1) "z" (.u 64) (.lit (.u64 0))
        _ _ _ (.u64 0)
        (by intro se h; cases h) (by intro se h; cases h)
        (by intro ce h; cases h)
        (memEvalExpr_lit _ _ _ _) (by simp [evalExpr, litVal]),
      rfl, rfl⟩
  have hz₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "z" = some (.u64 0) :=
    envExtend_hit _ _ _
  have hm₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₁ (by decide)
  have hv₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "v" = some (.stdVecVal l) :=
    envLookup_extend_miss _ _ _ _ _ hv₁ (by decide)
  have hk₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "k" = some (.u64 kB) :=
    envLookup_extend_miss _ _ _ _ _ hk₁ (by decide)
  -- First window `[0, k)`: transfer + U2 contract.
  have hcon1 : vecSegReverseFwd l 0 kB =
      .ok (.stdVecVal (segReverseWindow l 0 k)) := by
    have h := vecSegReverse_correct l 0 kB
      (by rw [hz0]; exact Nat.zero_le _)
      (by rw [hkB]; exact hk)
    rwa [hz0, hkB] at h
  have hcall1 : memEvalProgFunc vecRotateProg G vecSegReverseFunc
      [.stdVecVal l, .u64 0, .u64 kB] =
      .ok (.stdVecVal (segReverseWindow l 0 k)) := by
    rw [segMemEvalProgFunc vecRotateProg G l 0 k 0 kB hz0 hkB
      (by omega) (by omega) hlen64 hF₁ rotFindAt, hcon1]
  have hargs_c1 : lookupArgs (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0))
      ["v", "z", "k"] =
      some [.stdVecVal l, .u64 0, .u64 kB] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₂
      (lookupArgs_cons_hit _ _ _ _ _ hz₂
        (lookupArgs_cons_hit _ _ _ _ _ hk₂ (lookupArgs_nil _)))
  have leaf_c1 : HTripleProgAt vecRotateProg (G + 1)
      (fun st => st = (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]))
      (.callProg "v" vecSegReverseName ["v", "z", "k"])
      (fun st o => o = .fellThrough ∧ st = (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)])) := by
    refine htripleProg_callProg_at vecRotateProg G _ _ _ _ _ ?_
    intro ρ m π hP
    simp only [Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl, rfl⟩ := hP
    exact ⟨[.stdVecVal l, .u64 0, .u64 kB], vecSegReverseFunc,
      .stdVecVal (segReverseWindow l 0 k),
      hargs_c1, rotFindSeg, hcall1, rfl, rfl⟩
  -- Second window `[k, n)` (memory still untouched).
  have hlen1w : (segReverseWindow l 0 k).length = l.length :=
    segReverseWindow_length l 0 k (Nat.zero_le _) hk
  have hlen64w1 : (segReverseWindow l 0 k).length < 2 ^ 64 := by
    rw [hlen1w]; exact hlen64
  have hv₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v" =
      some (.stdVecVal (segReverseWindow l 0 k)) :=
    envExtend_hit _ _ _
  have hk₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "k" =
      some (.u64 kB) :=
    envLookup_extend_miss _ _ _ _ _ hk₂ (by decide)
  have hm₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₂ (by decide)
  have hcon2 : vecSegReverseFwd (segReverseWindow l 0 k) kB
      (BitVec.ofNat 64 l.length) =
      .ok (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length)) := by
    have h := vecSegReverse_correct (segReverseWindow l 0 k) kB
      (BitVec.ofNat 64 l.length)
      (by rw [hkB, hnN]; exact hk)
      (by rw [hnN]; omega)
    rwa [hkB, hnN] at h
  have hcall2 : memEvalProgFunc vecRotateProg G vecSegReverseFunc
      [.stdVecVal (segReverseWindow l 0 k), .u64 kB,
        .u64 (BitVec.ofNat 64 l.length)] =
      .ok (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length)) := by
    rw [segMemEvalProgFunc vecRotateProg G (segReverseWindow l 0 k)
      k l.length kB (BitVec.ofNat 64 l.length) hkB hnN
      (by omega) (by omega) hlen64w1 hF₂ rotFindAt, hcon2]
  have hargs_c2 : lookupArgs (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) ["v", "k", "m"] =
      some [.stdVecVal (segReverseWindow l 0 k), .u64 kB,
        .u64 (BitVec.ofNat 64 l.length)] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₃
      (lookupArgs_cons_hit _ _ _ _ _ hk₃
        (lookupArgs_cons_hit _ _ _ _ _ hm₃ (lookupArgs_nil _)))
  have leaf_c2 : HTripleProgAt vecRotateProg (G + 1)
      (fun st => st = (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]))
      (.callProg "v" vecSegReverseName ["v", "k", "m"])
      (fun st o => o = .fellThrough ∧ st = (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)])) := by
    refine htripleProg_callProg_at vecRotateProg G _ _ _ _ _ ?_
    intro ρ m π hP
    simp only [Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl, rfl⟩ := hP
    exact ⟨[.stdVecVal (segReverseWindow l 0 k), .u64 kB,
      .u64 (BitVec.ofNat 64 l.length)], vecSegReverseFunc,
      .stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length),
      hargs_c2, rotFindSeg, hcall2, rfl, rfl⟩
  -- Third window `[0, n)`.
  have hlen2w : (segReverseWindow (segReverseWindow l 0 k)
      k l.length).length = l.length := by
    have h := segReverseWindow_length (segReverseWindow l 0 k)
      k l.length hk (by omega)
    rwa [hlen1w] at h
  have hlen64w2 : (segReverseWindow (segReverseWindow l 0 k)
      k l.length).length < 2 ^ 64 := by
    rw [hlen2w]; exact hlen64
  have hv₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "v" =
      some (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length)) :=
    envExtend_hit _ _ _
  have hz₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "z" =
      some (.u64 0) :=
    envLookup_extend_miss _ _ _ _ _ hz₂ (by decide)
  have hz₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "z" = some (.u64 0) :=
    envLookup_extend_miss _ _ _ _ _ hz₃ (by decide)
  have hk₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "k" = some (.u64 kB) := by
    have hk₃' : envLookup (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "k" =
        some (.u64 kB) :=
      hk₃
    rw [envExtend_miss _ _ _ _
      (show ("k" : String) ≠ "v" by decide)]
    exact hk₃'
  have hm₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₃ (by decide)
  have hcon3 : vecSegReverseFwd
      (segReverseWindow (segReverseWindow l 0 k) k l.length) 0
      (BitVec.ofNat 64 l.length) =
      .ok (.stdVecVal (segReverseWindow (segReverseWindow
        (segReverseWindow l 0 k) k l.length) 0 l.length)) := by
    have h := vecSegReverse_correct
      (segReverseWindow (segReverseWindow l 0 k) k l.length) 0
      (BitVec.ofNat 64 l.length)
      (by rw [hz0]; exact Nat.zero_le _)
      (by rw [hnN]; omega)
    rwa [hz0, hnN] at h
  have hcall3 : memEvalProgFunc vecRotateProg G vecSegReverseFunc
      [.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length), .u64 0,
        .u64 (BitVec.ofNat 64 l.length)] =
      .ok (.stdVecVal (segReverseWindow (segReverseWindow
        (segReverseWindow l 0 k) k l.length) 0 l.length)) := by
    rw [segMemEvalProgFunc vecRotateProg G
      (segReverseWindow (segReverseWindow l 0 k) k l.length)
      0 l.length 0 (BitVec.ofNat 64 l.length) hz0 hnN
      (by omega) (by omega) hlen64w2 hF₃ rotFindAt, hcon3]
  have hargs_c3 : lookupArgs (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) ["v", "z", "m"] =
      some [.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length), .u64 0, .u64 (BitVec.ofNat 64 l.length)] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₄
      (lookupArgs_cons_hit _ _ _ _ _ hz₄
        (lookupArgs_cons_hit _ _ _ _ _ hm₄ (lookupArgs_nil _)))
  have leaf_c3 : HTripleProgAt vecRotateProg (G + 1)
      (fun st => st = (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]))
      (.callProg "v" vecSegReverseName ["v", "z", "m"])
      (fun st o => o = .fellThrough ∧ st = (envExtend (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow
          (segReverseWindow l 0 k) k l.length) 0 l.length)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)])) := by
    refine htripleProg_callProg_at vecRotateProg G _ _ _ _ _ ?_
    intro ρ m π hP
    simp only [Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl, rfl⟩ := hP
    exact ⟨[.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
      k l.length), .u64 0, .u64 (BitVec.ofNat 64 l.length)],
      vecSegReverseFunc,
      .stdVecVal (segReverseWindow (segReverseWindow
        (segReverseWindow l 0 k) k l.length) 0 l.length),
      hargs_c3, rotFindSeg, hcall3, rfl, rfl⟩
  -- Four fixed-fuel compositions.
  have s45 := htripleProg_seq_at vecRotateProg (G + 1)
    _ _ _ _ _ leaf_c2 leaf_c3
  have s345 := htripleProg_seq_at vecRotateProg (G + 1)
    _ _ _ _ _ leaf_c1 s45
  have s2345 := htripleProg_seq_at vecRotateProg (G + 1)
    _ _ _ _ _ leaf_z s345
  exact htripleProg_seq_at vecRotateProg (G + 1)
    _ _ _ _ _ leaf_size s2345

/-- F3 rule exercise: the first seg call with a caller-memory
    frame — an arbitrary `R` over the (unchanged) caller memory
    rides across the call. Same debts and facts as `leaf_c1`
    above; the frame adds no proof obligations because the call
    equation keeps `m` identical. A fully framed spine (all five
    leaves) waits for an actual multi-cell caller — third-use
    rule, so prose for now. -/
theorem hoare_segCall1_framed (G : Nat) (l : List (BitVec 32))
    (k : Nat) (kB : BitVec 64)
    (hkB : kB.toNat = k)
    (hk : k ≤ l.length)
    (hlen64 : l.length < 2 ^ 64)
    (hF₁ : revIters 0 k + 1 ≤ G)
    (R : Mem → Prop) :
    HTripleProgAt vecRotateProg (G + 1)
      (fun st => st = (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) ∧
        R st.2.1)
      (.callProg "v" vecSegReverseName ["v", "z", "k"])
      (fun st o => (o = .fellThrough ∧ st = (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k)),
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)])) ∧
        R st.2.1) := by
  have hz0 : (0 : BitVec 64).toNat = 0 := rfl
  have hm₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envExtend_hit _ _ _
  have hv₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "m" by decide)]
    simp [envLookup]
  have hk₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "k" =
      some (.u64 kB) := by
    rw [envExtend_miss _ _ _ _
      (show ("k" : String) ≠ "m" by decide)]
    simp [envLookup]
  have hz₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "z" = some (.u64 0) :=
    envExtend_hit _ _ _
  have hm₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₁ (by decide)
  have hv₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "v" = some (.stdVecVal l) :=
    envLookup_extend_miss _ _ _ _ _ hv₁ (by decide)
  have hk₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "k" = some (.u64 kB) :=
    envLookup_extend_miss _ _ _ _ _ hk₁ (by decide)
  have hcon1 : vecSegReverseFwd l 0 kB =
      .ok (.stdVecVal (segReverseWindow l 0 k)) := by
    have h := vecSegReverse_correct l 0 kB
      (by rw [hz0]; exact Nat.zero_le _)
      (by rw [hkB]; exact hk)
    rwa [hz0, hkB] at h
  have hcall1 : memEvalProgFunc vecRotateProg G vecSegReverseFunc
      [.stdVecVal l, .u64 0, .u64 kB] =
      .ok (.stdVecVal (segReverseWindow l 0 k)) := by
    rw [segMemEvalProgFunc vecRotateProg G l 0 k 0 kB hz0 hkB
      (by omega) (by omega) hlen64 hF₁ rotFindAt, hcon1]
  have hargs_c1 : lookupArgs (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0))
      ["v", "z", "k"] =
      some [.stdVecVal l, .u64 0, .u64 kB] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₂
      (lookupArgs_cons_hit _ _ _ _ _ hz₂
        (lookupArgs_cons_hit _ _ _ _ _ hk₂ (lookupArgs_nil _)))
  refine htripleProg_callProg_frame_at vecRotateProg G
    (fun st => st = (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0),
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
      [("v", 0, 0)]))
    (fun st o => (o = .fellThrough ∧ st = (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k)),
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
      [("v", 0, 0)])))
    R "v" vecSegReverseName ["v", "z", "k"] ?_
  intro ρ m π hP hR
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  exact ⟨[.stdVecVal l, .u64 0, .u64 kB], vecSegReverseFunc,
    .stdVecVal (segReverseWindow l 0 k),
    hargs_c1, rotFindSeg, hcall1, ⟨rfl, rfl⟩⟩

/-- Transfer for `vec_rotate` (program level). -/
theorem rotMemTransferProg (F : Nat) (l : List (BitVec 32))
    (k : Nat) (kB : BitVec 64)
    (hkB : kB.toNat = k)
    (hk : k ≤ l.length)
    (hlen64 : l.length < 2 ^ 64)
    (hF : (revIters 0 k + 1) + (revIters k l.length + 1) +
      (revIters 0 l.length + 1) + 1 ≤ F)
    (_h : oracleNoalias vecRotateFunc [.stdVecVal l, .u64 kB]) :
    memEvalProgFunc vecRotateProg F vecRotateFunc
      [.stdVecVal l, .u64 kB] =
      evalProgFunc vecRotateProg F vecRotateFunc
        [.stdVecVal l, .u64 kB] := by
  rw [rotMemEvalProgFunc F l k kB hkB hk hlen64 hF,
    evalProgFunc_vecRotate F l k kB hkB hk hlen64 hF]
