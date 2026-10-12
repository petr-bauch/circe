/-
Circe.Crypto.ShaFunc — whole-function correctness for the K5
SHA-256 block function `sha256_compress`.

Assembly discipline: the head of the chain (block-copy, schedule,
work-init) threads exact phase envs with `rfl` bridges, reusing the
`ShaLoops` whiles (K4 `evalFuncFuel_chachaBlock` precedent). The
tail goes abstract: an exact `compressWhile` over `mkCompressEnv`
cannot bridge by `rfl` (the loop-entry env after `let r` has no
`t1`/`t2` bindings while `mkCompressEnv` carries them as stale
params, and post-iteration envs differ structurally again — shape
drift from the fragment's two `let`s; changing the mirror is
rejected since the K5a gate pins exact op counts). So the func
proof feeds Slice B's abstract `compressWhile_correct` (which
needs only the five lookups) and continues existentially through
a new abstract add-back pair below — `shaAddBody` has no `let`s,
so its transfer is a single store plus counter with no value
tower. Only `st`/`v`/`j` lookups are threaded (the return reads
`st`; nothing downstream needs the `w`/`K`/`r` frame).
-/
import Circe.Crypto.ShaLoops
import Circe.Crypto.ShaOob

/-! ### Abstract add-back (existential post-envs, Slice B idiom) -/

/-- The add-back condition over an abstract env (mirrors
    `compressCond_lookup`). -/
theorem shaAddCond_lookup (ρ : Env) (j : Nat) (h : j < 2 ^ 64)
    (hρj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j))) :
    evalExpr (.ult (.var "j") (.lit (.u64 (BitVec.ofNat 64 8)))) ρ =
      .ok (.b (decide (j < 8))) := by
  have h8 : (BitVec.ofNat 64 8).toNat = 8 := ofNat64_toNat 8 (by decide)
  simp [evalExpr, hρj, litVal, ofNat64_ult j _ h, h8]

/-- One add-back iteration over an abstract env: `st[j] += v[j];
    j++`, with the post-env pinned by lookups (absolute for the
    evolving `st`/`j`, absolute values for the `v` frame). -/
theorem shaAddBody_transfer (F : Nat) (ρ : Env)
    (st vv : List (BitVec 32)) (j : Nat)
    (hj64 : j < 2 ^ 64)
    (hstlen : j < st.length) (hvlen : j < vv.length)
    (hρst : envLookup ρ "st" = some (.arr32 st))
    (hρv : envLookup ρ "v" = some (.arr32 vv))
    (hρj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j))) :
    ∃ ρ', evalStmtFuel F shaAddBody ρ = .ok (ρ', .fellThrough)
      ∧ envLookup ρ' "st" = some (.arr32 (st.set j (st[j] + vv[j])))
      ∧ envLookup ρ' "j" = some (.u64 (BitVec.ofNat 64 (j + 1)))
      ∧ envLookup ρ' "v" = some (.arr32 vv) := by
  have htoNat : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat j hj64
  have hij : evalExpr (.var "j") ρ =
      .ok (.u64 (BitVec.ofNat 64 j)) := by
    simp [evalExpr, hρj]
  have hget : st[j]? = some st[j] := List.getElem?_eq_getElem hstlen
  have hgetv : vv[j]? = some vv[j] := List.getElem?_eq_getElem hvlen
  have hv : evalExpr (.uadd (.idxu "st" (.var "j")) (.idxu "v" (.var "j")))
      ρ = .ok (.u32 (st[j] + vv[j])) := by
    simp only [evalExpr, hρst, hρv, hρj, htoNat, hget, hgetv]
  -- The store lemma wants the index in `toNat` form.
  have hgetArr : st[(BitVec.ofNat 64 j).toNat]? = some st[j] := by
    rw [htoNat]; exact hget
  obtain ⟨ρm, hu⟩ := envUpdate_some_of_lookup ρ "st"
    (.arr32 st)
    (.arr32 (st.set (BitVec.ofNat 64 j).toNat (st[j] + vv[j]))) hρst
  have hstm : envLookup ρm "st" =
      some (.arr32 (st.set (BitVec.ofNat 64 j).toNat (st[j] + vv[j]))) :=
    envLookup_envUpdate_same _ _ _ _ hu
  have hvm : envLookup ρm "v" = some (.arr32 vv) := by
    have h := envLookup_envUpdate_diff _ _ _ _ _ hu (by decide : "st" ≠ "v")
    rw [hρv] at h
    exact h
  have hjm : envLookup ρm "j" = some (.u64 (BitVec.ofNat 64 j)) := by
    have h := envLookup_envUpdate_diff _ _ _ _ _ hu (by decide : "st" ≠ "j")
    rw [hρj] at h
    exact h
  have harr := evalStmtFuel_arrSet F "st" (.var "j") _ _ _ _ _ _ _
    hij hv hρst hgetArr hu
  have huaddr : evalExpr (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
      ρm = .ok (.u64 (BitVec.ofNat 64 (j + 1))) := by
    simp only [evalExpr, hjm, litVal, ofNat64_add_one]
  obtain ⟨ρ', hu2⟩ := envUpdate_some_of_lookup ρm "j"
    (.u64 (BitVec.ofNat 64 j)) (.u64 (BitVec.ofNat 64 (j + 1))) hjm
  have hjj : envLookup ρ' "j" = some (.u64 (BitVec.ofNat 64 (j + 1))) :=
    envLookup_envUpdate_same _ _ _ _ hu2
  have hstt : envLookup ρ' "st" =
      some (.arr32 (st.set j (st[j] + vv[j]))) := by
    have h := envLookup_envUpdate_diff _ _ _ _ _ hu2 (by decide : "j" ≠ "st")
    rw [hstm, htoNat] at h
    exact h
  have hvv : envLookup ρ' "v" = some (.arr32 vv) := by
    have h := envLookup_envUpdate_diff _ _ _ _ _ hu2 (by decide : "j" ≠ "v")
    rw [hvm] at h
    exact h
  have hassign := evalStmtFuel_assign F "j" _ _ _ _ huaddr hu2
  have heval : evalStmtFuel F shaAddBody ρ = .ok (ρ', .fellThrough) := by
    rw [shaAddBody, evalStmtFuel_seq_fallthrough F _ _ _ _ harr, hassign]
  exact ⟨ρ', heval, hstt, hjj, hvv⟩

/-- The add-back loop evaluates to `shaAddBackN st0 vv 8` (fuel
    induction over abstract envs, mirroring `compressWhile_correct`
    with the K4 `addWhile_correct` step argument: the just-written
    cell pushes through `shaAddBackN_succ`, grounding both reads
    via `shaAddBackN_get_untouched` and the length facts). -/
theorem shaAddWhile_abs (F : Nat) (ρ : Env)
    (st0 vv : List (BitVec 32)) (j : Nat) (st : List (BitVec 32))
    (hj : j ≤ 8) (hst0len : 8 ≤ st0.length) (hvlen : 8 ≤ vv.length)
    (hρst : envLookup ρ "st" = some (.arr32 st))
    (hρv : envLookup ρ "v" = some (.arr32 vv))
    (hρj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
    (hst : st = shaAddBackN st0 vv j)
    (hF : 8 - j ≤ F) :
    ∃ ρ', evalStmtFuel F shaAddWhile ρ = .ok (ρ', .fellThrough)
      ∧ envLookup ρ' "st" = some (.arr32 (shaAddBackN st0 vv 8))
      ∧ envLookup ρ' "j" = some (.u64 (BitVec.ofNat 64 8))
      ∧ envLookup ρ' "v" = some (.arr32 vv) := by
  induction F generalizing ρ j st with
  | zero =>
    have hj8 : j = 8 := by omega
    subst hj8
    have hcond := shaAddCond_lookup ρ 8 (by decide) hρj
    have hcondF : evalExpr (.ult (.var "j")
          (.lit (.u64 (BitVec.ofNat 64 8)))) ρ =
        .ok (.b false) := by
      simpa using hcond
    have hdone : st = shaAddBackN st0 vv 8 := hst
    refine ⟨ρ, ?_, ?_, ?_, ?_⟩
    · simp [shaAddWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
        evalStmtWith, hcondF]
    · rw [← hdone]; exact hρst
    · exact hρj
    · exact hρv
  | succ F ih =>
    by_cases hlt : j < 8
    · have hj64 : j < 2 ^ 64 := by omega
      have hcond := shaAddCond_lookup ρ j hj64 hρj
      have hcondT : evalExpr (.ult (.var "j")
            (.lit (.u64 (BitVec.ofNat 64 8)))) ρ =
          .ok (.b true) := by
        simpa [hlt] using hcond
      have hstlen : j < st.length := by
        rw [hst, shaAddBackN_length]; omega
      have hvlenj : j < vv.length := by omega
      obtain ⟨ρm, hbody, hstm, hjm, hvm⟩ :=
        shaAddBody_transfer F ρ st vv j hj64 hstlen hvlenj
          hρst hρv hρj
      have hstep : evalStmtFuel (F + 1) shaAddWhile ρ
          = evalStmtFuel F shaAddWhile ρm := by
        simp [shaAddWhile, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcondT, hbody]
      rw [hstep]
      have hj' : j + 1 ≤ 8 := by omega
      have hAL : (shaAddBackN st0 vv j).length = st0.length :=
        shaAddBackN_length _ _ _
      have hjj : j < (shaAddBackN st0 vv j).length := by omega
      have hcell : (shaAddBackN st0 vv j)[j] = st0[j] := by
        have hunt := shaAddBackN_get_untouched st0 vv j j (Nat.le_refl j)
        have hget := List.getElem?_eq_getElem hjj
        have hgo := List.getElem?_eq_getElem (show j < st0.length by omega)
        rw [hget, hgo] at hunt
        exact Option.some_inj.mp hunt
      have hvv : vv[j] = vv[j]?.getD 0 :=
        (congrArg (·.getD 0)
          (List.getElem?_eq_getElem (show j < vv.length by omega))).symm
      -- `st` is a generalized variable occurring dependently
      -- (`st[j]`), so `rw [hst]` is ill-moded: `subst` it away instead.
      subst hst
      have hst' : (shaAddBackN st0 vv j).set j
          ((shaAddBackN st0 vv j)[j] + vv[j]) =
          shaAddBackN st0 vv (j + 1) := by
        have hst0 : st0[j] = st0[j]?.getD 0 :=
          (congrArg (·.getD 0)
            (List.getElem?_eq_getElem
              (show j < st0.length by omega))).symm
        rw [hcell, hvv, hst0, shaAddBackN_succ]
      have hρstm : envLookup ρm "st" =
          some (.arr32 (shaAddBackN st0 vv (j + 1))) := by
        rw [hst'] at hstm
        exact hstm
      exact ih ρm (j + 1) _ hj' hρstm hvm hjm rfl (by omega)
    · have hj8 : j = 8 := by omega
      subst hj8
      have hcond := shaAddCond_lookup ρ 8 (by decide) hρj
      have hcondF : evalExpr (.ult (.var "j")
            (.lit (.u64 (BitVec.ofNat 64 8)))) ρ =
          .ok (.b false) := by
        simpa using hcond
      have hdone : st = shaAddBackN st0 vv 8 := hst
      refine ⟨ρ, ?_, ?_, ?_, ?_⟩
      · simp [shaAddWhile, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcondF]
      · rw [← hdone]; exact hρst
      · exact hρj
      · exact hρv

/-- The counter twin at `8` is the closed-form add-back (the
    `shaAddBackN_eq` right side with `n = 8` is `shaAddBack` by
    definition). -/
theorem shaAddBackN_eight (s v : List (BitVec 32))
    (hs : 8 ≤ s.length) (hv : 8 ≤ v.length) :
    shaAddBackN s v 8 = shaAddBack s v := by
  rw [shaAddBackN_eq s v 8 hs hv]
  rfl

/-! ### Loop-post glue (mirror fill = spec prefix) -/

/-- Pointwise copy behavior (fuel induction: positions below
    the counter keep `w`, positions in `[t, t+f)` hold `st[8+·]`,
    later cells are untouched yet). -/
theorem initLoop_get (f t : Nat) (w s : List (BitVec 32)) (k : Nat)
    (hs : 8 + (t + f) ≤ s.length) (hw : w.length = 64)
    (hbf : t + f ≤ 16) :
    (initLoop f t w s)[k]? =
      if k < t then w[k]? else if k < t + f then s[8 + k]? else w[k]? := by
  induction f generalizing t w with
  | zero =>
    simp only [initLoop]
    by_cases h1 : k < t
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ k < t + 0 by omega)]
  | succ f ih =>
    rw [initLoop_succ]
    have hs' : 8 + ((t + 1) + f) ≤ s.length := by omega
    have hw' : (initStep w s t).length = 64 := by
      rw [initStep_length]; exact hw
    have hbf' : (t + 1) + f ≤ 16 := by omega
    rw [ih (t + 1) (initStep w s t) hs' hw' hbf']
    have hsome : s[8 + t]? = some s[8 + t] :=
      List.getElem?_eq_getElem (by omega)
    have hstep : (initStep w s t)[k]? =
        if k = t then s[8 + t]? else w[k]? := by
      by_cases hkt : k = t
      · rw [hkt, ite_eq_left rfl]
        simp only [initStep, hsome,
          List.getElem?_set_self (l := w) (i := t) (a := s[8 + t])
            (by omega)]
      · rw [ite_eq_right hkt]
        cases he : s[8 + t]? with
        | some x =>
          simp only [initStep, he, List.getElem?_set_ne (Ne.symm hkt)]
        | none => simp only [initStep, he]
    by_cases h1 : k < t
    · rw [ite_eq_left (show k < t + 1 by omega), hstep,
        ite_eq_right (show k ≠ t by omega), ite_eq_left h1]
    · by_cases h2 : k = t
      · rw [ite_eq_left (show k < t + 1 by omega), hstep, ite_eq_left h2,
          ite_eq_right h1, ite_eq_left (show k < t + (f + 1) by omega), h2]
      · have hn1 : ¬ k < t + 1 := by omega
        have hcond : t + 1 + f = t + (f + 1) := by omega
        rw [ite_eq_right hn1, ite_eq_right h1, hcond, hstep, ite_eq_right h2]

/-- Pointwise work-init behavior (same fuel induction over the
    digest head; no `+8` offset). -/
theorem vinitLoop_get (f i : Nat) (v s : List (BitVec 32)) (k : Nat)
    (hs : 24 ≤ s.length) (hv : v.length = 8) (hbf : i + f ≤ 8) :
    (vinitLoop f i v s)[k]? =
      if k < i then v[k]? else if k < i + f then s[k]? else v[k]? := by
  induction f generalizing i v with
  | zero =>
    simp only [vinitLoop]
    by_cases h1 : k < i
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ k < i + 0 by omega)]
  | succ f ih =>
    rw [vinitLoop_succ]
    have hs' : 24 ≤ s.length := hs
    have hv' : (vinitStep v s i).length = 8 := by
      rw [vinitStep_length]; exact hv
    have hbf' : (i + 1) + f ≤ 8 := by omega
    rw [ih (i + 1) (vinitStep v s i) hv' hbf']
    have hsome : s[i]? = some s[i] :=
      List.getElem?_eq_getElem (by omega)
    have hstep : (vinitStep v s i)[k]? =
        if k = i then s[i]? else v[k]? := by
      by_cases hkt : k = i
      · rw [hkt, ite_eq_left rfl]
        simp only [vinitStep, hsome,
          List.getElem?_set_self (l := v) (i := i) (a := s[i])
            (by omega)]
      · rw [ite_eq_right hkt]
        cases he : s[i]? with
        | some x =>
          simp only [vinitStep, he, List.getElem?_set_ne (Ne.symm hkt)]
        | none => simp only [vinitStep, he]
    by_cases h1 : k < i
    · rw [ite_eq_left (show k < i + 1 by omega), hstep,
        ite_eq_right (show k ≠ i by omega), ite_eq_left h1]
    · by_cases h2 : k = i
      · rw [ite_eq_left (show k < i + 1 by omega), hstep, ite_eq_left h2,
          ite_eq_right h1, ite_eq_left (show k < i + (f + 1) by omega), h2]
      · have hn1 : ¬ k < i + 1 := by omega
        have hcond : i + 1 + f = i + (f + 1) := by omega
        rw [ite_eq_right hn1, ite_eq_right h1, hcond, hstep, ite_eq_right h2]

/-- The block-copy loop fills the schedule head from the block
    tail (the func-level bridge into `schedLoop`). -/
theorem initLoop_full (s : List (BitVec 32)) (hs : 24 ≤ s.length) :
    initLoop 16 0 (List.replicate 64 0) s =
      (s.drop 8).take 16 ++ List.replicate 48 0 := by
  apply List.ext_getElem?
  intro k
  rw [initLoop_get 16 0 _ _ k (by omega) (by decide)
    (show 0 + 16 ≤ 16 by omega)]
  rw [ite_eq_right (show ¬ k < 0 by omega)]
  by_cases h2 : k < 0 + 16
  · have h2' : k < 16 := by omega
    rw [ite_eq_left h2, List.getElem?_append_left (show k <
      ((s.drop 8).take 16).length by simp [List.length_take]; omega)]
    rw [List.getElem?_take_of_lt h2', List.getElem?_drop]
  · have hge : 16 ≤ k := by omega
    rw [ite_eq_right h2]
    have htake : ((s.drop 8).take 16).length ≤ k := by
      simp [List.length_take]; omega
    have hlen16 : ((s.drop 8).take 16).length = 16 := by
      simp [List.length_take, List.length_drop]; omega
    rw [List.getElem?_append_right htake, hlen16]
    by_cases hk64 : k < 64
    · rw [List.getElem?_replicate_of_lt hk64,
        List.getElem?_replicate_of_lt (show k - 16 < 48 by omega)]
    · have hnk : 64 ≤ k := by omega
      rw [List.getElem?_eq_none
        (show (List.replicate 64 (0 : BitVec 32)).length ≤ k by
          simp; omega)]
      rw [List.getElem?_eq_none
        (show (List.replicate 48 (0 : BitVec 32)).length ≤ k - 16 by
          simp; omega)]

/-- The work-init loop fills the working vars from the digest head
    (the func-level bridge into `compressLoop`). -/
theorem vinitLoop_full (s : List (BitVec 32)) (hs : 24 ≤ s.length) :
    vinitLoop 8 0 (List.replicate 8 0) s = s.take 8 := by
  apply List.ext_getElem?
  intro k
  rw [vinitLoop_get 8 0 _ _ k hs (by decide)
    (show 0 + 8 ≤ 8 by omega)]
  rw [ite_eq_right (show ¬ k < 0 by omega)]
  by_cases h2 : k < 0 + 8
  · have h2' : k < 8 := by omega
    rw [ite_eq_left h2, List.getElem?_take_of_lt h2']
  · have hge : 8 ≤ k := by omega
    rw [ite_eq_right h2,
      List.getElem?_eq_none (show (s.take 8).length ≤ k by
        simp [List.length_take]; omega)]
    exact List.getElem?_eq_none
      (show (List.replicate 8 (0 : BitVec 32)).length ≤ k by simp; omega)

/-! ### Whole-function correctness -/

/-- Forward correctness at any sufficient fuel (mirrors
    `evalFuncFuel_chachaBlock`: the `let`s bridge by `rfl` to the
    phase envs through work-init, the loops plug in at handler
    level by unfolding; past `let r` the proof goes abstract
    through Slice B's `compressWhile_correct` and the pair above,
    since no exact compress env can bridge by `rfl`). -/
theorem evalFuncFuel_sha256 (F : Nat) (s : List (BitVec 32))
    (h24 : 24 ≤ s.length) (hF : 64 ≤ F) :
    evalFuncFuel F sha256Func [.arr32 s] = sha256FuncFwd s := by
  cases F with
  | zero => exact False.elim (by omega)
  | succ F =>
    have hbind : bindArgs
        [Param.mk "st" (.array (.u 32) 24) (.mutBorrow 0)]
        [.arr32 s] = some [("st", .arr32 s)] := rfl
    have hvarW : evalExpr (.lit (.arr32 (List.replicate 64 0)))
        [("st", .arr32 s)] =
        .ok (.arr32 (List.replicate 64 0)) := by
      simp [evalExpr, litVal]
    have hletW := evalStmtFuel_let_ (F + 1) "w" (.array (.u 32) 64)
      (.lit (.arr32 (List.replicate 64 0)))
      [("st", .arr32 s)] (.arr32 (List.replicate 64 0)) hvarW
    have henvW : envExtend [("st", .arr32 s)] "w"
        (.arr32 (List.replicate 64 0)) =
        [("w", .arr32 (List.replicate 64 0)), ("st", .arr32 s)] := rfl
    have hvarT : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("w", .arr32 (List.replicate 64 0)), ("st", .arr32 s)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletT := evalStmtFuel_let_ (F + 1) "t" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("w", .arr32 (List.replicate 64 0)), ("st", .arr32 s)]
      (.u64 (BitVec.ofNat 64 0)) hvarT
    have henvT : envExtend [("w", .arr32 (List.replicate 64 0)),
        ("st", .arr32 s)] "t" (.u64 (BitVec.ofNat 64 0)) =
        mkInitEnv s 0 (List.replicate 64 0) := rfl
    have hw0len : (List.replicate 64 (0 : BitVec 32)).length = 64 := by
      decide
    have hinv0 : initLoop (16 - 0) 0 (List.replicate 64 0) s =
        initLoop 16 0 (List.replicate 64 0) s := by rw [Nat.sub_zero]
    have hinit' : evalStmtFuel (F + 1) initWhile
        (mkInitEnv s 0 (List.replicate 64 0)) =
        .ok (mkInitEnv s 16 (initLoop 16 0 (List.replicate 64 0) s),
          .fellThrough) :=
      initWhile_correct (F + 1) s 0 _ _ (Nat.zero_le _) h24 hw0len
        hinv0 (by omega)
    have hvarU : evalExpr (.lit (.u64 (BitVec.ofNat 64 16)))
        (mkInitEnv s 16 (initLoop 16 0 (List.replicate 64 0) s)) =
        .ok (.u64 (BitVec.ofNat 64 16)) := by
      simp [evalExpr, litVal]
    have hletU := evalStmtFuel_let_ (F + 1) "u" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 16)))
      (mkInitEnv s 16 (initLoop 16 0 (List.replicate 64 0) s))
      (.u64 (BitVec.ofNat 64 16)) hvarU
    have henvU : envExtend
        (mkInitEnv s 16 (initLoop 16 0 (List.replicate 64 0) s)) "u"
        (.u64 (BitVec.ofNat 64 16)) =
        mkSchedEnv s 16 (initLoop 16 0 (List.replicate 64 0) s) := rfl
    have hW1len : (initLoop 16 0 (List.replicate 64 0) s).length = 64 := by
      rw [initLoop_length]; exact hw0len
    have hschedinv : schedLoop (64 - 16) 16
        (initLoop 16 0 (List.replicate 64 0) s) =
        schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s) := rfl
    have hsched' : evalStmtFuel (F + 1) schedWhile
        (mkSchedEnv s 16 (initLoop 16 0 (List.replicate 64 0) s)) =
        .ok (mkSchedEnv s 64
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)),
          .fellThrough) :=
      schedWhile_correct (F + 1) s 16 _ _ (by decide) (by decide)
        hW1len hschedinv (by omega)
    have hvarV : evalExpr (.lit (.arr32 (List.replicate 8 0)))
        (mkSchedEnv s 64
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))) =
        .ok (.arr32 (List.replicate 8 0)) := by
      simp [evalExpr, litVal]
    have hletV := evalStmtFuel_let_ (F + 1) "v" (.array (.u 32) 8)
      (.lit (.arr32 (List.replicate 8 0)))
      (mkSchedEnv s 64
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
      (.arr32 (List.replicate 8 0)) hvarV
    have henvV : envExtend (mkSchedEnv s 64
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))) "v"
        (.arr32 (List.replicate 8 0)) =
        [("v", .arr32 (List.replicate 8 0)),
         ("u", .u64 (BitVec.ofNat 64 64)),
         ("t", .u64 (BitVec.ofNat 64 16)),
         ("w", .arr32
           (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))),
         ("st", .arr32 s)] := rfl
    have hvarI : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("v", .arr32 (List.replicate 8 0)),
         ("u", .u64 (BitVec.ofNat 64 64)),
         ("t", .u64 (BitVec.ofNat 64 16)),
         ("w", .arr32
           (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))),
         ("st", .arr32 s)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletI := evalStmtFuel_let_ (F + 1) "i" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .arr32 (List.replicate 8 0)),
       ("u", .u64 (BitVec.ofNat 64 64)),
       ("t", .u64 (BitVec.ofNat 64 16)),
       ("w", .arr32
         (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))),
       ("st", .arr32 s)]
      (.u64 (BitVec.ofNat 64 0)) hvarI
    have henvI : envExtend [("v", .arr32 (List.replicate 8 0)),
        ("u", .u64 (BitVec.ofNat 64 64)),
        ("t", .u64 (BitVec.ofNat 64 16)),
        ("w", .arr32
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))),
        ("st", .arr32 s)] "i" (.u64 (BitVec.ofNat 64 0)) =
        mkVinitEnv s 0 (List.replicate 8 0)
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)) := rfl
    have hv0len : (List.replicate 8 (0 : BitVec 32)).length = 8 := by
      decide
    have hvinitinv : vinitLoop (8 - 0) 0 (List.replicate 8 0) s =
        vinitLoop 8 0 (List.replicate 8 0) s := by rw [Nat.sub_zero]
    have hvinit' : evalStmtFuel (F + 1) vinitWhile
        (mkVinitEnv s 0 (List.replicate 8 0)
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))) =
        .ok (mkVinitEnv s 8
          (vinitLoop 8 0 (List.replicate 8 0) s)
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)),
          .fellThrough) :=
      vinitWhile_correct (F + 1) s 0 _ _
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))
        (Nat.zero_le _) h24 hv0len hvinitinv (by omega)
    have hvarK : evalExpr (.lit (.arr32 shaK))
        (mkVinitEnv s 8
          (vinitLoop 8 0 (List.replicate 8 0) s)
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))) =
        .ok (.arr32 shaK) := by
      simp [evalExpr, litVal]
    have hletK := evalStmtFuel_let_ (F + 1) "K" (.array (.u 32) 64)
      (.lit (.arr32 shaK))
      (mkVinitEnv s 8
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
      (.arr32 shaK) hvarK
    have hvarR : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (mkVinitEnv s 8
          (vinitLoop 8 0 (List.replicate 8 0) s)
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
          "K" (.arr32 shaK)) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletR := evalStmtFuel_let_ (F + 1) "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (mkVinitEnv s 8
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
        "K" (.arr32 shaK))
      (.u64 (BitVec.ofNat 64 0)) hvarR
    -- Compress entry lookups over the two extends.
    have hρv : envLookup (envExtend (envExtend (mkVinitEnv s 8
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
        "K" (.arr32 shaK)) "r" (.u64 (BitVec.ofNat 64 0))) "v" =
        some (.arr32 (vinitLoop 8 0 (List.replicate 8 0) s)) := by
      simp [envExtend, envLookup, show ("v" : String) ≠ "r" by decide,
        show ("v" : String) ≠ "K" by decide, mkVinitEnv_v]
    have hρw : envLookup (envExtend (envExtend (mkVinitEnv s 8
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
        "K" (.arr32 shaK)) "r" (.u64 (BitVec.ofNat 64 0))) "w" =
        some (.arr32
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s))) := by
      simp [envExtend, envLookup, mkVinitEnv, show ("w" : String) ≠ "r" by decide,
        show ("w" : String) ≠ "K" by decide,
        show ("w" : String) ≠ "i" by decide,
        show ("w" : String) ≠ "v" by decide,
        show ("w" : String) ≠ "u" by decide,
        show ("w" : String) ≠ "t" by decide]
    have hρK : envLookup (envExtend (envExtend (mkVinitEnv s 8
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
        "K" (.arr32 shaK)) "r" (.u64 (BitVec.ofNat 64 0))) "K" =
        some (.arr32 shaK) := by
      simp [envExtend, envLookup, show ("K" : String) ≠ "r" by decide]
    have hρr : envLookup (envExtend (envExtend (mkVinitEnv s 8
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
        "K" (.arr32 shaK)) "r" (.u64 (BitVec.ofNat 64 0))) "r" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      simp [envExtend, envLookup]
    have hρst : envLookup (envExtend (envExtend (mkVinitEnv s 8
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
        "K" (.arr32 shaK)) "r" (.u64 (BitVec.ofNat 64 0))) "st" =
        some (.arr32 s) := by
      simp [envExtend, envLookup, show ("st" : String) ≠ "r" by decide,
        show ("st" : String) ≠ "K" by decide, mkVinitEnv_st]
    have hVVlen : (vinitLoop 8 0 (List.replicate 8 0) s).length = 8 := by
      rw [vinitLoop_length]; exact hv0len
    have hW2len : (schedLoop 48 16
        (initLoop 16 0 (List.replicate 64 0) s)).length = 64 := by
      rw [schedLoop_length]; exact hW1len
    have hloop0 : compressLoop (64 - 0) 0
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)) =
        compressLoop 64 0 (vinitLoop 8 0 (List.replicate 8 0) s)
          (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)) := by
      rw [Nat.sub_zero]
    obtain ⟨ρC, hcompress', hvvC, _, _, _, hstC⟩ :=
      compressWhile_correct (F + 1) (envExtend (envExtend (mkVinitEnv s 8
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16 (initLoop 16 0 (List.replicate 64 0) s)))
        "K" (.arr32 shaK)) "r" (.u64 (BitVec.ofNat 64 0)))
        s 0 _ _ _ (Nat.zero_le _) hVVlen hW2len
        hρv hρw hρK hρr hρst hloop0 (by omega)
    have hVClen : (compressLoop 64 0
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16
          (initLoop 16 0 (List.replicate 64 0) s))).length = 8 := by
      rw [compressLoop_length]; exact hVVlen
    have hvarJ : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρC =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletJ := evalStmtFuel_let_ (F + 1) "j" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      ρC (.u64 (BitVec.ofNat 64 0)) hvarJ
    have hρj1 : envLookup (envExtend ρC "j"
        (.u64 (BitVec.ofNat 64 0))) "j" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      simp [envExtend, envLookup]
    have hρst1 : envLookup (envExtend ρC "j"
        (.u64 (BitVec.ofNat 64 0))) "st" = some (.arr32 s) := by
      simp [envExtend, envLookup, show ("st" : String) ≠ "j" by decide, hstC]
    have hρv1 : envLookup (envExtend ρC "j"
        (.u64 (BitVec.ofNat 64 0))) "v" =
        some (.arr32 (compressLoop 64 0
          (vinitLoop 8 0 (List.replicate 8 0) s)
          (schedLoop 48 16
            (initLoop 16 0 (List.replicate 64 0) s)))) := by
      simp [envExtend, envLookup, show ("v" : String) ≠ "j" by decide, hvvC]
    have hstentry : s = shaAddBackN s (compressLoop 64 0
        (vinitLoop 8 0 (List.replicate 8 0) s)
        (schedLoop 48 16
          (initLoop 16 0 (List.replicate 64 0) s))) 0 := rfl
    obtain ⟨ρA, hshaadd', hstA, _, _⟩ :=
      shaAddWhile_abs (F + 1) (envExtend ρC "j"
        (.u64 (BitVec.ofNat 64 0))) s _ 0 s
        (Nat.zero_le _) (by omega) (by omega)
        hρst1 hρv1 hρj1 hstentry (by omega)
    have hvarRet : evalExpr (.var "st") ρA =
        .ok (.arr32 (shaAddBackN s (compressLoop 64 0
          (vinitLoop 8 0 (List.replicate 8 0) s)
          (schedLoop 48 16
            (initLoop 16 0 (List.replicate 64 0) s))) 8)) := by
      simp [evalExpr, hstA]
    have hret' : evalStmtFuel (F + 1) (.return_ (.var "st")) ρA =
        .ok (ρA, .returned (.arr32 (shaAddBackN s (compressLoop 64 0
          (vinitLoop 8 0 (List.replicate 8 0) s)
          (schedLoop 48 16
            (initLoop 16 0 (List.replicate 64 0) s))) 8))) :=
      evalStmtFuel_return _ _ _ _ hvarRet
    simp only [evalFuncFuel, sha256Func, hbind]
    rw [evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletW, henvW,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletT, henvT,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hinit',
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletU, henvU,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hsched',
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletV, henvV,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletI, henvI,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hvinit',
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletK,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletR,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hcompress',
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletJ,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hshaadd', hret']
    rw [shaAddBackN_eight s _ (by omega) (by omega),
      initLoop_full s h24, vinitLoop_full s h24]
    simp [sha256FuncFwd, h24, sha256CompressFwd]

/-- OOB corollary: a short input state fails loudly in the first
    loop (mirrors `evalFuncFuel_chachaBlock_oob`; the general
    `initWhile_oob` covers all `s.length < 24`, including inputs
    that survive the first iterations). -/
theorem evalFuncFuel_sha256_oob (F : Nat) (s : List (BitVec 32))
    (hshort : s.length < 24) (hF : 16 ≤ F) :
    evalFuncFuel F sha256Func [.arr32 s] = .error .OOB := by
  cases F with
  | zero => exact False.elim (by omega)
  | succ F =>
    have hbind : bindArgs
        [Param.mk "st" (.array (.u 32) 24) (.mutBorrow 0)]
        [.arr32 s] = some [("st", .arr32 s)] := rfl
    have hvarW : evalExpr (.lit (.arr32 (List.replicate 64 0)))
        [("st", .arr32 s)] =
        .ok (.arr32 (List.replicate 64 0)) := by
      simp [evalExpr, litVal]
    have hletW := evalStmtFuel_let_ (F + 1) "w" (.array (.u 32) 64)
      (.lit (.arr32 (List.replicate 64 0)))
      [("st", .arr32 s)] (.arr32 (List.replicate 64 0)) hvarW
    have henvW : envExtend [("st", .arr32 s)] "w"
        (.arr32 (List.replicate 64 0)) =
        [("w", .arr32 (List.replicate 64 0)), ("st", .arr32 s)] := rfl
    have hvarT : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("w", .arr32 (List.replicate 64 0)), ("st", .arr32 s)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletT := evalStmtFuel_let_ (F + 1) "t" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("w", .arr32 (List.replicate 64 0)), ("st", .arr32 s)]
      (.u64 (BitVec.ofNat 64 0)) hvarT
    have henvT : envExtend [("w", .arr32 (List.replicate 64 0)),
        ("st", .arr32 s)] "t" (.u64 (BitVec.ofNat 64 0)) =
        mkInitEnv s 0 (List.replicate 64 0) := rfl
    have hw0len : (List.replicate 64 (0 : BitVec 32)).length = 64 := by
      decide
    have hinitErr : evalStmtFuel (F + 1) initWhile
        (mkInitEnv s 0 (List.replicate 64 0)) = .error .OOB :=
      initWhile_oob (F + 1) s 0 _ (by decide) hshort hw0len (by omega)
    simp only [evalFuncFuel, sha256Func, hbind]
    rw [evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletW, henvW,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletT, henvT,
      evalStmtFuel_seq_err (F + 1) _ _ _ _ hinitErr]

/-- `emit_correct` for `sha256_compress` at the default fuel. -/
theorem emit_correct_sha256 (s : List (BitVec 32))
    (h24 : 24 ≤ s.length) (hfuel : 64 ≤ EVAL_FUEL) :
    evalFunc sha256Func [.arr32 s] = sha256FuncFwd s :=
  evalFuncFuel_sha256 EVAL_FUEL s h24 hfuel
