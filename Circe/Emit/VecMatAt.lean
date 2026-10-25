/-
Circe.Emit.VecMatAt — G2 flat-2D index read: the `mat_at` entry over
the N4d-iv-c `at()` reads.

The corpus (`tests/cpp/mat_at.cpp`: const-matrix `m`, `u64` `ncols` /
`i` / `j`, `i32` out) captures the entry + `size` + const-`at()` +
`_M_range_check` + `operator[]` leaves. The entry functionalizes to
a fused guard (the `at()`-throw precedent, the `vec_at_one` shape:
miss is `AssertFail`, including wrapping index computations that
land out of range) over the wrapping unsigned index computation
`i * ncols + j` (`umul` + `uadd` on `u64` — C++ unsigned arithmetic
wraps, the S3b precedent; no `nsw` anywhere). A call-per-entry
composer was considered and rejected the same way as G1: entries
fuse their single call into the read (the `vec_at_one` precedent).

Error precedence: the guard `fail` is the `at()`-throw precedent
(`AssertFail`); the live arithmetic is wrapping (no loud leg); the
forward is therefore the single checked read at the wrapped index.
-/
import Circe.Emit.VecRead
import Circe.Emit.VecAt

/-! ## G2: `mat_at` entry -/

/-- Mangled name of the flat-2D read entry. -/
def matAtName : String :=
  "_Z6mat_atRKSt6vectorIiSaIiEEmmm"

/-- The wrapping unsigned 2D index (`i * ncols + j`, CIR order). -/
def matAtIdx : CExpr :=
  .uadd (.umul (.var "i") (.var "ncols")) (.var "j")

/-- Canonical CoreIR for `mat_at`: the fused `at()` guard over the
    wrapped index, then the checked read (the `vec_at_one` shape). -/
def matAtFunc : Func :=
  ⟨matAtName,
   [{ name := "m", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "ncols", ty := .u 64, role := .owned },
    { name := "i", ty := .u 64, role := .owned },
    { name := "j", ty := .u 64, role := .owned }],
   .i 32,
   .if_ (.ult matAtIdx (.stdVecLen "m"))
     (.return_ (.stdVecAt "m" matAtIdx))
     .fail⟩

/-- Entry environment: `u64` dims + index, word list view. -/
def mkMatEnv (mL : List (BitVec 32)) (ncols i j : BitVec 64) : Env :=
  [("m", .stdVecVal mL), ("ncols", .u64 ncols),
   ("i", .u64 i), ("j", .u64 j)]

theorem mkMatEnv_m (mL : List (BitVec 32)) (ncols i j : BitVec 64) :
    envLookup (mkMatEnv mL ncols i j) "m" = some (.stdVecVal mL) := by
  simp [mkMatEnv, envLookup]

theorem mkMatEnv_ncols (mL : List (BitVec 32)) (ncols i j : BitVec 64) :
    envLookup (mkMatEnv mL ncols i j) "ncols" = some (.u64 ncols) := by
  simp [mkMatEnv, envLookup]

theorem mkMatEnv_i (mL : List (BitVec 32)) (ncols i j : BitVec 64) :
    envLookup (mkMatEnv mL ncols i j) "i" = some (.u64 i) := by
  simp [mkMatEnv, envLookup]

theorem mkMatEnv_j (mL : List (BitVec 32)) (ncols i j : BitVec 64) :
    envLookup (mkMatEnv mL ncols i j) "j" = some (.u64 j) := by
  simp [mkMatEnv, envLookup]

/-- Value-level forward: the single checked read at the wrapped
    index (miss is the `at()`-throw `AssertFail`). -/
def matAtFwd (l : List (BitVec 32)) (ncols i j : BitVec 64) :
    Result Value :=
  match l[(i * ncols + j).toNat]? with
  | some w => .ok (.i32 w)
  | none => .error .AssertFail

/-- `toNat` bridge for the wrapped index (the simplifier
    unfolds `toNat` over `*`/`+`; the statements keep the folded
    form that mirrors the model). -/
theorem matAtLin_toNat (ncols i j : BitVec 64) :
    (i * ncols + j).toNat = (i.toNat * ncols.toNat + j.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_add, BitVec.toNat_mul]

theorem matAtFwd_ok (l : List (BitVec 32)) (ncols i j : BitVec 64)
    (w : BitVec 32) (h : l[(i * ncols + j).toNat]? = some w) :
    matAtFwd l ncols i j = .ok (.i32 w) := by
  rw [matAtLin_toNat] at h
  simp [matAtFwd, h]

theorem matAtFwd_err (l : List (BitVec 32)) (ncols i j : BitVec 64)
    (h : l[(i * ncols + j).toNat]? = none) :
    matAtFwd l ncols i j = .error .AssertFail := by
  rw [matAtLin_toNat] at h
  simp [matAtFwd, h]

/-- The index computation evaluates to the wrapped `u64`. -/
theorem matAtIdx_eval (mL : List (BitVec 32)) (ncols i j : BitVec 64) :
    evalExpr matAtIdx (mkMatEnv mL ncols i j) =
      .ok (.u64 (i * ncols + j)) := by
  have hn := mkMatEnv_ncols mL ncols i j
  have hi := mkMatEnv_i mL ncols i j
  have hj := mkMatEnv_j mL ncols i j
  have hvi : evalExpr (.var "i") (mkMatEnv mL ncols i j) =
      .ok (.u64 i) := by simp [evalExpr, hi]
  have hvn : evalExpr (.var "ncols") (mkMatEnv mL ncols i j) =
      .ok (.u64 ncols) := by simp [evalExpr, hn]
  have hvj : evalExpr (.var "j") (mkMatEnv mL ncols i j) =
      .ok (.u64 j) := by simp [evalExpr, hj]
  have hmul : evalExpr (.umul (.var "i") (.var "ncols"))
      (mkMatEnv mL ncols i j) = .ok (.u64 (i * ncols)) :=
    evalExpr_umul_u64 _ _ _ _ _ hvi hvn
  have := evalExpr_uadd_u64 _ _ _ _ _ hmul hvj
  simpa [matAtIdx] using this

/-- The fused guard reads the wrapped index against the length. -/
theorem matAtGuard_eval (mL : List (BitVec 32)) (ncols i j : BitVec 64)
    (hlen64 : mL.length < 2 ^ 64) :
    evalExpr (.ult matAtIdx (.stdVecLen "m")) (mkMatEnv mL ncols i j) =
      .ok (.b (decide ((i * ncols + j).toNat < mL.length))) := by
  have hm := mkMatEnv_m mL ncols i j
  have hidx := matAtIdx_eval mL ncols i j
  have hlen : evalExpr (.stdVecLen "m") (mkMatEnv mL ncols i j) =
      .ok (.u64 (BitVec.ofNat 64 mL.length)) :=
    evalExpr_stdVecLen_some "m" _ mL hm
  have h := evalExpr_ult_u64 _ _ _ _ _ hidx hlen
  rw [BitVec.ult_eq_decide, ofNat64_toNat mL.length hlen64] at h
  exact h

/-- The entry theorem: evaluation agrees with the forward
    (hit reads, miss takes the fused `fail`). -/
theorem evalFuncFuel_matAt (mL : List (BitVec 32))
    (ncols i j : BitVec 64) (F : Nat)
    (hlen64 : mL.length < 2 ^ 64) :
    evalFuncFuel F matAtFunc
      [.stdVecVal mL, .u64 ncols, .u64 i, .u64 j] =
      matAtFwd mL ncols i j := by
  have hbind : bindArgs matAtFunc.args
      [.stdVecVal mL, .u64 ncols, .u64 i, .u64 j] =
      some [("m", .stdVecVal mL), ("ncols", .u64 ncols),
        ("i", .u64 i), ("j", .u64 j)] := rfl
  have hbody : matAtFunc.body =
      .if_ (.ult matAtIdx (.stdVecLen "m"))
        (.return_ (.stdVecAt "m" matAtIdx))
        .fail := rfl
  have henv : (mkMatEnv mL ncols i j) =
      [("m", .stdVecVal mL), ("ncols", .u64 ncols),
        ("i", .u64 i), ("j", .u64 j)] := rfl
  have hg := matAtGuard_eval mL ncols i j hlen64
  rw [henv] at hg
  by_cases h : (i * ncols + j).toNat < mL.length
  · have hne : mL[(i * ncols + j).toNat]? ≠ none := by
      rw [ne_eq, List.getElem?_eq_none_iff]
      omega
    obtain ⟨w, hget'⟩ := Option.ne_none_iff_exists.mp hne
    have hget : mL[(i * ncols + j).toNat]? = some w := hget'.symm
    have hc : evalExpr (.ult matAtIdx (.stdVecLen "m"))
        [("m", .stdVecVal mL), ("ncols", .u64 ncols),
          ("i", .u64 i), ("j", .u64 j)] = .ok (.b true) := by
      simp only [h] at hg
      exact hg
    have hfwd : matAtFwd mL ncols i j = .ok (.i32 w) :=
      matAtFwd_ok mL ncols i j w hget
    have hidx : evalExpr matAtIdx
        [("m", .stdVecVal mL), ("ncols", .u64 ncols),
          ("i", .u64 i), ("j", .u64 j)] =
        .ok (.u64 (i * ncols + j)) := by
      have := matAtIdx_eval mL ncols i j
      simpa [henv] using this
    have hm : envLookup
        [("m", .stdVecVal mL), ("ncols", .u64 ncols),
          ("i", .u64 i), ("j", .u64 j)] "m" =
        some (.stdVecVal mL) := by simp [envLookup]
    have hread : evalExpr (.stdVecAt "m" matAtIdx)
        [("m", .stdVecVal mL), ("ncols", .u64 ncols),
          ("i", .u64 i), ("j", .u64 j)] = .ok (.i32 w) :=
      evalExpr_stdVecAt_some "m" _ _ _ _ _ hm hidx hget
    have hstmt : evalStmtFuel F matAtFunc.body
        [("m", .stdVecVal mL), ("ncols", .u64 ncols),
          ("i", .u64 i), ("j", .u64 j)] =
        .ok ([("m", .stdVecVal mL), ("ncols", .u64 ncols),
          ("i", .u64 i), ("j", .u64 j)], .returned (.i32 w)) := by
      rw [hbody]
      exact (evalStmtFuel_if_true _ _ _ _ _ hc).trans
        (evalStmtFuel_return F _ _ _ hread)
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  · have hc : evalExpr (.ult matAtIdx (.stdVecLen "m"))
        [("m", .stdVecVal mL), ("ncols", .u64 ncols),
          ("i", .u64 i), ("j", .u64 j)] = .ok (.b false) := by
      simp only [h] at hg
      exact hg
    have hget : mL[(i * ncols + j).toNat]? = none := by
      rw [List.getElem?_eq_none_iff]
      omega
    have hfwd : matAtFwd mL ncols i j = .error .AssertFail :=
      matAtFwd_err mL ncols i j hget
    have hstmt : evalStmtFuel F matAtFunc.body
        [("m", .stdVecVal mL), ("ncols", .u64 ncols),
          ("i", .u64 i), ("j", .u64 j)] =
        .error .AssertFail := by
      rw [hbody]
      exact (evalStmtFuel_if_false _ _ _ _ _ hc).trans
        (evalStmtFuel_fail F _)
    simp [evalFuncFuel, hbind, hstmt, hfwd]
