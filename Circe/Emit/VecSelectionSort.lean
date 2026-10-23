/-
M4 iterative selection sort over `std::vector<int>`.

Corpus: `tests/cpp/vec_selection_sort.cpp` →
`tests/cir/vec_selection_sort.cir` (entry
`_Z18vec_selection_sortRSt6vectorIiSaIiEE`: one `mutBorrow`
vector, `void` out; outer index loop with a per-iteration
`cir.call` to the `min_index` leaf plus an unconditional swap;
leaf `_Z9min_indexRKSt6vectorIiSaIiEEm`: read-only borrow +
owned `lo`, `u64` out; forward min-scan with a conditional
`m` update).

Model (the `vecAt`/`vec_at_set` fusion precedents): the const
`at()` reads fuse into the pure reads (`stdVecAt`); both swap
writes carry the loop-guard shape (`i < len`, and `m ≤ len`
with `m` in-bounds by the scan invariant — the guard justifies
every access, so the model is total). The `slt` comparison on
`s32` maps to the plain signed less-than (total); the `u64`
counter bumps are the plain `.uadd` (exact below `2 ^ 64` by
the length bound, the `bv64_succ_toNat` idiom). Two fuels: the
outer scan consumes one program-fuel step per iteration while
the inner scan re-spends the full forward budget (self-contained
leaf — the M2 two-fuel idiom).
-/
import Circe.Emit.VecAtSet

namespace VecSelectionSort

/-- Leaf name (Itanium mangling of a `min_index` free function
    taking `const vector<int>&` + `unsigned long`, returning
    `unsigned long`). -/
def minIndexName : String :=
  "_Z9min_indexRKSt6vectorIiSaIiEEm"

/-- Entry name (Itanium mangling of a `vec_selection_sort` free
    function taking `vector<int>&`, returning `void`). -/
def vecSelectionSortName : String :=
  "_Z18vec_selection_sortRSt6vectorIiSaIiEE"

/-- Leaf step: conditional `m` update, `j` advances. -/
def minIndexStep : CStmt :=
  (.seq (.if_ (.slt (.stdVecAt "a" (.var "j"))
                    (.stdVecAt "a" (.var "m")))
          (.assign "m" (.var "j"))
          .skip)
    (.assign "j"
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- Leaf loop `while (j < len) step`. -/
def minIndexLoop : CStmt :=
  (.while_ (.ult (.var "j") (.stdVecLen "a")) minIndexStep)

/-- Leaf body: `m`/`j` prelude, forward min-scan, the minimum
    index returns. -/
def minIndexBody : CStmt :=
  (.seq (.let_ "m" (.u 64) (.var "lo"))
    (.seq (.let_ "j" (.u 64)
            (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq minIndexLoop
        (.return_ (.var "m")))))

/-- Leaf: read-only borrow + owned bound in, `u64` out. -/
def minIndexFunc : Func :=
  ⟨minIndexName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "lo", ty := .u 64, role := .owned }],
   .u 64,
   minIndexBody⟩

/-- Outer step: per-iteration leaf call, unconditional swap of
    `v[i]` with `v[m]`, `i` advances. -/
def selectionSortStep : CStmt :=
  (.seq (.callRet "m" minIndexName ["v", "i"])
    (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
      (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "m")))
        (.seq (.vecSet "v" (.var "m") (.var "t"))
          (.assign "i"
            (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))))))))

/-- Outer body: one step, looped. -/
def selectionSortBody : CStmt := selectionSortStep

/-- Outer loop `while (i < n) step`. -/
def selectionSortLoop : CStmt :=
  (.while_ (.ult (.var "i") (.var "n")) selectionSortStep)

/-- Whole function: `let_`-prelude binds `n` and `i`, the loop,
    then the updated words return (`xor_n` out-param idiom). -/
def vecSelectionSortFunc : Func :=
  ⟨vecSelectionSortName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 }],
   stdVecObjTy,
   (.seq (.let_ "n" (.u 64) (.stdVecLen "v"))
     (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq selectionSortLoop
         (.return_ (.var "v")))))⟩

/-- Program over which the entry evaluates (callee before entry,
    the `arraySortProg` precedent). -/
def vecSelectionSortProg : Prog := [minIndexFunc, vecSelectionSortFunc]

/-- Leaf environment (borrowed words + owned bound), in prelude
    `let_` cons order (`j` over `m` over `[a, lo]`, so the entry
    bridge is `rfl`). -/
def mkMinIndexEnv (l : List (BitVec 32))
    (lo : BitVec 64) (m j : BitVec 64) : Env :=
  [("j", .u64 j), ("m", .u64 m), ("lo", .u64 lo),
   ("a", .stdVecVal l)]

theorem mkMinIndexEnv_a (l : List (BitVec 32))
    (lo : BitVec 64) (m j : BitVec 64) :
    envLookup (mkMinIndexEnv l lo m j) "a" =
      some (.stdVecVal l) := by
  simp [mkMinIndexEnv, envLookup,
    show ("a" : String) ≠ "j" by decide,
    show ("a" : String) ≠ "m" by decide,
    show ("a" : String) ≠ "lo" by decide]

theorem mkMinIndexEnv_lo (l : List (BitVec 32))
    (lo : BitVec 64) (m j : BitVec 64) :
    envLookup (mkMinIndexEnv l lo m j) "lo" = some (.u64 lo) := by
  simp [mkMinIndexEnv, envLookup,
    show ("lo" : String) ≠ "j" by decide,
    show ("lo" : String) ≠ "m" by decide]

theorem mkMinIndexEnv_m (l : List (BitVec 32))
    (lo : BitVec 64) (m j : BitVec 64) :
    envLookup (mkMinIndexEnv l lo m j) "m" = some (.u64 m) := by
  simp [mkMinIndexEnv, envLookup, show ("m" : String) ≠ "j" by decide]

theorem mkMinIndexEnv_j (l : List (BitVec 32))
    (lo : BitVec 64) (m j : BitVec 64) :
    envLookup (mkMinIndexEnv l lo m j) "j" = some (.u64 j) := by
  simp [mkMinIndexEnv, envLookup]

/-- Outer environment (borrowed words + snapshot bound and
    index), in prelude `let_` cons order (`i` over `n` over
    `[v]`, so the entry bridge is `rfl`). -/
def mkSelectionSortEnv (l : List (BitVec 32))
    (n i : BitVec 64) : Env :=
  [("i", .u64 i), ("n", .u64 n), ("v", .stdVecVal l)]

theorem mkSelectionSortEnv_v (l : List (BitVec 32))
    (n i : BitVec 64) :
    envLookup (mkSelectionSortEnv l n i) "v" =
      some (.stdVecVal l) := by
  simp [mkSelectionSortEnv, envLookup,
    show ("v" : String) ≠ "i" by decide,
    show ("v" : String) ≠ "n" by decide]

theorem mkSelectionSortEnv_n (l : List (BitVec 32))
    (n i : BitVec 64) :
    envLookup (mkSelectionSortEnv l n i) "n" = some (.u64 n) := by
  simp [mkSelectionSortEnv, envLookup,
    show ("n" : String) ≠ "i" by decide]

theorem mkSelectionSortEnv_i (l : List (BitVec 32))
    (n i : BitVec 64) :
    envLookup (mkSelectionSortEnv l n i) "i" = some (.u64 i) := by
  simp [mkSelectionSortEnv, envLookup]

/-! ## Forward models (fuel-threaded, mirroring the loops) -/

/-- Leaf model: fuel + scan index + running minimum. Fuel 0
    returns the state so far; the `none` arms are unreachable
    in-invariant (every access is guard-justified: `j < len`
    from the loop guard, `m < len` from the scan invariant). -/
def minIndexFwd (l : List (BitVec 32)) :
    Nat → Nat → Nat → Result (Nat × Nat)
  | 0, j, m => .ok (m, j)
  | fuel + 1, j, m =>
    if _ : j < l.length then
      match l[j]? with
      | none => .error .AssertFail
      | some x =>
        match l[m]? with
        | none => .error .AssertFail
        | some y =>
          if x.slt y then minIndexFwd l fuel (j + 1) j
          else minIndexFwd l fuel (j + 1) m
    else .ok (m, j)

/-- Outer model: outer fuel + scan index. Each iteration
    re-spends the full inner budget (self-contained leaf); the
    swap writes through unconditionally. -/
def selectionSortFwd (l : List (BitVec 32)) :
    Nat → Nat → Nat → Result (Nat × List (BitVec 32))
  | 0, _, i => .ok (i, l)
  | fuel + 1, inner, i =>
    if _ : i < l.length then
      match minIndexFwd l inner (i + 1) i with
      | .error e => .error e
      | .ok (m, _) =>
        match l[i]?, l[m]? with
        | some x, some y =>
          selectionSortFwd ((l.set i y).set m x) fuel inner (i + 1)
        | _, _ => .error .AssertFail
    else .ok (i, l)

/-- Leaf whole-function forward: the scan at full-length fuel,
    then the minimum index word. -/
def vecMinIndexFwd (l : List (BitVec 32)) (lo : Nat) :
    Result Value :=
  match minIndexFwd l l.length (lo + 1) lo with
  | .error e => .error e
  | .ok (m, _) => .ok (.u64 (BitVec.ofNat 64 m))

/-- Whole-function forward: the outer loop at measure-exact fuel
    with a sufficient inner budget, then the words. -/
def vecSelectionSortFwd (l : List (BitVec 32)) :
    Result Value :=
  match selectionSortFwd l l.length l.length 0 with
  | .error e => .error e
  | .ok (_, l') => .ok (.stdVecVal l')

/-! ## M5a: pure selection-sort model + sort contract (N9 precedent).

The kernel compares with `slt` (signed), so ascending here means
`Pairwise (fun a b => b.slt a = false)` — the N9 `ult` shape with
the kernel's comparator. Order facts go through `toInt` + `omega`. -/

/-- `slt` is irreflexive (via `toInt`). -/
theorem slt_irrefl (x : BitVec 32) : (x.slt x) = false := by
  rw [BitVec.slt_eq_decide]
  simp

/-- `slt` is transitive (via `toInt` + `omega`). -/
theorem slt_trans {x y z : BitVec 32}
    (hxy : x.slt y = true) (hyz : y.slt z = true) :
    x.slt z = true := by
  rw [BitVec.slt_eq_decide] at hxy hyz ⊢
  simp only [decide_eq_true_eq] at hxy hyz ⊢
  omega

/-- `≥` is transitive (via `toInt` + `omega`): the skip-case fact. -/
theorem slt_ge_trans {y m r : BitVec 32}
    (h1 : (y.slt m) = false) (h2 : (m.slt r) = false) :
    (y.slt r) = false := by
  rw [BitVec.slt_eq_decide] at h1 h2 ⊢
  simp only [decide_eq_false_iff_not] at h1 h2 ⊢
  omega

/-- Take-case lower bound (via `toInt` + `omega`): a new strict
    minimum stays below every old lower bound (`x < ym ≤ x'`
    gives `x' ≥ x`). -/
theorem slt_lower_trans {x ym x' : BitVec 32}
    (hlt : (x.slt ym) = true) (hge : (x'.slt ym) = false) :
    (x'.slt x) = false := by
  rw [BitVec.slt_eq_decide] at hlt hge ⊢
  simp only [decide_eq_false_iff_not] at hge ⊢
  simp only [decide_eq_true_eq] at hlt
  omega

/-- Running minimum under `slt` (seeded fold). -/
def selMinAux (m : BitVec 32) : List (BitVec 32) → BitVec 32
  | [] => m
  | y :: ys => selMinAux (if y.slt m then y else m) ys

/-- The running minimum is always one of the candidates. -/
theorem selMinAux_mem (m : BitVec 32) (ys : List (BitVec 32)) :
    selMinAux m ys ∈ m :: ys := by
  induction ys generalizing m with
  | nil => exact List.Mem.head _
  | cons y ys ih =>
    by_cases h : y.slt m
    · simp only [selMinAux, ite_eq_left h]
      have hmem := ih y
      simp only [List.mem_cons] at hmem ⊢
      rcases hmem with h | h
      · rw [h]; exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · simp only [selMinAux, ite_eq_right h]
      have hmem := ih m
      simp only [List.mem_cons] at hmem ⊢
      rcases hmem with h | h
      · rw [h]; exact Or.inl rfl
      · exact Or.inr (Or.inr h)

/-- The running minimum is a lower bound of the candidates. -/
theorem selMinAux_le (m : BitVec 32) (ys : List (BitVec 32))
    (z : BitVec 32) (hz : z ∈ m :: ys) :
    (z.slt (selMinAux m ys)) = false := by
  induction ys generalizing m z with
  | nil =>
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hz
    subst hz
    exact slt_irrefl _
  | cons y ys ih =>
    by_cases h : y.slt m
    · have ht : (y.slt m) = true := h
      simp only [selMinAux, ite_eq_left h]
      have hle := ih y
      simp only [List.mem_cons] at hz
      -- NB: `rw`, not `rcases ... rfl`: `subst` would eliminate `m`.
      rcases hz with hzm | hzy | hz
      · rw [hzm]
        have hyr : (y.slt (selMinAux y ys)) = false :=
          hle _ (List.Mem.head _)
        by_cases hm : (m.slt (selMinAux y ys)) = true
        · exact absurd (slt_trans ht hm) (by simp [hyr])
        · have hf : (m.slt (selMinAux y ys)) = false := by
            cases hh : (m.slt (selMinAux y ys)) <;> simp_all
          exact hf
      · rw [hzy]
        exact hle _ (List.Mem.head _)
      · exact hle _ (List.mem_cons_of_mem _ hz)
    · have hf : (y.slt m) = false := by
        cases hh : (y.slt m) <;> simp_all
      simp only [selMinAux, ite_eq_right h]
      have hle := ih m
      simp only [List.mem_cons] at hz
      rcases hz with hzm | hzy | hz
      · rw [hzm]
        exact hle _ (List.Mem.head _)
      · rw [hzy]
        exact slt_ge_trans hf (hle _ (List.Mem.head _))
      · exact hle _ (List.mem_cons_of_mem _ hz)

/-- Minimum of a list (`0` default on empty; M5 only calls it on
    nonempty suffixes). -/
def selMin : List (BitVec 32) → BitVec 32
  | [] => BitVec.ofNat 32 0
  | x :: xs => selMinAux x xs

/-- The minimum belongs to a nonempty list. -/
theorem selMin_mem {x : BitVec 32} {xs : List (BitVec 32)} :
    selMin (x :: xs) ∈ x :: xs := by
  simp only [selMin]
  exact selMinAux_mem x xs

/-- The minimum lower-bounds a nonempty list. -/
theorem selMin_le {x : BitVec 32} {xs : List (BitVec 32)}
    {z : BitVec 32} (hz : z ∈ x :: xs) :
    (z.slt (selMin (x :: xs))) = false := by
  simp only [selMin]
  exact selMinAux_le x xs z hz

/-- Pure selection sort, fuel-indexed (house style: structural
    on fuel, so every call site unfolds by `simp only`). -/
def selectionSortListAux : Nat → List (BitVec 32) → List (BitVec 32)
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, x :: xs =>
    selMin (x :: xs) ::
      selectionSortListAux f ((x :: xs).erase (selMin (x :: xs)))

/-- Pure selection sort: repeatedly emit the minimum. -/
def selectionSortList (l : List (BitVec 32)) : List (BitVec 32) :=
  selectionSortListAux l.length l

/-- Joint sort contract at bounded fuel (one induction: sortedness
    needs the tail permutation for membership transport, so both go
    together; N9 proves them separately only because insertion keeps
    the tail literally in place). -/
theorem selectionSortListAux_spec : ∀ (n : Nat) (l : List (BitVec 32)),
    l.length ≤ n →
    (selectionSortListAux n l).Pairwise (fun a b => b.slt a = false) ∧
    List.Perm (selectionSortListAux n l) l := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have hempty : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hempty
    simp only [selectionSortListAux]
    exact ⟨List.Pairwise.nil, List.Perm.rfl⟩
  | succ n ih =>
    intro l hl
    cases l with
    | nil =>
      simp only [selectionSortListAux]
      exact ⟨List.Pairwise.nil, List.Perm.rfl⟩
    | cons x xs =>
      have hmem : selMin (x :: xs) ∈ x :: xs := selMin_mem
      have hlen : ((x :: xs).erase (selMin (x :: xs))).length ≤ n := by
        have h := List.length_erase_of_mem hmem
        simp only [List.length_cons] at hl h ⊢
        omega
      have ih' := ih _ hlen
      have hperm : List.Perm
          (selectionSortListAux n ((x :: xs).erase (selMin (x :: xs))))
          ((x :: xs).erase (selMin (x :: xs))) := ih'.2
      have hstep : selectionSortListAux (n + 1) (x :: xs) =
          selMin (x :: xs) ::
            selectionSortListAux n ((x :: xs).erase (selMin (x :: xs))) := by
        simp only [selectionSortListAux]
      have hsorted : (selectionSortListAux (n + 1) (x :: xs)).Pairwise
          (fun a b => b.slt a = false) := by
        rw [hstep, List.pairwise_cons]
        refine ⟨fun z hz => ?_, ih'.1⟩
        exact selMin_le (List.mem_of_mem_erase
          (hperm.mem_iff.mp hz))
      have hperm' : List.Perm (selectionSortListAux (n + 1) (x :: xs))
          (x :: xs) := by
        rw [hstep]
        exact (ih'.2.cons _).trans (List.perm_cons_erase hmem).symm
      exact ⟨hsorted, hperm'⟩

/-- Pure selection sort is ascending (N9 shape). -/
theorem selectionSortList_sorted (l : List (BitVec 32)) :
    (selectionSortList l).Pairwise (fun a b => b.slt a = false) :=
  (selectionSortListAux_spec l.length l (Nat.le_refl _)).1

/-- Pure selection sort permutes its input (erase-then-cons). -/
theorem selectionSortList_perm (l : List (BitVec 32)) :
    List.Perm (selectionSortList l) l :=
  (selectionSortListAux_spec l.length l (Nat.le_refl _)).2

end VecSelectionSort
