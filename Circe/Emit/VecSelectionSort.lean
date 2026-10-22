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

end VecSelectionSort
