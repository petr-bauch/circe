/-
Circe.Emit.ArraySort — N9 insertion sort over `std::array<uint32_t, 4>`:
the `__array_traits::_S_ref` unchecked-index leaf (u32 monomorph) +
mutating `operator[]` + the sort loop + the `array_sort_sum` entry.

Fusion follows the N4d-i precedent one level up: the subscript-call +
load fuses into the `idxu` read downstream, and the subscript-call +
`cir.store` fuses into `arrSet` downstream (the call itself is a pure
projection, so the fused read is harmless). `_S_ref` still validates
separately (same value story), so misshapen variants of either def
reject loudly. The `while` condition's short-circuit `&&`
(`cir.ternary` over `j > 0`) maps to `tif` (lazy in the untaken arm,
so index `j - 1` never evaluates at `j = 0`); `cir.dec` fuses to
`usub`-one like `cir.inc` fuses to `uadd`-one.

The sort returns the array (C++ `void` functionalizes as threaded
state, the `push_back` precedent), so the entry communicates with it
by value like every N7 composer.
-/
import Circe.Emit.Fragment

/-! ## N9: `std::array<uint32_t, 4>` sort leaves, loop, entry -/

/-- Mangled callee names in `tests/cpp/array_sort_sum.cpp`. -/
def arrayRefU32Name : String :=
  "_ZNSt14__array_traitsIjLm4EE6_S_refERA4_Kjm"
def arrayAtU32Name : String := "_ZNSt5arrayIjLm4EEixEm"
def insertionSortName : String := "_Z14insertion_sortRSt5arrayIjLm4EE"
def arraySortSumName : String := "_Z14array_sort_sumv"

/-- Canonical CoreIR for the u32 `_S_ref` leaf: unchecked `u64` index
    into the 4-word `u32` array (`cir.get_element`, OOB is UB so the
    model reports `OOB`). -/
def arrayRefU32Func : Func :=
  ⟨arrayRefU32Name,
   [{ name := "t", ty := .array (.u 32) 4, role := .sharedBorrow },
    { name := "n", ty := .u 64, role := .owned }],
   .u 32,
   .return_ (.idxu "t" (.var "n"))⟩

/-- Canonical CoreIR for the mutating `operator[]`: the `_M_elems`
    projection + `_S_ref` call fused into the `idxu` read (the store
    path fuses into `arrSet` downstream instead). -/
def arrayAtU32Func : Func :=
  ⟨arrayAtU32Name,
   [{ name := "a", ty := .array (.u 32) 4, role := .mutBorrow 0 },
    { name := "n", ty := .u 64, role := .owned }],
   .u 32,
   .return_ (.idxu "a" (.var "n"))⟩

/-- Canonical CoreIR for `insertion_sort`: outer `for`-as-`while`
    over `i in [1, N)`, inner `while` over the short-circuit
    condition, swap via temp + two `arrSet`s, counters via
    `assign`. -/
def insertionSortFunc (N : Nat) : Func :=
  ⟨insertionSortName,
   [{ name := "a", ty := .array (.u 32) N, role := .mutBorrow 0 }],
   .array (.u 32) N,
   .seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.while_ (.ult (.var "i") (.lit (.u64 (BitVec.ofNat 64 N))))
     (.seq (.let_ "j" (.u 64) (.var "i"))
     (.seq (.while_
       (.tif (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j"))
         (.ult (.idxu "a" (.var "j"))
           (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
         (.lit (.b false)))
       (.seq (.let_ "t" (.u 32) (.idxu "a" (.var "j")))
       (.seq (.arrSet "a" (.var "j")
                (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
       (.seq (.arrSet "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
                (.var "t"))
         (.assign "j" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))))))
       (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))))))
   (.return_ (.var "a")))⟩

/-- Canonical CoreIR for `array_sort_sum`: const-record init (the
    `trailing_zeros` fourth word folded in), sort call, four indexed
    reads, three wrapping adds. -/
def arraySortSumEntryFunc : Func :=
  ⟨arraySortSumName, [], .u 32,
   .seq (.let_ "a" (.array (.u 32) 4)
     (.lit (.arr32 [BitVec.ofNat 32 3, BitVec.ofNat 32 1,
       BitVec.ofNat 32 2, BitVec.ofNat 32 0])))
   (.seq (.callProg "s" insertionSortName ["a"])
   (.seq (.let_ "i0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq (.callRet "e0" arrayAtU32Name ["s", "i0"])
   (.seq (.let_ "i1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.callRet "e1" arrayAtU32Name ["s", "i1"])
   (.seq (.let_ "i2" (.u 64) (.lit (.u64 (BitVec.ofNat 64 2))))
   (.seq (.callRet "e2" arrayAtU32Name ["s", "i2"])
   (.seq (.let_ "i3" (.u 64) (.lit (.u64 (BitVec.ofNat 64 3))))
   (.seq (.callRet "e3" arrayAtU32Name ["s", "i3"])
          (.return_ (.uadd (.uadd (.uadd (.var "e0") (.var "e1"))
            (.var "e2")) (.var "e3"))))))))))))⟩

/-- Value-level forward for the u32 `_S_ref`: the word at `u64` index
    `n`, `OOB` off the end. -/
def arrayRefU32Fwd (l : List (BitVec 32)) (n : BitVec 64) :
    Result Value :=
  match l[n.toNat]? with
  | some x => .ok (.u32 x)
  | none => .error .OOB

/-- Value-level forward for the mutating `operator[]`: the same read
    (the call edge is fused, so the forward is the leaf forward by
    definition). -/
def arrayAtU32Fwd (l : List (BitVec 32)) (n : BitVec 64) :
    Result Value :=
  arrayRefU32Fwd l n

theorem arrayAtU32Fwd_is_call (l : List (BitVec 32)) (n : BitVec 64) :
    arrayAtU32Fwd l n = arrayRefU32Fwd l n := rfl

/-- Pure insertion sort over words (structural; the forward below runs
    it and wraps the result back into an array value). Insert before
    the first strictly greater word: equal words keep their relative
    order, matching the loop (which swaps only on strict `>`). -/
def insertU32 (x : BitVec 32) : List (BitVec 32) → List (BitVec 32)
  | [] => [x]
  | y :: ys => if x.ult y then x :: y :: ys else y :: insertU32 x ys

def insertionSortList : List (BitVec 32) → List (BitVec 32)
  | [] => []
  | x :: xs => insertU32 x (insertionSortList xs)

/-- Value-level forward for `insertion_sort`: the sorted array. -/
def insertionSortFwd (l : List (BitVec 32)) : Result Value :=
  .ok (.arr32 (insertionSortList l))

/-- Value-level forward for `array_sort_sum`: sort `[3, 1, 2, 0]`,
    add the four words (wrapping). -/
def arraySortSumEntryFwd : Result Value :=
  .ok (.u32 ((insertionSortList [BitVec.ofNat 32 3, BitVec.ofNat 32 1,
    BitVec.ofNat 32 2, BitVec.ofNat 32 0]).foldl (· + ·) (BitVec.ofNat 32 0)))

/-! ## N9-iii: emit-correctness (leaves, loop, entry) -/

/-- Env facts for the u32 `_S_ref` shape. -/
theorem envLookup_arrayRefU32_t (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("t", .arr32 l), ("n", .u64 n)] "t" =
      some (.arr32 l) := by
  simp [envLookup]

theorem envLookup_arrayRefU32_n (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("t", .arr32 l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
  simp [envLookup, show ("n" : String) ≠ "t" by decide]

/-- `emit_correct` for the u32 `_S_ref` (all inputs, hit and `OOB`
    paths; the i32 `evalFuncFuel_arrayRef` proof with `idxu`). -/
theorem evalFuncFuel_arrayRefU32 (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) :
    evalFuncFuel F arrayRefU32Func [.arr32 l, .u64 n] =
      arrayRefU32Fwd l n := by
  have hbind : bindArgs arrayRefU32Func.args [.arr32 l, .u64 n] =
      some [("t", .arr32 l), ("n", .u64 n)] := rfl
  have hbody : arrayRefU32Func.body =
      .return_ (.idxu "t" (.var "n")) := rfl
  have ht := envLookup_arrayRefU32_t l n
  have hn := envLookup_arrayRefU32_n l n
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, arrayRefU32Fwd, ht, hn] <;>
    (cases h : l[n.toNat]? <;> simp [h])

/-- Env facts for the mutating `operator[]` shape. -/
theorem envLookup_arrayAtU32_a (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("a", .arr32 l), ("n", .u64 n)] "a" =
      some (.arr32 l) := by
  simp [envLookup]

theorem envLookup_arrayAtU32_n (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("a", .arr32 l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
  simp [envLookup, show ("n" : String) ≠ "a" by decide]

/-- `emit_correct` for the mutating `operator[]` (same read, fused
    call edge; the i32 `evalFuncFuel_arrayAt` proof with `idxu`). -/
theorem evalFuncFuel_arrayAtU32 (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) :
    evalFuncFuel F arrayAtU32Func [.arr32 l, .u64 n] =
      arrayAtU32Fwd l n := by
  have hbind : bindArgs arrayAtU32Func.args [.arr32 l, .u64 n] =
      some [("a", .arr32 l), ("n", .u64 n)] := rfl
  have hbody : arrayAtU32Func.body =
      .return_ (.idxu "a" (.var "n")) := rfl
  have ha := envLookup_arrayAtU32_a l n
  have hn := envLookup_arrayAtU32_n l n
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, arrayAtU32Fwd, arrayRefU32Fwd, ha, hn] <;>
    (cases h : l[n.toNat]? <;> simp [h])

/-! ## N9-iii: pure-list infrastructure (take/drop, order, insert) -/

/-- A hit `getElem?` is in bounds. -/
theorem lt_of_getElem?_some {α : Type} {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · exact hlt
  · rw [List.getElem?_eq_none hge] at h
    cases h

/-- `take (j+1)` splits at a hit index. -/
theorem take_succ_of_getElem? {α : Type} (l : List α) (j : Nat) (z : α)
    (h : l[j]? = some z) : l.take (j + 1) = l.take j ++ [z] := by
  induction j generalizing l with
  | zero =>
    cases l with
    | nil => cases h
    | cons y ys => cases h; rfl
  | succ j ih =>
    cases l with
    | nil => cases h
    | cons y ys =>
      show y :: ys.take (j + 1) = (y :: ys.take j) ++ [z]
      rw [List.cons_append, ih _ h]

/-- `drop j` exposes a hit index. -/
theorem drop_of_getElem? {α : Type} (l : List α) (j : Nat) (z : α)
    (h : l[j]? = some z) : l.drop j = z :: l.drop (j + 1) := by
  induction j generalizing l with
  | zero =>
    cases l with
    | nil => cases h
    | cons y ys => cases h; rfl
  | succ j ih =>
    cases l with
    | nil => cases h
    | cons y ys => exact ih _ h

/-- A hit index splits the list in three. -/
theorem split_of_getElem? {α : Type} (l : List α) (j : Nat) (z : α)
    (h : l[j]? = some z) :
    l = l.take j ++ z :: l.drop (j + 1) := by
  induction j generalizing l with
  | zero =>
    cases l with
    | nil => cases h
    | cons y ys => cases h; rfl
  | succ j ih =>
    cases l with
    | nil => cases h
    | cons y ys =>
      show y :: ys = (y :: ys.take j) ++ z :: ys.drop (j + 1)
      rw [List.cons_append]
      exact congrArg _ (ih _ h)

/-- BitVec `ult` is asymmetric (via `toNat`). -/
theorem bv_ult_asymm {w : Nat} (x y : BitVec w)
    (h : x.ult y = true) : y.ult x = false := by
  rw [BitVec.ult_eq_decide] at h
  have h1 : x.toNat < y.toNat := of_decide_eq_true h
  rw [BitVec.ult_eq_decide]
  exact decide_eq_false (by omega : ¬ y.toNat < x.toNat)

/-- `¬(_ = true)` to `_ = false` (for feeding `by_cases`
    negations into `simp` without the hypothesis-normalization
    round trip). -/
theorem bool_eq_false_of_not_true {b : Bool} (h : ¬ b = true) :
    b = false := by
  cases b with
  | true => exact absurd rfl h
  | false => rfl

/-- BitVec `≤` (as `ult = false`) is transitive (via `toNat`). -/
theorem bv_le_trans {w : Nat} (x y z : BitVec w)
    (h1 : y.ult x = false) (h2 : z.ult y = false) :
    z.ult x = false := by
  have n1 : ¬ (y.ult x) = true := fun hc => by rw [h1] at hc; cases hc
  have n2 : ¬ (z.ult y) = true := fun hc => by rw [h2] at hc; cases hc
  have g1 : ¬ y.toNat < x.toNat := by
    intro hlt
    apply n1
    rw [BitVec.ult_eq_decide]
    exact decide_eq_true hlt
  have g2 : ¬ z.toNat < y.toNat := by
    intro hlt
    apply n2
    rw [BitVec.ult_eq_decide]
    exact decide_eq_true hlt
  have g3 : ¬ z.toNat < x.toNat := by omega
  rw [BitVec.ult_eq_decide]
  exact decide_eq_false g3

/-- BitVec `ult` is transitive (via `toNat`; for the commute
    inconsistency leaves). -/
theorem bv_ult_trans {w : Nat} (x y z : BitVec w)
    (h1 : x.ult y = true) (h2 : y.ult z = true) :
    x.ult z = true := by
  rw [BitVec.ult_eq_decide] at h1
  rw [BitVec.ult_eq_decide] at h2
  rw [BitVec.ult_eq_decide]
  simp only [decide_eq_true_eq] at h1 h2 ⊢
  omega

/-- Antisymmetry: no strict cycle means equality (via `toNat`;
    for the commute equal-words leaf). -/
theorem bv_eq_of_not_ult_both (a b : BitVec 32)
    (h1 : ¬ a.ult b = true) (h2 : ¬ b.ult a = true) : a = b := by
  have g1 : ¬ a.toNat < b.toNat := by
    intro hlt
    apply h1
    rw [BitVec.ult_eq_decide]
    exact decide_eq_true hlt
  have g2 : ¬ b.toNat < a.toNat := by
    intro hlt
    apply h2
    rw [BitVec.ult_eq_decide]
    exact decide_eq_true hlt
  have heq : a.toNat = b.toNat := by omega
  exact BitVec.toNat_inj.mp heq

/-- `envUpdate` on the updated key reads back the new value. -/
theorem envLookup_envUpdate_same (ρ : Env) (x : String) (v : Value)
    (ρ' : Env) (hu : envUpdate ρ x v = some ρ') :
    envLookup ρ' x = some v := by
  induction ρ generalizing ρ' with
  | nil => cases hu
  | cons kv tl ih =>
    simp only [envUpdate] at hu
    by_cases heq : x = kv.1
    · simp only [heq, ite_true] at hu
      cases hu
      simp [envLookup, heq]
    · simp only [heq, ite_false] at hu
      cases he : envUpdate tl x v with
      | none => simp [he] at hu
      | some rest' =>
        simp [he] at hu
        cases hu
        simp only [envLookup, heq, ite_false]
        exact ih _ he

/-- `envUpdate` leaves other keys alone. -/
theorem envLookup_envUpdate_diff (ρ : Env) (x y : String) (v : Value)
    (ρ' : Env) (hu : envUpdate ρ x v = some ρ') (hne : x ≠ y) :
    envLookup ρ' y = envLookup ρ y := by
  induction ρ generalizing ρ' with
  | nil => cases hu
  | cons kv tl ih =>
    simp only [envUpdate] at hu
    by_cases heq : x = kv.1
    · simp only [heq, ite_true] at hu
      cases hu
      have hney : y ≠ kv.1 := by rw [← heq]; exact Ne.symm hne
      simp [envLookup, heq, hney]
    · simp only [heq, ite_false] at hu
      cases he : envUpdate tl x v with
      | none => simp [he] at hu
      | some rest' =>
        simp [he] at hu
        cases hu
        simp only [envLookup]
        by_cases hy : y = kv.1
        · simp [hy]
        · simp [hy, ih _ he]

/-- A bound key always updates successfully. -/
theorem envUpdate_some_of_lookup (ρ : Env) (x : String) (v w : Value)
    (h : envLookup ρ x = some v) :
    ∃ ρ', envUpdate ρ x w = some ρ' := by
  induction ρ with
  | nil => simp [envLookup] at h
  | cons kv tl ih =>
    simp only [envLookup] at h
    by_cases heq : x = kv.1
    · simp only [heq, ite_true] at h
      cases h
      exact ⟨(kv.1, w) :: tl, by simp [envUpdate, heq]⟩
    · simp only [heq, ite_false] at h
      obtain ⟨ρ', hu⟩ := ih h
      exact ⟨(kv.1, kv.2) :: ρ',
        by simp [envUpdate, heq, hu]⟩

/-- `take` of the full length is identity. -/
theorem take_all {α : Type} (l : List α) : l.take l.length = l := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- `drop` of the full length is empty. -/
theorem drop_all {α : Type} (l : List α) : l.drop l.length = [] := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- `take 0` is empty (definitional, named for rewriting). -/
theorem take_zero' {α : Type} (l : List α) : l.take 0 = [] := rfl

/-- `drop 0` is identity (definitional, named for rewriting). -/
theorem drop_zero' {α : Type} (l : List α) : l.drop 0 = l := rfl

/-- `take` at the split point recovers the prefix. -/
theorem take_append_self {α : Type} (A B : List α) :
    (A ++ B).take A.length = A := by
  have hz : A.length - A.length = 0 := by omega
  rw [List.take_append, hz, take_zero', take_all, List.append_nil]

/-- `drop` at the split point recovers the suffix. -/
theorem drop_append_self {α : Type} (A B : List α) :
    (A ++ B).drop A.length = B := by
  have hz : A.length - A.length = 0 := by omega
  rw [List.drop_append, hz, drop_zero', drop_all, List.nil_append]

/-- Indexing past the split point lands in the suffix. -/
theorem getElem?_append_add {α : Type} (A B : List α) (k : Nat) :
    (A ++ B)[A.length + k]? = B[k]? := by
  induction A with
  | nil => simp
  | cons a as ih =>
    have e : as.length + 1 + k = (as.length + k) + 1 := by omega
    simp only [List.cons_append, List.length_cons] at *
    rw [e]
    exact ih

/-- `take m` has length `m` when `m` fits. -/
theorem take_length_eq {α : Type} (l : List α) (m : Nat)
    (h : m ≤ l.length) :
    (l.take m).length = m := by
  induction m generalizing l with
  | zero => rfl
  | succ m ih =>
    cases l with
    | nil =>
      simp only [List.length_nil] at h
      omega
    | cons a as =>
      show ((a :: as.take m).length) = _
      have hm : m ≤ as.length := by
        simp only [List.length_cons] at h
        omega
      simp [ih as hm]

/-- The swap body in take/drop form: writing `v` at `m+1` then `w`
    at `m` splices both words in (needs only the length bound, no
    value hypotheses). Proved by induction on `m`; the zero case
    computes by `rfl`, the step case peels one `cons`. -/
theorem set_take_drop (l : List (BitVec 32)) (m : Nat)
    (v w : BitVec 32) (hlen : m + 2 ≤ l.length) :
    ((l.set (m + 1) v).set m w) =
      l.take m ++ [w, v] ++ l.drop (m + 2) := by
  induction m generalizing l with
  | zero =>
    cases l with
    | nil =>
      simp only [List.length_nil] at hlen
      omega
    | cons a as =>
      cases as with
      | nil =>
        simp only [List.length_cons, List.length_nil] at hlen
        omega
      | cons b bs => rfl
  | succ m ih =>
    cases l with
    | nil =>
      simp only [List.length_nil] at hlen
      omega
    | cons a as =>
      have hlen' : m + 2 ≤ as.length := by
        simp only [List.length_cons] at hlen
        omega
      have e := ih as hlen'
      show a :: ((as.set (m + 1) v).set m w) =
        (a :: as.take m) ++ [w, v] ++ as.drop (m + 2)
      rw [e]
      simp [List.append_assoc]

/-- BitVec `ult` is irreflexive (via `toNat`). -/
theorem bv_ult_irrefl {w : Nat} (x : BitVec w) : x.ult x = false := by
  rw [BitVec.ult_eq_decide]
  exact decide_eq_false (by simp)

/-- Insert preserves length. -/
theorem insertU32_length (x : BitVec 32) (l : List (BitVec 32)) :
    (insertU32 x l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [insertU32]
    by_cases hc : x.ult y = true <;> simp [hc, ih]

/-- Inserting before a strictly greater tail word keeps it last
    (the swap-case equation: the insertion point lies inside). -/
theorem insertU32_append_gt (x y : BitVec 32) (ws : List (BitVec 32))
    (h : x.ult y = true) :
    insertU32 x (ws ++ [y]) = insertU32 x ws ++ [y] := by
  induction ws with
  | nil => simp [insertU32, h]
  | cons z zs ih =>
    show insertU32 x (z :: (zs ++ [y])) = insertU32 x (z :: zs) ++ [y]
    simp only [insertU32]
    by_cases hz : x.ult z = true <;> simp [hz, ih]

/-- Inserting above every word snocs (the exit-case equation). -/
theorem insertU32_snoc_ge (x : BitVec 32) (ws : List (BitVec 32))
    (h : ∀ w ∈ ws, ¬ x.ult w = true) :
    insertU32 x ws = ws ++ [x] := by
  induction ws with
  | nil => rfl
  | cons y ys ih =>
    have hy : ¬ x.ult y = true := h y (by simp)
    simp only [insertU32]
    by_cases hc : x.ult y = true
    · exact absurd hc hy
    · simp [hc, ih (fun w hm => h w (by simp [hm]))]

/-- Insert commutes (both orders splice both words in). The
    consistent leaves evaluate by `simp`; the two inconsistent
    leaves (`a<b` with `b<y` but `¬a<y`, and symmetric) close by
    `ult`-transitivity, and the equal-words leaf (`¬a<b`,
    `¬b<a`) by antisymmetry. -/
theorem insertU32_commute (a b : BitVec 32) (l : List (BitVec 32)) :
    insertU32 a (insertU32 b l) = insertU32 b (insertU32 a l) := by
  induction l with
  | nil =>
    simp only [insertU32]
    by_cases hab : a.ult b = true
    · by_cases hba : b.ult a = true
      · have hcon := bv_ult_asymm a b hab
        rw [hcon] at hba
        cases hba
      · simp [hab, hba]
    · by_cases hba : b.ult a = true
      · simp [hab, hba]
      · have heq := bv_eq_of_not_ult_both a b hab hba
        subst heq
        rfl
  | cons y ys ih =>
    by_cases hby : b.ult y = true
    · by_cases hay : a.ult y = true
      · by_cases hab : a.ult b = true
        · have hba' : ¬ (b.ult a = true) := by
            intro hc
            have hf := bv_ult_asymm a b hab
            rw [hf] at hc
            cases hc
          simp [insertU32, hby, hay, hab, hba']
        · by_cases hba : b.ult a = true
          · have hab' : ¬ (a.ult b = true) := by
              intro hc
              have hf := bv_ult_asymm b a hba
              rw [hf] at hc
              cases hc
            simp [insertU32, hby, hay, hab', hba]
          · have heq := bv_eq_of_not_ult_both a b hab hba
            subst heq
            rfl
      · by_cases hab : a.ult b = true
        · have hlt := bv_ult_trans a b y hab hby
          exact absurd hlt hay
        · simp [insertU32, hby, hay, hab]
    · by_cases hay : a.ult y = true
      · by_cases hba : b.ult a = true
        · have hlt := bv_ult_trans b a y hba hay
          exact absurd hlt hby
        · simp [insertU32, hby, hay, hba]
      · simp [insertU32, hby, hay, ih]

/-- Membership in an insertion: the word is the inserted one or
    was already there. -/
theorem insertU32_mem (z x : BitVec 32) (ws : List (BitVec 32))
    (h : x ∈ insertU32 z ws) : x = z ∨ x ∈ ws := by
  induction ws with
  | nil =>
    simp only [insertU32] at h
    simp at h
    exact Or.inl h
  | cons w rest ih =>
    simp only [insertU32] at h
    by_cases hz : z.ult w = true
    · simp only [hz, ite_true, List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
      · exact Or.inr (by simp only [List.mem_cons]; exact Or.inr h)
    · simp [hz, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (by simp [h])
      · have h2 := ih h
        rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (by simp [h2])

/-- Left-fold insertion: `sortL acc l` folds `insertU32` over `l`
    starting from `acc`. `insertionSortList l = sortL [] l`; the
    outer-loop mirror is a `sortL` with `take`-slice accumulators. -/
def sortL (acc : List (BitVec 32)) : List (BitVec 32) → List (BitVec 32)
  | [] => acc
  | x :: xs => sortL (insertU32 x acc) xs

/-- Pushing `x` into the accumulator commutes past the fold. -/
theorem sortL_insert (x : BitVec 32) (acc xs : List (BitVec 32)) :
    sortL (insertU32 x acc) xs = insertU32 x (sortL acc xs) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih =>
    show sortL (insertU32 y (insertU32 x acc)) ys =
      insertU32 x (sortL (insertU32 y acc) ys)
    rw [insertU32_commute y x acc]
    exact ih _

/-- `insertionSortList` is the empty-accumulator fold. -/
theorem sortL_nil (l : List (BitVec 32)) :
    insertionSortList l = sortL [] l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [insertionSortList]
    rw [ih]
    exact (sortL_insert x [] xs).symm

/-- Insert into sorted stays sorted (needs `≤`-transitivity at the
    splice point and asymmetry for the strict head case). -/
theorem pairwise_insertU32_sorted (z : BitVec 32) (ws : List (BitVec 32))
    (h : ws.Pairwise (fun a b => b.ult a = false)) :
    (insertU32 z ws).Pairwise (fun a b => b.ult a = false) := by
  induction ws with
  | nil => exact List.pairwise_singleton _ _
  | cons w rest ih =>
    have h1 := (List.pairwise_cons.mp h).1
    have h2 := (List.pairwise_cons.mp h).2
    by_cases hz : z.ult w = true
    · have hzw : w.ult z = false := bv_ult_asymm z w hz
      simp only [insertU32, hz, ite_true]
      rw [List.pairwise_cons]
      refine ⟨fun x hx => ?_, h⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hzw
      · exact bv_le_trans z w x hzw (h1 x hx)
    · have hzf : z.ult w = false := bool_eq_false_of_not_true hz
      simp [insertU32, hzf]
      refine ⟨fun x hx => ?_, ih h2⟩
      have hx' := insertU32_mem z x rest hx
      rcases hx' with rfl | hxm
      · exact hzf
      · exact h1 x hxm

/-- Every word of a sorted snoc-list ending in `y` is `≤ z` when
    `y ≤ z` (the exit-case precondition, by induction on the snoc). -/
theorem pairwise_snoc_all_le (ws : List (BitVec 32)) (y z : BitVec 32)
    (h : (ws ++ [y]).Pairwise (fun a b => b.ult a = false))
    (hle : z.ult y = false) :
    ∀ w ∈ ws ++ [y], (z.ult w) = false := by
  induction ws with
  | nil =>
    intro w hm
    simp at hm
    subst hm
    exact hle
  | cons a as ih =>
    simp only [List.cons_append] at h
    rw [List.pairwise_cons] at h
    intro w hm
    simp only [List.cons_append, List.mem_cons] at hm
    rcases hm with haw | hm
    · have hay : y.ult a = false := h.1 y (by simp)
      rw [haw]
      exact bv_le_trans a y z hay hle
    · exact ih h.2 w hm

/-- One outer-loop pass in take/drop form: insert the `i`-th word
    into the `take i` prefix, keep the `drop (i+1)` suffix. `z` is
    passed explicitly so the bridge can rewrite it via hit facts. -/
def outerListStep (l : List (BitVec 32)) (i : Nat) (z : BitVec 32) :
    List (BitVec 32) :=
  insertU32 z (l.take i) ++ l.drop (i + 1)

/-- Outer-loop mirror: `fuel` passes starting from index `i` over a
    length-`N` list (the N9 `4` case runs passes `i = 1, 2, 3`). The
    `getD 0` default never fires (every index hits); the bridge
    discharges each read with a hit fact. -/
def outerListAux (N : Nat) (l : List (BitVec 32)) (i fuel : Nat) :
    List (BitVec 32) :=
  match fuel with
  | 0 => l
  | f + 1 =>
    if i < N then outerListAux N (outerListStep l i (l[i]?.getD 0)) (i + 1) f
    else l

/-- Base case (definitional, named for rewriting). -/
theorem outerListAux_zero (N : Nat) (l : List (BitVec 32)) (i : Nat) :
    outerListAux N l i 0 = l := rfl

/-- Step case (definitional, named for rewriting). -/
theorem outerListAux_succ (N : Nat) (l : List (BitVec 32)) (i f : Nat) :
    outerListAux N l i (f + 1) =
      if i < N then outerListAux N (outerListStep l i (l[i]?.getD 0)) (i + 1) f
      else l := rfl

/-- Decrementing a positive small index word (for the `j - 1`
    reads and the `j` countdown; exact by `u64sub_toNat_exact`). -/
theorem ofNat64_sub_one_toNat (j : Nat) (hj : 1 ≤ j) (hj64 : j < 2 ^ 64) :
    (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat = j - 1 := by
  have h := u64sub_toNat_exact (BitVec.ofNat 64 j) (BitVec.ofNat 64 1)
    (by rw [ofNat64_toNat j hj64, ofNat64_toNat 1 (by decide)]; omega)
  rw [h, ofNat64_toNat j hj64, ofNat64_toNat 1 (by decide)]

/-- Decrement stays in `ofNat` form (for the `j` post-env). -/
theorem ofNat64_sub_one (j : Nat) (hj : 1 ≤ j) (hj64 : j < 2 ^ 64) :
    BitVec.ofNat 64 j - BitVec.ofNat 64 1 = BitVec.ofNat 64 (j - 1) := by
  apply BitVec.toNat_inj.mp
  rw [ofNat64_sub_one_toNat j hj hj64, ofNat64_toNat (j - 1) (by omega)]

/-- A pairwise list stays pairwise under `take` (for narrowing the
    outer sorted prefix to the inner-loop window). -/
theorem pairwise_take {α : Type} (R : α → α → Prop) (l : List α) (k : Nat)
    (h : l.Pairwise R) : (l.take k).Pairwise R := by
  induction l generalizing k with
  | nil => simp
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, List.pairwise_cons]
      rw [List.pairwise_cons] at h
      exact ⟨fun x hx => h.1 x (List.mem_of_mem_take hx), ih k h.2⟩

/-! ## N9-iii: CoreIR mirrors (transcribed once from `insertionSortFunc`) -/

/-- The inner-loop swap body: temp + two `arrSet`s + countdown. -/
def sortSwapBody : CStmt :=
  .seq (.let_ "t" (.u 32) (.idxu "a" (.var "j")))
    (.seq (.arrSet "a" (.var "j")
      (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
    (.seq (.arrSet "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
        (.var "t"))
      (.assign "j" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))))

/-- The inner-loop condition: `j > 0` short-circuits (via `tif`, so
    `j - 1` never evaluates at `j = 0`) before `a[j] < a[j-1]`. -/
def sortInnerCond : CExpr :=
  .tif (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j"))
    (.ult (.idxu "a" (.var "j"))
      (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
    (.lit (.b false))

/-- The inner `while` (one outer pass's worth of bubbling). -/
def sortInnerWhile : CStmt := .while_ sortInnerCond sortSwapBody

/-- The outer-loop condition `i < N`. -/
def sortOuterCond (N : Nat) : CExpr :=
  .ult (.var "i") (.lit (.u64 (BitVec.ofNat 64 N)))

/-- One outer pass: rebind `j` at `i`, bubble, step `i`. -/
def sortOuterBody : CStmt :=
  .seq (.let_ "j" (.u 64) (.var "i"))
  (.seq sortInnerWhile
    (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- The outer `while` (`N - 1` passes from `i = 1`). -/
def sortOuterWhile (N : Nat) : CStmt := .while_ (sortOuterCond N) sortOuterBody

/-- `insertionSortFunc.body` is `i := 1`, the outer loop, `return a`. -/
theorem insertionSortFunc_body (N : Nat) : (insertionSortFunc N).body =
    .seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
    (.seq (sortOuterWhile N) (.return_ (.var "a"))) := rfl

/-- The inner condition at `j = 0`: the `j > 0` guard is false,
    so `tif` takes the else-branch without touching the array. -/
theorem sortInnerCond_eval_zero (ρ : Env) (l : List (BitVec 32)) (j : Nat)
    (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
    (hj0 : j = 0) :
    evalExpr sortInnerCond ρ = .ok (.b false) := by
  have e_c : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
      .ok (.b ((BitVec.ofNat 64 0).ult (BitVec.ofNat 64 j))) :=
    evalExpr_ult_u64lit _ _ _ _ (evalExpr_var_hit _ _ _ hj)
  rw [hj0, bv_ult_irrefl] at e_c
  simp only [sortInnerCond]
  rw [evalExpr_tif_false _ _ _ _ e_c]
  exact evalExpr_lit _ _

/-- The inner condition at `j ≥ 1`: the guard holds, so `tif` runs
    the `a[j] < a[j-1]` comparison (both reads hit). -/
theorem sortInnerCond_eval_succ (N : Nat) (ρ : Env) (l : List (BitVec 32)) (j : Nat)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
    (hlen : l.length = N) (hN64 : N < 2 ^ 64) (hjN : j + 1 ≤ N)
    (hj1 : 1 ≤ j) :
    evalExpr sortInnerCond ρ = .ok (.b (l[j].ult l[j - 1])) := by
  have hj64 : j < 2 ^ 64 := by omega
  have htoNat_j : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat j hj64
  have hsub_toNat := ofNat64_sub_one_toNat j hj1 hj64
  have hj_get : l[j]? = some l[j] := List.getElem?_eq_getElem (by omega)
  have hjm_get : l[j - 1]? = some l[j - 1] :=
    List.getElem?_eq_getElem (by omega)
  have e_c : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
      .ok (.b true) := by
    have h := evalExpr_ult_u64lit (BitVec.ofNat 64 0) (BitVec.ofNat 64 j)
      (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
    have htrue : (BitVec.ofNat 64 0).ult (BitVec.ofNat 64 j) = true := by
      rw [ofNat64_ult 0 _ (by decide : (0 : Nat) < 2 ^ 64),
        ofNat64_toNat j hj64]
      exact decide_eq_true (by omega : 0 < j)
    rw [htrue] at h
    exact h
  have e1 : evalExpr (.idxu "a" (.var "j")) ρ = .ok (.u32 l[j]) := by
    simp only [evalExpr, hj, ha, htoNat_j, hj_get]
  have e2 : evalExpr
      (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
      .ok (.u32 l[j - 1]) := by
    simp only [evalExpr, litVal, hj, ha, hsub_toNat, hjm_get]
  simp only [sortInnerCond]
  rw [evalExpr_tif_true _ _ _ _ e_c]
  simp only [evalExpr, litVal, hj, ha, htoNat_j, hsub_toNat, hj_get, hjm_get]

/-- Inserting below every word conses (for the bubble-down base
    case: the bubbled word precedes the greater suffix). -/
theorem insertU32_all_gt (z : BitVec 32) (l : List (BitVec 32))
    (h : ∀ w ∈ l, z.ult w = true) :
    insertU32 z l = z :: l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have hy : z.ult y = true := h y (by simp)
    simp only [insertU32, hy, ite_true]

/-- Inserting before a list of strictly greater words keeps the list
    last (for splicing the bubbled word before the shifted slice). -/
theorem insertU32_append_all_gt (z : BitVec 32) (A B : List (BitVec 32))
    (h : ∀ b ∈ B, z.ult b = true) :
    insertU32 z (A ++ B) = insertU32 z A ++ B := by
  induction B generalizing A with
  | nil => simp
  | cons b bs ih =>
    have hb : z.ult b = true := h b (by simp)
    have hbs : ∀ w ∈ bs, z.ult w = true := fun w hm => h w (by simp [hm])
    have e : A ++ (b :: bs) = (A ++ [b]) ++ bs := by
      simp [List.append_assoc]
    rw [e, ih (A ++ [b]) hbs, insertU32_append_gt z b A hb]
    exact List.append_assoc _ _ _

/-- Pure bubble-down mirror of the inner loop: compare `l[j]` below
    `l[j-1]`, swap and descend on strict `<`, else stop (OOB stops
    too — the loop proof only feeds hitting indices). -/
def bubbleDown (l : List (BitVec 32)) : Nat → List (BitVec 32)
  | 0 => l
  | j + 1 =>
    match l[j + 1]?, l[j]? with
    | some zj, some xj =>
      if zj.ult xj then bubbleDown ((l.set (j + 1) xj).set j zj) j else l
    | _, _ => l

/-- Bubble-down equals one outer pass. The slice invariant: `z`
    sits at `j`, the prefix is the entry prefix, the suffix is the
    entry slice shifted up by one plus the untouched tail, the entry
    prefix is sorted, and everything already below exceeds `z`
    (the swap history). At `j = 0` the word conses before the
    greater suffix (`insertU32_all_gt`); at a false guard the
    sorted prefix absorbs it (`insertU32_snoc_ge`); on swap the
    slice shifts down by one. -/
theorem bubbleDown_eq_outerListStep (N : Nat) (l₀ : List (BitVec 32)) (i : Nat)
    (l : List (BitVec 32)) (j : Nat) (z : BitVec 32)
    (hlen₀ : l₀.length = N) (hiN : i + 1 ≤ N)
    (hsorted : (l₀.take i).Pairwise (fun a b => b.ult a = false))
    (hlen : l.length = N) (hji : j ≤ i)
    (hz : l[j]? = some z)
    (htake : l.take j = l₀.take j)
    (hslice : l.drop (j + 1) = (l₀.take i).drop j ++ l₀.drop (i + 1))
    (hmid : ∀ w ∈ (l₀.take i).drop j, z.ult w = true) :
    bubbleDown l j = insertU32 z (l₀.take i) ++ l₀.drop (i + 1) := by
  -- Explicit `Nat.rec` motive (instead of `induction ... with`,
  -- whose auto-introduction misnames the reverted hypotheses).
  refine Nat.rec
    (motive := fun j => ∀ (l : List (BitVec 32)) (hlen : l.length = N)
      (hji : j ≤ i) (hz : l[j]? = some z)
      (htake : l.take j = l₀.take j)
      (hslice : l.drop (j + 1) = (l₀.take i).drop j ++ l₀.drop (i + 1))
      (hmid : ∀ w ∈ (l₀.take i).drop j, z.ult w = true),
      bubbleDown l j = insertU32 z (l₀.take i) ++ l₀.drop (i + 1))
    ?_ ?_ j l hlen hji hz htake hslice hmid
  · intro l hlen hji hz htake hslice hmid
    have hmid0 : ∀ w ∈ l₀.take i, z.ult w = true := by
      simpa [drop_zero'] using hmid
    have hins : insertU32 z (l₀.take i) = z :: l₀.take i :=
      insertU32_all_gt z _ hmid0
    have hslice0 : l.drop (0 + 1) = (l₀.take i).drop 0 ++ l₀.drop (i + 1) :=
      hslice
    have hl : l = z :: ((l₀.take i) ++ l₀.drop (i + 1)) := by
      have hs := split_of_getElem? l 0 z hz
      rw [hslice0] at hs
      simpa [take_zero'] using hs
    simp only [bubbleDown, hl, hins, List.cons_append]
  · -- Clear the theorem parameters first: `intro` freshens (rather
    -- than shadows) colliding names, which misnamed every binder.
    clear l j hlen hji hz htake hslice hmid
    intro j ih l hlen hji hz htake hslice hmid
    have hj_lt : j + 1 < l.length := by omega
    have hget : l[j]? = some l[j] := List.getElem?_eq_getElem (by omega)
    have hunfold : bubbleDown l (j + 1) =
        if z.ult l[j] then bubbleDown ((l.set (j + 1) l[j]).set j z) j
        else l := by
      simp only [bubbleDown, hz, hget]
    -- The current word below equals the entry word (prefix untouched).
    -- Option injectivity over free variables (`cases` on `getElem`
    -- terms fails: the index proofs differ).
    have hx_eq : l[j] = l₀[j] := by
      have hinj : ∀ (a b : BitVec 32), (some a = some b) → a = b := by
        intro a b h
        cases h
        rfl
      have g1 : (l.take (j + 1))[j]? = some l[j] := by
        rw [List.getElem?_take, if_pos (by omega : j < j + 1)]
        exact List.getElem?_eq_getElem (by omega)
      have g2 : (l₀.take (j + 1))[j]? = some l₀[j] := by
        rw [List.getElem?_take, if_pos (by omega : j < j + 1)]
        exact List.getElem?_eq_getElem (by omega)
      rw [htake] at g1
      rw [g2] at g1
      exact (hinj _ _ g1).symm
    -- The slice head is the entry word at `j`.
    have hdrop : (l₀.take i).drop j = l₀[j] :: (l₀.take i).drop (j + 1) := by
      have hg : (l₀.take i)[j]? = some l₀[j] := by
        rw [List.getElem?_take, if_pos (by omega : j < i)]
        exact List.getElem?_eq_getElem (by omega)
      exact drop_of_getElem? _ _ _ hg
    by_cases hc : z.ult l[j] = true
    · rw [hunfold, if_pos hc]
      -- NOTE: `hpost` rewrites the goal below (set-form to
      -- take/drop-form) so the IH applies on the nose.
      have hpost : ((l.set (j + 1) l[j]).set j z) =
          l.take j ++ [z, l[j]] ++ l.drop (j + 2) :=
        set_take_drop l j l[j] z (by omega)
      have hAlen : (l.take j).length = j := take_length_eq _ _ (by omega)
      have hz' : ((l.take j ++ [z, l[j]] ++ l.drop (j + 2)))[j]? =
          some z := by
        have e := getElem?_append_add (l.take j)
          ([z, l[j]] ++ l.drop (j + 2)) 0
        rw [hAlen, show j + 0 = j from by omega] at e
        rw [List.append_assoc, e]
        rfl
      have hA : l.take j = l₀.take j := by
        have e1 : (l.take (j + 1)).take j = l.take j := by
          rw [List.take_take, show min j (j + 1) = j from by omega]
        have e2 : (l₀.take (j + 1)).take j = l₀.take j := by
          rw [List.take_take, show min j (j + 1) = j from by omega]
        rw [htake] at e1
        rw [e2] at e1
        exact e1.symm
      have htake' : ((l.take j ++ [z, l[j]] ++ l.drop (j + 2))).take j =
          l₀.take j := by
        have e := take_append_self (l.take j) ([z, l[j]] ++ l.drop (j + 2))
        rw [hAlen] at e
        rw [List.append_assoc, e]
        exact hA
      have hslice' :
          ((l.take j ++ [z, l[j]] ++ l.drop (j + 2))).drop (j + 1) =
          (l₀.take i).drop j ++ l₀.drop (i + 1) := by
        have d2 : (l.take j).length ≤ j + 1 := by omega
        have d1 : j + 1 - (l.take j).length = 1 := by omega
        have dr : (([z, l[j]] ++ l.drop (j + 2)).drop 1) =
            [l[j]] ++ l.drop (j + 2) := rfl
        have eD : j + 2 = (j + 1) + 1 := by omega
        rw [List.append_assoc, List.drop_append,
          List.drop_eq_nil_of_le d2, d1, dr, eD, hslice, hdrop, ← hx_eq]
        rfl
      have hmid' : ∀ w ∈ (l₀.take i).drop j, z.ult w = true := by
        intro w hm
        rw [hdrop] at hm
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · rw [← hx_eq]
          exact hc
        · exact hmid w hm
      have hlen' : (l.take j ++ [z, l[j]] ++ l.drop (j + 2)).length = N := by
        have hmin : min j l.length = j := by omega
        have h2 : [z, l[j]].length = 2 := rfl
        rw [List.length_append, List.length_append, List.length_take, hmin,
          h2, List.length_drop, hlen]
        omega
      have hji' : j ≤ i := by omega
      rw [hpost]
      exact ih _ hlen' hji' hz' htake' hslice' hmid'
    · -- Exit with `¬ z < l[j]`: the sorted prefix absorbs `z`
      -- (`insertU32_snoc_ge`), the slice stays last
      -- (`insertU32_append_all_gt`).
      have hle : z.ult l₀[j] = false := by
        rw [← hx_eq]
        exact bool_eq_false_of_not_true hc
      have hj0hit : l₀[j]? = some l₀[j] :=
        List.getElem?_eq_getElem (by omega)
      have hsplit : l₀.take (j + 1) = l₀.take j ++ [l₀[j]] :=
        take_succ_of_getElem? _ _ _ hj0hit
      have h2 : (l₀.take (j + 1)).Pairwise (fun a b => b.ult a = false) := by
        have e : l₀.take (j + 1) = (l₀.take i).take (j + 1) := by
          rw [List.take_take, show min (j + 1) i = j + 1 from by omega]
        rw [e]
        exact pairwise_take _ _ _ hsorted
      have hle_all : ∀ w ∈ l₀.take j ++ [l₀[j]], z.ult w = false := by
        have hp : (l₀.take j ++ [l₀[j]]).Pairwise
            (fun a b => b.ult a = false) := by
          rw [← hsplit]
          exact h2
        exact pairwise_snoc_all_le _ _ _ hp hle
      have hne_all : ∀ w ∈ l₀.take j ++ [l₀[j]], ¬ z.ult w = true := by
        intro w hm
        have h := hle_all w hm
        intro hc2
        rw [h] at hc2
        cases hc2
      have hins : insertU32 z (l₀.take (j + 1)) =
          l₀.take (j + 1) ++ [z] := by
        rw [hsplit]
        exact insertU32_snoc_ge z _ hne_all
      have hsplitI : l₀.take i =
          l₀.take (j + 1) ++ (l₀.take i).drop (j + 1) := by
        have h := List.take_append_drop (j + 1) (l₀.take i)
        rw [List.take_take, show min (j + 1) i = j + 1 from by omega] at h
        exact h.symm
      have hinsI : insertU32 z (l₀.take i) =
          (l₀.take (j + 1) ++ [z]) ++ (l₀.take i).drop (j + 1) := by
        -- `congrArg`: plain `rw [hsplitI]` would also rewrite the
        -- `take i l₀` inside the RHS slice.
        have h1 : insertU32 z (l₀.take i) =
            insertU32 z (l₀.take (j + 1) ++ (l₀.take i).drop (j + 1)) :=
          congrArg _ hsplitI
        rw [h1, insertU32_append_all_gt z _ _ hmid, hins]
      have hl : l = l₀.take (j + 1) ++ z ::
          ((l₀.take i).drop (j + 1) ++ l₀.drop (i + 1)) := by
        have hs := split_of_getElem? l (j + 1) z hz
        rw [hslice, htake] at hs
        exact hs
      rw [hunfold, if_neg hc, hl, hinsI]
      -- Reassociate, fold `[z] ++ _` to `z :: _`, drop `[] ++ _`.
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- One swap-body pass: `t := a[j]; a[j] := a[j-1]; a[j-1] := t;
    j := j - 1` (any fuel — the body is loop-free, so `cases F`
    + `simp` handles both fuels uniformly, the `stdVecBody_step_ok`
    shape). The post-array is the `set_take_drop` splice; `i` is
    untouched. -/
theorem sortSwapBody_step (N : Nat) (F : Nat) (ρ : Env) (l : List (BitVec 32))
    (j : Nat)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
    (hlen : l.length = N) (hN64 : N < 2 ^ 64) (hjN : j + 1 ≤ N)
    (hj1 : 1 ≤ j) :
    ∃ ρ₄, evalStmtFuel F sortSwapBody ρ = .ok (ρ₄, .fellThrough) ∧
      envLookup ρ₄ "a" =
        some (.arr32 (l.take (j - 1) ++ [l[j], l[j - 1]] ++ l.drop (j + 1))) ∧
      envLookup ρ₄ "j" = some (.u64 (BitVec.ofNat 64 (j - 1))) ∧
      envLookup ρ₄ "i" = envLookup ρ "i" := by
  have hj64 : j < 2 ^ 64 := by omega
  have hj_get : l[j]? = some l[j] := List.getElem?_eq_getElem (by omega)
  have hjm_get : l[j - 1]? = some l[j - 1] :=
    List.getElem?_eq_getElem (by omega)
  have hsub_toNat := ofNat64_sub_one_toNat j hj1 hj64
  have hsub_eq := ofNat64_sub_one j hj1 hj64
  have htoNat_j : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat j hj64
  have e_j : evalExpr (.var "j") ρ = .ok (.u64 (BitVec.ofNat 64 j)) :=
    evalExpr_var_hit ρ "j" _ hj
  have e_sub : evalExpr (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) :=
    evalExpr_u64_usub _ _ _ _ e_j
  have e_readj : evalExpr (.idxu "a" (.var "j")) ρ = .ok (.u32 l[j]) := by
    simp only [evalExpr, hj, ha, htoNat_j, hj_get]
  have hget_jm : l[(BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat]? =
      some l[j - 1] := by
    rw [hsub_toNat]
    exact hjm_get
  have e_readjm : evalExpr
      (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
      .ok (.u32 l[j - 1]) := by
    simp only [evalExpr, litVal, hj, ha, hsub_toNat, hjm_get]
  -- The `t` binding and its lookup consequences.
  have ha₁ : envLookup (envExtend ρ "t" (.u32 l[j])) "a" =
      some (.arr32 l) := by
    simp [envExtend, envLookup, ha, show ("a" : String) ≠ "t" by decide]
  have hj₁ : envLookup (envExtend ρ "t" (.u32 l[j])) "j" =
      some (.u64 (BitVec.ofNat 64 j)) := by
    simp [envExtend, envLookup, hj, show ("j" : String) ≠ "t" by decide]
  have hi₁ : envLookup (envExtend ρ "t" (.u32 l[j])) "i" =
      envLookup ρ "i" := by
    simp [envExtend, envLookup, show ("i" : String) ≠ "t" by decide]
  have ht₁ : envLookup (envExtend ρ "t" (.u32 l[j])) "t" =
      some (.u32 l[j]) := by
    simp [envExtend, envLookup]
  have e_j₁ : evalExpr (.var "j") (envExtend ρ "t" (.u32 l[j])) =
      .ok (.u64 (BitVec.ofNat 64 j)) :=
    evalExpr_var_hit _ _ _ hj₁
  have e_sub₁ : evalExpr (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
      (envExtend ρ "t" (.u32 l[j])) =
      .ok (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) :=
    evalExpr_u64_usub _ _ _ _ e_j₁
  have e_readjm₁ : evalExpr
      (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))
      (envExtend ρ "t" (.u32 l[j])) = .ok (.u32 l[j - 1]) := by
    simp only [evalExpr, litVal, hj₁, ha₁, hsub_toNat, hjm_get]
  -- First `arrSet`: write `l[j-1]` at `j`.
  have hset1_get : l[(BitVec.ofNat 64 j).toNat]? = some l[j] := by
    rw [htoNat_j]
    exact hj_get
  obtain ⟨ρ₂, hu₁⟩ := envUpdate_some_of_lookup
    (envExtend ρ "t" (.u32 l[j])) "a" (.arr32 l)
    (.arr32 (l.set (BitVec.ofNat 64 j).toNat l[j - 1])) ha₁
  have ha₂ : envLookup ρ₂ "a" =
      some (.arr32 (l.set (BitVec.ofNat 64 j).toNat l[j - 1])) :=
    envLookup_envUpdate_same _ _ _ _ hu₁
  have hj₂ : envLookup ρ₂ "j" = some (.u64 (BitVec.ofNat 64 j)) := by
    have h := envLookup_envUpdate_diff (envExtend ρ "t" (.u32 l[j])) "a" "j"
      _ _ hu₁ (by decide)
    rw [hj₁] at h
    exact h
  have ht₂ : envLookup ρ₂ "t" = some (.u32 l[j]) := by
    have h := envLookup_envUpdate_diff (envExtend ρ "t" (.u32 l[j])) "a" "t"
      _ _ hu₁ (by decide)
    rw [ht₁] at h
    exact h
  have hi₂ : envLookup ρ₂ "i" = envLookup ρ "i" := by
    have h := envLookup_envUpdate_diff (envExtend ρ "t" (.u32 l[j])) "a" "i"
      _ _ hu₁ (by decide)
    rw [hi₁] at h
    exact h
  have e_j₂ : evalExpr (.var "j") ρ₂ = .ok (.u64 (BitVec.ofNat 64 j)) :=
    evalExpr_var_hit _ _ _ hj₂
  have e_sub₂ : evalExpr (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
      ρ₂ = .ok (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) :=
    evalExpr_u64_usub _ _ _ _ e_j₂
  have e_t₂ : evalExpr (.var "t") ρ₂ = .ok (.u32 l[j]) :=
    evalExpr_var_hit _ _ _ ht₂
  -- Second `arrSet`: write `t` at `j - 1` (the set-index differs
  -- from the first, so the earlier word is still there).
  have hset2_get : (l.set (BitVec.ofNat 64 j).toNat l[j - 1])[
      (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat]? =
      some l[j - 1] := by
    rw [hsub_toNat, htoNat_j, List.getElem?_set_ne (by omega : j ≠ j - 1)]
    exact hjm_get
  obtain ⟨ρ₃, hu₂⟩ := envUpdate_some_of_lookup ρ₂ "a"
    (.arr32 (l.set (BitVec.ofNat 64 j).toNat l[j - 1]))
    (.arr32 ((l.set (BitVec.ofNat 64 j).toNat l[j - 1]).set
      (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat l[j])) ha₂
  have ha₃ : envLookup ρ₃ "a" = some (.arr32
      ((l.set (BitVec.ofNat 64 j).toNat l[j - 1]).set
        (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat l[j])) :=
    envLookup_envUpdate_same _ _ _ _ hu₂
  have hj₃' : envLookup ρ₃ "j" = some (.u64 (BitVec.ofNat 64 j)) := by
    have h := envLookup_envUpdate_diff ρ₂ "a" "j" _ _ hu₂ (by decide)
    rw [hj₂] at h
    exact h
  have hi₃ : envLookup ρ₃ "i" = envLookup ρ "i" := by
    have h := envLookup_envUpdate_diff ρ₂ "a" "i" _ _ hu₂ (by decide)
    rw [hi₂] at h
    exact h
  have e_sub₃ : evalExpr (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
      ρ₃ = .ok (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) :=
    evalExpr_u64_usub _ _ _ _ (evalExpr_var_hit _ _ _ hj₃')
  -- The countdown `j := j - 1`.
  obtain ⟨ρ₄, hu₃⟩ := envUpdate_some_of_lookup ρ₃ "j"
    (.u64 (BitVec.ofNat 64 j))
    (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) hj₃'
  have ha₄ : envLookup ρ₄ "a" = some (.arr32
      ((l.set (BitVec.ofNat 64 j).toNat l[j - 1]).set
        (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat l[j])) := by
    have h := envLookup_envUpdate_diff ρ₃ "j" "a" _ _ hu₃ (by decide)
    rw [ha₃] at h
    exact h
  have hj₄ : envLookup ρ₄ "j" = some (.u64 (BitVec.ofNat 64 (j - 1))) := by
    rw [← hsub_eq]
    exact envLookup_envUpdate_same _ _ _ _ hu₃
  have hi₄ : envLookup ρ₄ "i" = envLookup ρ "i" := by
    have h := envLookup_envUpdate_diff ρ₃ "j" "i" _ _ hu₃ (by decide)
    rw [hi₃] at h
    exact h
  -- The spliced array is the take/drop step.
  have harr : (l.set (BitVec.ofNat 64 j).toNat l[j - 1]).set
        (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat l[j] =
        l.take (j - 1) ++ [l[j], l[j - 1]] ++ l.drop (j + 1) := by
    rw [htoNat_j, hsub_toNat]
    have h := set_take_drop l (j - 1) l[j - 1] l[j] (by omega)
    rw [show (j - 1) + 1 = j from by omega] at h
    rw [show (j - 1) + 2 = j + 1 from by omega] at h
    exact h
  -- Chain the four steps (each at any fuel, so the whole body is
  -- fuel-polymorphic; no big-`simp`, which would normalize `.toNat`
  -- under the rewrite rules via simprocs).
  have s1 : ∀ f, evalStmtFuel f (.let_ "t" (.u 32) (.idxu "a" (.var "j")))
      ρ = .ok (envExtend ρ "t" (.u32 l[j]), .fellThrough) :=
    fun f => evalStmtFuel_let_ f _ _ _ _ _ e_readj
  have s2 : ∀ f, evalStmtFuel f
      (.arrSet "a" (.var "j")
        (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
      (envExtend ρ "t" (.u32 l[j])) = .ok (ρ₂, .fellThrough) :=
    fun f => evalStmtFuel_arrSet f _ _ _ _ _ _ _ _ _ e_j₁ e_readjm₁ ha₁
      hset1_get hu₁
  have s3 : ∀ f, evalStmtFuel f
      (.arrSet "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
        (.var "t"))
      ρ₂ = .ok (ρ₃, .fellThrough) :=
    fun f => evalStmtFuel_arrSet f _ _ _ _ _ _ _ _ _ e_sub₂ e_t₂ ha₂
      hset2_get hu₂
  have s4 : ∀ f, evalStmtFuel f
      (.assign "j" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))) ρ₃ =
      .ok (ρ₄, .fellThrough) :=
    fun f => evalStmtFuel_assign f _ _ _ _ _ e_sub₃ hu₃
  refine ⟨ρ₄, ?_, ?_, ?_, ?_⟩
  · simp only [sortSwapBody]
    rw [evalStmtFuel_seq_fallthrough F _ _ _ _ (s1 F),
      evalStmtFuel_seq_fallthrough F _ _ _ _ (s2 F),
      evalStmtFuel_seq_fallthrough F _ _ _ _ (s3 F)]
    exact s4 F
  · rw [harr] at ha₄
    exact ha₄
  · exact hj₄
  · exact hi₄

/-- Inner-loop correctness: the loop mirrors `bubbleDown` (fuel
    covers the `j + 1` live indices; `i` is untouched). The
    `take`-prefix and hit facts thread the condition evaluation
    and the swap-body applicability. -/
theorem sortInnerWhile_correct (N : Nat) (F : Nat) (ρ : Env)
    (l₀ : List (BitVec 32))
    (l : List (BitVec 32)) (j : Nat) (z : BitVec 32)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
    (hlen : l.length = N) (hN64 : N < 2 ^ 64) (hjN : j + 1 ≤ N)
    (hz : l[j]? = some z)
    (htake : l.take j = l₀.take j)
    (hF : j + 1 ≤ F) :
    ∃ ρ', evalStmtFuel F sortInnerWhile ρ = .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.arr32 (bubbleDown l j)) ∧
      envLookup ρ' "i" = envLookup ρ "i" := by
  refine Nat.rec
    (motive := fun F => ∀ (ρ : Env) (l : List (BitVec 32)) (j : Nat)
      (ha : envLookup ρ "a" = some (.arr32 l))
      (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
      (hlen : l.length = N) (hN64 : N < 2 ^ 64) (hjN : j + 1 ≤ N)
      (hz : l[j]? = some z) (htake : l.take j = l₀.take j)
      (hF : j + 1 ≤ F),
      ∃ ρ', evalStmtFuel F sortInnerWhile ρ = .ok (ρ', .fellThrough) ∧
        envLookup ρ' "a" = some (.arr32 (bubbleDown l j)) ∧
        envLookup ρ' "i" = envLookup ρ "i")
    ?_ ?_ F ρ l j ha hj hlen hN64 hjN hz htake hF
  · clear F ρ l j ha hj hlen hN64 hjN hz htake hF
    intro ρ l j ha hj hlen hN64 hjN hz htake hF
    have h0 : j + 1 ≤ 0 := hF
    exact (Nat.not_succ_le_zero j h0).elim
  · clear F ρ l j ha hj hlen hN64 hjN hz htake hF
    intro F ih ρ l j ha hj hlen hN64 hjN hz htake hF
    -- Structural split on the index (no manual predecessor lemma,
    -- keeping the `n5-no-manual-fuel-split` gate green).
    cases j with
    | zero =>
      have hcond := sortInnerCond_eval_zero ρ l 0 hj rfl
      have hexit : evalStmtFuel (F + 1) sortInnerWhile ρ =
          .ok (ρ, .fellThrough) := by
        simp [sortInnerWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond]
      rw [hexit]
      refine ⟨ρ, rfl, ?_, rfl⟩
      · -- `bubbleDown` at zero is definitionally `l`, however `0`
        -- elaborates after the split.
        show envLookup ρ "a" = some (.arr32 l)
        exact ha
    | succ k =>
      have hj1 : 1 ≤ k + 1 := by omega
      have hcond := sortInnerCond_eval_succ N ρ l (k + 1) ha hj hlen hN64
        (by omega) hj1
      by_cases hc : l[k + 1].ult l[(k + 1) - 1] = true
      · -- Swap iteration: body, then the IH below (`k` is ambient
        -- from the structural split).
        rw [hc] at hcond
        obtain ⟨ρ₄, hbody, ha₄, hj₄, hi₄⟩ :=
          sortSwapBody_step N F ρ l (k + 1) ha hj hlen hN64 (by omega)
            (by omega)
        -- `(k+1)-1 ≡ k`, `(k+1)+1 ≡ k+2` definitionally: ascribe the
        -- post-state in `k`-form (rewriting indices inside `getElem`
        -- would disturb its proof argument).
        have ha₄k : envLookup ρ₄ "a" = some (.arr32
          (l.take k ++ [l[k + 1], l[k]] ++ l.drop (k + 2))) := ha₄
        have hj₄k : envLookup ρ₄ "j" =
          some (.u64 (BitVec.ofNat 64 k)) := hj₄
        have hstep : evalStmtFuel (F + 1) sortInnerWhile ρ =
            evalStmtFuel F sortInnerWhile ρ₄ := by
          simp [sortInnerWhile, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hbody]
        rw [hstep]
        have hAlen : (l.take k).length = k := take_length_eq _ _ (by omega)
        have hzj : l[k + 1] = z := by
          have hinj : ∀ (a b : BitVec 32), (some a = some b) → a = b := by
            intro a b h
            cases h
            rfl
          have g := List.getElem?_eq_getElem (show k + 1 < l.length from by omega)
          rw [hz] at g
          exact (hinj _ _ g).symm
        -- Value-form post-state: the swapped head is the tracked `z`.
        have ha₄z : envLookup ρ₄ "a" = some (.arr32
          (l.take k ++ [z, l[k]] ++ l.drop (k + 2))) := by
          have g := ha₄k
          rw [hzj] at g
          exact g
        have hz' : ((l.take k ++ [z, l[k]] ++ l.drop (k + 2)))[k]? =
            some z := by
          have e := getElem?_append_add (l.take k)
            ([z, l[k]] ++ l.drop (k + 2)) 0
          rw [hAlen, show k + 0 = k from by omega] at e
          rw [List.append_assoc, e]
          have hB0 : (([z, l[k]] ++ l.drop (k + 2))[0]?) = some z := rfl
          rw [hB0]
        have htake' :
            ((l.take k ++ [z, l[k]] ++ l.drop (k + 2))).take k =
            l₀.take k := by
          have e := take_append_self (l.take k) ([z, l[k]] ++ l.drop (k + 2))
          rw [hAlen] at e
          rw [List.append_assoc, e]
          have hA : l.take k = l₀.take k := by
            have e1 : (l.take (k + 1)).take k = l.take k := by
              rw [List.take_take, show min k (k + 1) = k from by omega]
            have e2 : (l₀.take (k + 1)).take k = l₀.take k := by
              rw [List.take_take, show min k (k + 1) = k from by omega]
            rw [htake] at e1
            rw [e2] at e1
            exact e1.symm
          exact hA
        have hlen' : (l.take k ++ [z, l[k]] ++ l.drop (k + 2)).length = N := by
          have hmin : min k l.length = k := by omega
          have h2 : [z, l[k]].length = 2 := rfl
          rw [List.length_append, List.length_append, List.length_take, hmin,
            h2, List.length_drop, hlen]
          omega
        have hF' : k + 1 ≤ F := by omega
        have hjN' : k + 1 ≤ N := by omega
        obtain ⟨ρ', hloop, ha', hi'⟩ :=
          ih ρ₄ _ k ha₄z hj₄k hlen' hN64 hjN' hz' htake' hF'
        -- The loop head equals the pure unfold.
        have hbub : bubbleDown l (k + 1) = bubbleDown
            (l.take k ++ [z, l[k]] ++ l.drop (k + 2)) k := by
          have hgetk : l[k]? = some l[k] :=
            List.getElem?_eq_getElem (by omega)
          simp only [bubbleDown, hz, hgetk]
          -- `(k+1)-1` is definitionally `k`, so `hc` ascribes directly
          -- (rewriting the index would disturb the `getElem` proof).
          have hck : l[k + 1].ult l[k] = true := hc
          have hc' : z.ult l[k] = true := by
            rw [hzj] at hck
            exact hck
          rw [if_pos hc']
          rw [set_take_drop l k l[k] z (by omega)]
        refine ⟨ρ', hloop, ?_, ?_⟩
        · rw [hbub]
          exact ha'
        · rw [hi']
          exact hi₄
      · -- Exit with `¬ z < l[j-1]`: the array is already bubbled.
        have hc' : l[k + 1].ult l[(k + 1) - 1] = false :=
          bool_eq_false_of_not_true hc
        rw [hc'] at hcond
        have hexit : evalStmtFuel (F + 1) sortInnerWhile ρ =
            .ok (ρ, .fellThrough) := by
          simp [sortInnerWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond]
        rw [hexit]
        have hbub : bubbleDown l (k + 1) = l := by
          have hgetk : l[k]? = some l[k] :=
            List.getElem?_eq_getElem (by omega)
          simp only [bubbleDown, hz, hgetk]
          have hzj : l[k + 1] = z := by
            have hinj : ∀ (a b : BitVec 32), (some a = some b) → a = b := by
              intro a b h
              cases h
              rfl
            have g := List.getElem?_eq_getElem
              (show k + 1 < l.length from by omega)
            rw [hz] at g
            exact (hinj _ _ g).symm
          -- Same definitional `(k+1)-1 = k` ascription as above.
          have hck : ¬ l[k + 1].ult l[k] = true := hc
          have hc' : ¬ z.ult l[k] = true := by
            rw [hzj] at hck
            exact hck
          rw [if_neg hc']
        refine ⟨ρ, rfl, ?_, rfl⟩
        rw [hbub]
        exact ha

/-- The outer condition reads `i < N` off the environment (raw `ult`
    form, like the inner condition lemmas; call sites case-split). -/
theorem sortOuterCond_eval (N : Nat) (ρ : Env) (i : Nat)
    (hi : envLookup ρ "i" = some (.u64 (BitVec.ofNat 64 i))) :
    evalExpr (sortOuterCond N) ρ =
      .ok (.b ((BitVec.ofNat 64 i).ult (BitVec.ofNat 64 N))) := by
  have e_i : evalExpr (.var "i") ρ = .ok (.u64 (BitVec.ofNat 64 i)) :=
    evalExpr_var_hit _ _ _ hi
  have eN : evalExpr (.lit (.u64 (BitVec.ofNat 64 N))) ρ =
      .ok (.u64 (BitVec.ofNat 64 N)) := by
    simp [evalExpr, litVal]
  have h := evalExpr_ult_u64 _ _ ρ _ _ e_i eN
  simp only [sortOuterCond]
  exact h

/-- One outer pass: rebind `j` at `i`, bubble down (which inserts
    `l[i]` into the sorted `take i` prefix by `bubbleDown_eq`),
    step `i`. The post-pass prefix `take (i+1)` is sorted
    (`pairwise_insertU32_sorted`) with length preserved. -/
theorem sortOuterBody_step (N : Nat) (F : Nat) (ρ : Env) (l : List (BitVec 32))
    (i : Nat)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hi : envLookup ρ "i" = some (.u64 (BitVec.ofNat 64 i)))
    (hlen : l.length = N) (hN64 : N < 2 ^ 64) (hiN : i + 1 ≤ N)
    (hsorted : (l.take i).Pairwise (fun a b => b.ult a = false))
    (hF : i + 1 ≤ F) :
    ∃ ρ', evalStmtFuel F sortOuterBody ρ = .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" =
        some (.arr32 (outerListStep l i (l[i]?.getD 0))) ∧
      envLookup ρ' "i" = some (.u64 (BitVec.ofNat 64 (i + 1))) ∧
      ((outerListStep l i (l[i]?.getD 0)).take (i + 1)).Pairwise
        (fun a b => b.ult a = false) ∧
      (outerListStep l i (l[i]?.getD 0)).length = N := by
  have hi64 : i < 2 ^ 64 := by omega
  have hz : l[i]? = some l[i] := List.getElem?_eq_getElem (by omega)
  have hgetD : l[i]?.getD 0 = l[i] := by simp [hz]
  have hstep_eq : outerListStep l i (l[i]?.getD 0) =
      insertU32 l[i] (l.take i) ++ l.drop (i + 1) := by
    simp only [outerListStep, hgetD]
  -- Rebind `j` at `i`.
  have e_i : evalExpr (.var "i") ρ = .ok (.u64 (BitVec.ofNat 64 i)) :=
    evalExpr_var_hit _ _ _ hi
  have ha₁ : envLookup (envExtend ρ "j" (.u64 (BitVec.ofNat 64 i))) "a" =
      some (.arr32 l) := by
    simp [envExtend, envLookup, show ("a" : String) ≠ "j" by decide, ha]
  have hj₁ : envLookup (envExtend ρ "j" (.u64 (BitVec.ofNat 64 i))) "j" =
      some (.u64 (BitVec.ofNat 64 i)) := by
    simp [envExtend, envLookup]
  have hi₁ : envLookup (envExtend ρ "j" (.u64 (BitVec.ofNat 64 i))) "i" =
      envLookup ρ "i" := by
    simp [envExtend, envLookup, show ("i" : String) ≠ "j" by decide]
  -- Bubble down from `j = i` (prefix is trivially the entry prefix).
  obtain ⟨ρ₂, hloop, ha₂raw, hi₂raw⟩ :=
    sortInnerWhile_correct N F (envExtend ρ "j" (.u64 (BitVec.ofNat 64 i)))
      l l i l[i] ha₁ hj₁ hlen hN64 (by omega) hz rfl hF
  have hi₂' : envLookup ρ₂ "i" = some (.u64 (BitVec.ofNat 64 i)) := by
    rw [hi₂raw, hi₁]
    exact hi
  -- The bubbled array is the outer step.
  have hdrop : (l.take i).drop i = [] := by
    have hL : (l.take i).length = i := take_length_eq _ _ (by omega)
    have h := drop_all (l.take i)
    rw [hL] at h
    exact h
  have hslice : l.drop (i + 1) = (l.take i).drop i ++ l.drop (i + 1) := by
    simp [hdrop]
  have hmid : ∀ w ∈ (l.take i).drop i, l[i].ult w = true := by
    intro w hw
    rw [hdrop] at hw
    simp at hw
  have hbub := bubbleDown_eq_outerListStep N l i l i l[i] hlen hiN hsorted
    hlen (Nat.le_refl i) hz rfl hslice hmid
  have ha₂ : envLookup ρ₂ "a" =
      some (.arr32 (outerListStep l i (l[i]?.getD 0))) := by
    rw [hbub] at ha₂raw
    rw [← hstep_eq] at ha₂raw
    exact ha₂raw
  -- Step `i`.
  have e_i₂ : evalExpr (.var "i") ρ₂ = .ok (.u64 (BitVec.ofNat 64 i)) :=
    evalExpr_var_hit _ _ _ hi₂'
  -- `uadd` with a variable LHS (generalized like `evalExpr_u64_usub`,
  -- so the `var` arm cannot preempt the sub-evaluation fact).
  have euadd : ∀ (e : CExpr) (r : Env) (x : BitVec 64),
      evalExpr e r = .ok (.u64 x) →
      evalExpr (.uadd e (.lit (.u64 (BitVec.ofNat 64 1)))) r =
        .ok (.u64 (x + BitVec.ofNat 64 1)) := by
    intro e r x h
    simp [evalExpr, litVal, h]
  have e_add : evalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (BitVec.ofNat 64 (i + 1))) := by
    have h := euadd _ _ _ e_i₂
    rw [ofNat64_add_one] at h
    exact h
  obtain ⟨ρ₃, hu⟩ := envUpdate_some_of_lookup ρ₂ "i"
    (.u64 (BitVec.ofNat 64 i)) (.u64 (BitVec.ofNat 64 (i + 1))) hi₂'
  have ha₃ : envLookup ρ₃ "a" =
      some (.arr32 (outerListStep l i (l[i]?.getD 0))) := by
    have h := envLookup_envUpdate_diff ρ₂ "i" "a" _ _ hu (by decide)
    rw [ha₂] at h
    exact h
  -- The update value is already in `ofNat (i+1)` form, so no
  -- normalization rewrite is needed (unlike the swap countdown).
  have hi₃ : envLookup ρ₃ "i" = some (.u64 (BitVec.ofNat 64 (i + 1))) :=
    envLookup_envUpdate_same _ _ _ _ hu
  -- Chain the three steps (each fuel-polymorphic; no big-`simp`).
  have s1 : ∀ f, evalStmtFuel f (.let_ "j" (.u 64) (.var "i")) ρ =
      .ok (envExtend ρ "j" (.u64 (BitVec.ofNat 64 i)), .fellThrough) :=
    fun f => evalStmtFuel_let_ f _ _ _ _ _ e_i
  have s3 : ∀ f, evalStmtFuel f
      (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ρ₂ = .ok (ρ₃, .fellThrough) :=
    fun f => evalStmtFuel_assign f _ _ _ _ _ e_add hu
  -- The post-pass prefix is sorted with length preserved.
  have hL : (insertU32 l[i] (l.take i)).length = i + 1 := by
    rw [insertU32_length, take_length_eq _ _ (by omega)]
  have htakeN : ((insertU32 l[i] (l.take i) ++ l.drop (i + 1)).take
      (i + 1)) = insertU32 l[i] (l.take i) := by
    have e := take_append_self (insertU32 l[i] (l.take i)) (l.drop (i + 1))
    rw [hL] at e
    exact e
  have hnew_sorted : ((outerListStep l i (l[i]?.getD 0)).take
      (i + 1)).Pairwise (fun a b => b.ult a = false) := by
    rw [hstep_eq, htakeN]
    exact pairwise_insertU32_sorted _ _ hsorted
  have hnew_len : (outerListStep l i (l[i]?.getD 0)).length = N := by
    rw [hstep_eq, List.length_append, insertU32_length,
      take_length_eq _ _ (by omega), List.length_drop, hlen]
    omega
  refine ⟨ρ₃, ?_, ha₃, hi₃, hnew_sorted, hnew_len⟩
  simp only [sortOuterBody]
  rw [evalStmtFuel_seq_fallthrough F _ _ _ _ (s1 F),
    evalStmtFuel_seq_fallthrough F _ _ _ _ hloop]
  exact s3 F

/-- Outer-loop correctness: pass `i` bubbles `l[i]` into the sorted
    prefix (`sortOuterBody_step`), and the IH runs the remaining
    passes. Fuel `B(i) = (4-i)+4` covers the inner descent (`i+1`)
    plus one per remaining pass. -/
theorem sortOuterWhile_correct (N : Nat) (F : Nat) (ρ : Env)
    (l : List (BitVec 32))
    (i : Nat)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hi : envLookup ρ "i" = some (.u64 (BitVec.ofNat 64 i)))
    (hlen : l.length = N) (hN64 : N < 2 ^ 64) (hi1 : 1 ≤ i) (hiN : i ≤ N)
    (hsorted : (l.take i).Pairwise (fun a b => b.ult a = false))
    (hF : (N - i) + N ≤ F) :
    ∃ ρ', evalStmtFuel F (sortOuterWhile N) ρ = .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.arr32 (outerListAux N l i (N - i))) ∧
      envLookup ρ' "i" = some (.u64 (BitVec.ofNat 64 N)) := by
  induction F generalizing ρ l i ha hi hlen hN64 hi1 hiN hsorted with
  | zero =>
    have h0 : (N - i) + N ≤ 0 := hF
    have hcontra : False := by omega
    exact hcontra.elim
  | succ F ih =>
    have hi64 : i < 2 ^ 64 := by omega
    have hcond := sortOuterCond_eval N ρ i hi
    by_cases hiN' : i < N
    · -- Pass `i`: body, then the remaining passes below.
      have hc : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 N) = true := by
        rw [ofNat64_ult i _ hi64, ofNat64_toNat N hN64]
        exact decide_eq_true hiN'
      rw [hc] at hcond
      obtain ⟨ρ₂, hbody, ha₂, hi₂, hsorted₂, hlen₂⟩ :=
        sortOuterBody_step N F ρ l i ha hi hlen hN64 (by omega) hsorted
          (by omega)
      have hstep : evalStmtFuel (F + 1) (sortOuterWhile N) ρ =
          evalStmtFuel F (sortOuterWhile N) ρ₂ := by
        simp [sortOuterWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hfuel : N - i = (N - (i + 1)) + 1 := by omega
      have hF' : (N - (i + 1)) + N ≤ F := by omega
      obtain ⟨ρ', hloop, ha', hi'⟩ :=
        ih ρ₂ _ (i + 1) ha₂ hi₂ hlen₂ hN64 (by omega) (by omega) hsorted₂ hF'
      -- The loop head equals the pure unfold.
      have haux : outerListAux N l i (N - i) = outerListAux N
          (outerListStep l i (l[i]?.getD 0)) (i + 1) (N - (i + 1)) := by
        rw [hfuel, outerListAux_succ, if_pos hiN']
      refine ⟨ρ', hloop, ?_, hi'⟩
      rw [haux]
      exact ha'
    · -- Exit at `i = N`: no passes remain.
      have hiNeq : i = N := by omega
      have hc : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 N) = false := by
        rw [ofNat64_ult i _ hi64, ofNat64_toNat N hN64, hiNeq]
        simp
      rw [hc] at hcond
      have hexit : evalStmtFuel (F + 1) (sortOuterWhile N) ρ =
          .ok (ρ, .fellThrough) := by
        simp [sortOuterWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond]
      rw [hexit, hiNeq]
      refine ⟨ρ, rfl, ?_, ?_⟩
      · have hemp : outerListAux N l N (N - N) = l := by
          rw [Nat.sub_self, outerListAux_zero]
        rw [hemp]
        exact ha
      · rw [← hiNeq]
        exact hi

/-- The aux equals the insertion fold over the take/drop split: each
    pass inserts `l[i]` into the accumulator, so after `k` passes with
    `i + k = N` the accumulator holds the folded length-`N` prefix.
    Induction on the remaining passes; the step slides the split by
    one (`take_append_self` / `drop_append_self`), the base case folds
    the whole list from empty. -/
theorem outerListAux_sortL (N : Nat) (l : List (BitVec 32)) (i k : Nat)
    (hlen : l.length = N) (hik : i + k = N) :
    outerListAux N l i k = sortL (l.take i) (l.drop i) := by
  induction k generalizing l i with
  | zero =>
    have hiN : i = N := by omega
    have ht : l.take N = l := by
      rw [← hlen]
      simp
    have hd : l.drop N = [] := by
      rw [← hlen]
      simp
    rw [outerListAux_zero, hiN, ht, hd]
    rfl
  | succ k ih =>
    have hiN : i < N := by omega
    have hz : l[i]? = some l[i] := List.getElem?_eq_getElem (by omega)
    have hgetD : l[i]?.getD 0 = l[i] := by simp [hz]
    have hsteplen : (outerListStep l i l[i]).length = N := by
      rw [outerListStep, List.length_append, insertU32_length,
        take_length_eq _ _ (by omega), List.length_drop, hlen]
      omega
    have hik' : (i + 1) + k = N := by omega
    rw [outerListAux_succ, if_pos hiN, hgetD]
    rw [ih _ _ hsteplen hik']
    have hA : (insertU32 l[i] (l.take i)).length = i + 1 := by
      rw [insertU32_length, take_length_eq _ _ (by omega)]
    have htake : (outerListStep l i l[i]).take (i + 1) =
        insertU32 l[i] (l.take i) := by
      rw [outerListStep, show i + 1 = (insertU32 l[i] (l.take i)).length
        from hA.symm, take_append_self]
    have hdrop : (outerListStep l i l[i]).drop (i + 1) = l.drop (i + 1) := by
      rw [outerListStep, show i + 1 = (insertU32 l[i] (l.take i)).length
        from hA.symm, drop_append_self]
    rw [htake, hdrop, drop_of_getElem? _ _ _ hz]
    rfl


/-- `take 1` is pairwise sorted (at most one word). -/
theorem pairwise_take_one (l : List (BitVec 32)) (hlen : 1 ≤ l.length) :
    (l.take 1).Pairwise (fun a b => b.ult a = false) := by
  have hL : (l.take 1).length = 1 := take_length_eq _ _ hlen
  cases h : l.take 1 with
  | nil => exact List.Pairwise.nil
  | cons x xs =>
    cases xs with
    | nil => exact List.pairwise_singleton _ _
    | cons y ys =>
      rw [h] at hL
      simp at hL

/-- Folding from the singleton prefix sorts the whole list: the
    `i = 1` split is the head/tail split, and the fold from `[x]`
    agrees with `insertionSortList` by one `sortL_insert` step. -/
theorem sortL_take_one_drop_one (l : List (BitVec 32)) (hlen : 1 ≤ l.length) :
    sortL (l.take 1) (l.drop 1) = insertionSortList l := by
  cases l with
  | nil => simp at hlen
  | cons x xs =>
    have t : (x :: xs).take 1 = [x] := rfl
    have d : (x :: xs).drop 1 = xs := rfl
    rw [t, d]
    show sortL [x] xs = insertU32 x (insertionSortList xs)
    have e1 : insertU32 x [] = [x] := rfl
    have e2 := sortL_insert x [] xs
    rw [e1] at e2
    rw [sortL_nil]
    exact e2

/-- `emit_correct` for `insertion_sort`: bind `a`, run the outer
    passes from the singleton prefix (`sortOuterWhile_correct` at
    `i = 1`, fuel `(N-1)+N`), return the array — which is the insertion
    fold by `outerListAux_sortL` + `sortL_take_one_drop_one`. -/
theorem evalFuncFuel_insertionSort (N : Nat) (F : Nat) (l : List (BitVec 32))
    (hlen : l.length = N) (hN64 : N < 2 ^ 64) (h1N : 1 ≤ N)
    (hF : (N - 1) + N ≤ F) :
    evalFuncFuel F (insertionSortFunc N) [.arr32 l] = insertionSortFwd l := by
  have hbind : bindArgs (insertionSortFunc N).args [.arr32 l] =
      some [("a", .arr32 l)] := rfl
  have e_one : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [("a", .arr32 l)] = .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have s1 : evalStmtFuel F (.let_ "i" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))) [("a", .arr32 l)] =
      .ok (envExtend [("a", .arr32 l)] "i" (.u64 (BitVec.ofNat 64 1)),
        .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ e_one
  have ha₁ : envLookup
      (envExtend [("a", .arr32 l)] "i" (.u64 (BitVec.ofNat 64 1))) "a" =
      some (.arr32 l) := by
    simp [envExtend, envLookup, show ("a" : String) ≠ "i" by decide]
  have hi₁ : envLookup
      (envExtend [("a", .arr32 l)] "i" (.u64 (BitVec.ofNat 64 1))) "i" =
      some (.u64 (BitVec.ofNat 64 1)) := by
    simp [envExtend, envLookup]
  obtain ⟨ρ₂, hloop, ha₂, _⟩ :=
    sortOuterWhile_correct N F
      (envExtend [("a", .arr32 l)] "i" (.u64 (BitVec.ofNat 64 1))) l 1
      ha₁ hi₁ hlen hN64 (by decide : 1 ≤ 1) h1N
      (pairwise_take_one l (by omega)) hF
  have e_ret : evalExpr (.var "a") ρ₂ =
      .ok (.arr32 (outerListAux N l 1 (N - 1))) :=
    evalExpr_var_hit _ _ _ ha₂
  have hret : evalStmtFuel F (.return_ (.var "a")) ρ₂ =
      .ok (ρ₂, .returned (.arr32 (outerListAux N l 1 (N - 1)))) :=
    evalStmtFuel_return F _ _ _ e_ret
  have hbody : evalStmtFuel F (insertionSortFunc N).body [("a", .arr32 l)] =
      .ok (ρ₂, .returned (.arr32 (outerListAux N l 1 (N - 1)))) := by
    rw [insertionSortFunc_body]
    rw [evalStmtFuel_seq_fallthrough F _ _ _ _ s1,
      evalStmtFuel_seq_fallthrough F _ _ _ _ hloop]
    exact hret
  have hfunc : evalFuncFuel F (insertionSortFunc N) [.arr32 l] =
      .ok (.arr32 (outerListAux N l 1 (N - 1))) := by
    simp only [evalFuncFuel, hbind, hbody]
  -- The loop result is the insertion fold.
  have hsorted_eq : outerListAux N l 1 (N - 1) = insertionSortList l := by
    have h := outerListAux_sortL N l 1 (N - 1) hlen (by omega)
    rw [h]
    exact sortL_take_one_drop_one l (by omega)
  rw [hsorted_eq] at hfunc
  simpa [insertionSortFwd] using hfunc

/-- Closed program for the case study: the two array leaves, the
    sort, and the entry. -/
def arraySortProg : Prog :=
  [arrayRefU32Func, arrayAtU32Func, insertionSortFunc 4,
    arraySortSumEntryFunc]

/-- `findFunc` resolves the sort callee. -/
theorem findFunc_insertionSort :
    findFunc arraySortProg insertionSortName = some (insertionSortFunc 4) := by
  unfold arraySortProg
  rw [findFunc_miss _ _ _ (by decide), findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the indexed-read leaf. -/
theorem findFunc_arrayAtU32 :
    findFunc arraySortProg arrayAtU32Name = some arrayAtU32Func := by
  unfold arraySortProg
  rw [findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `emit_correct` for `array_sort_sum`: the closed entry over the
    sort program agrees with the compute-to-`6` forward.

    Collapsed proof (`cir_eval_closed`, N8c-style): both sides are
    closed terms — `#eval` reduces each to `.ok 6` — so the proof is
    computation, not reasoning. Fuel is `7`, not the leaf `6`: the
    entry pays one level for the `callProg` into the sort on top of
    the sort's own depth (probed minimal — fuel `6` exhausts). -/
theorem evalProgFunc_arraySortSumEntry :
    evalProgFunc arraySortProg 7 arraySortSumEntryFunc [] =
      arraySortSumEntryFwd := by
  cir_eval_closed

/-! ## N9-iv: Sorted/Permutation spec (the sort contract) -/

/-- The fold preserves pairwise sortedness: each step inserts below
    (`pairwise_insertU32_sorted`), so the accumulator stays sorted. -/
theorem sortL_sorted (acc : List (BitVec 32)) (xs : List (BitVec 32))
    (h : acc.Pairwise (fun a b => b.ult a = false)) :
    (sortL acc xs).Pairwise (fun a b => b.ult a = false) := by
  induction xs generalizing acc with
  | nil => exact h
  | cons y ys ih =>
    show (sortL (insertU32 y acc) ys).Pairwise _
    exact ih _ (pairwise_insertU32_sorted _ _ h)

/-- `insertionSortList` is sorted ascending (empty accumulator is
    vacuously sorted). -/
theorem insertionSortList_sorted (l : List (BitVec 32)) :
    (insertionSortList l).Pairwise (fun a b => b.ult a = false) := by
  rw [sortL_nil]
  exact sortL_sorted [] l List.Pairwise.nil

/-- Insertion preserves the multiset: the word lands before the
    first strictly greater one, otherwise the tails permute with a
    head swap. -/
theorem insertU32_perm (x : BitVec 32) (l : List (BitVec 32)) :
    List.Perm (insertU32 x l) (x :: l) := by
  induction l with
  | nil => exact List.Perm.rfl
  | cons y ys ih =>
    simp only [insertU32]
    by_cases h : x.ult y = true
    · simp only [h]
      exact List.Perm.rfl
    · simp only [h]
      exact (ih.cons y).trans (List.Perm.swap x y ys)

/-- `insertionSortList` permutes its input (insert below, then the
    tail permutes under the cons). -/
theorem insertionSortList_perm (l : List (BitVec 32)) :
    List.Perm (insertionSortList l) l := by
  induction l with
  | nil => exact List.Perm.rfl
  | cons x xs ih =>
    show List.Perm (insertU32 x (insertionSortList xs)) (x :: xs)
    exact (insertU32_perm x _).trans (ih.cons x)

/-- The emitted sort returns a sorted permutation of its input
    (the N9-iv contract: `evalFuncFuel_insertionSort` closed at the
    pure-list spec). -/
theorem evalFuncFuel_insertionSort_spec (N : Nat) (F : Nat) (l : List (BitVec 32))
    (hlen : l.length = N) (hN64 : N < 2 ^ 64) (h1N : 1 ≤ N)
    (hF : (N - 1) + N ≤ F) :
    ∃ s, evalFuncFuel F (insertionSortFunc N) [.arr32 l] = .ok (.arr32 s) ∧
      s.Pairwise (fun a b => b.ult a = false) ∧ List.Perm s l := by
  rw [evalFuncFuel_insertionSort N F l hlen hN64 h1N hF]
  exact ⟨insertionSortList l, rfl, insertionSortList_sorted l,
    insertionSortList_perm l⟩
