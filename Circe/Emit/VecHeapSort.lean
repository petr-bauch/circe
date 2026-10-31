/-
Circe.Emit.VecHeapSort — H-slice iterative in-place ascending
heapsort: the `heap_sort` entry.

The corpus (`tests/cpp/heap_sort.cpp`: mut `v`, `u64` heap length
`n` in, words out) carries the entry + twenty mut-`at()` sites.
Down-counting heapify from `n` (`usub`, leaves are no-ops) plus
extract-max; each sift computes `child = 2*root+1` with wrapping
`u64` (`umul`/`uadd`) — no division anywhere (the subset has no
unsigned div). Reads go through the pure `stdVecAt` expression
(J precedent), writes through `vecSet` (R precedent); the C++
`int t` spill allocas fuse to the direct word flow (no temps for
the swap values beyond the `aR`/`aC` compare binds). Both `&&`
child-picks are nested `if_`s; `while(true)` sifts exit by
`break` (S3a-native).

The two sift phases share ONE body through the env `B` bound
variable (set to `n` once for heapify, to the shrinking `last`
per extract iteration): the raw CIR duplicates the sift code,
but the emitter shares it — the H3 diff (eval-vs-native word
agreement) covers the raw↔emit gap, the J/BFS precedent.

Termination is by fuel lockstep: the sift descends (`cand >
root` while `root < bound ≤ 2^63`, a hypothesis the entry
discharges from the heap length), the drains count down. Fuel
bounds are stated per lemma (S3a induction pattern); cyclic
behavior cannot arise (no links), short `n` (past the vector
length) misses loud at the first out-of-range `at()`.
-/
import Circe.Emit.VecListRev
import Circe.Emit.VecSelectionSort
import Circe.Lemmas.CheckedIx

/-! ## H: `heap_sort` entry -/

/-- Mangled name of the heapsort entry. -/
def heapName : String :=
  "_Z9heap_sortRSt6vectorIiSaIiEEm"

/-- Seed: `i = last = B = n`; the remaining cursors start at
    zero (never read before their first bind, and `envUpdate`
    needs every assigned slot present). Matches `mkHeapEnv`. -/
def heapSeed : CStmt :=
  .seq (.let_ "i" (.u 64) (.var "n"))
  (.seq (.let_ "last" (.u 64) (.var "n"))
  (.seq (.let_ "B" (.u 64) (.var "n"))
  (.seq (.let_ "root" (.u 64) (.lit (.u64 0)))
  (.seq (.let_ "child" (.u 64) (.lit (.u64 0)))
  (.seq (.let_ "other" (.u 64) (.lit (.u64 0)))
  (.seq (.let_ "aR" (.i 32) (.lit (.i32 0)))
    (.let_ "aC" (.i 32) (.lit (.i32 0)))))))))

/-- Child indices: `child = 2*root+1`, `other = child+1`
    (wrapping `u64`). -/
def siftIdx : CStmt :=
  .seq (.assign "child"
    (.uadd (.umul (.var "root") (.lit (.u64 2))) (.lit (.u64 1))))
  (.assign "other" (.uadd (.var "child") (.lit (.u64 1))))

/-- Child pick: `if other < B and v[other] > v[child]`, take
    `other` (nested `if_`, the `&&` shape — the `at()` reads
    run only under the bound guard). -/
def siftPick : CStmt :=
  .if_ (.ult (.var "other") (.var "B"))
    (.if_ (.slt (.stdVecAt "v" (.var "child"))
              (.stdVecAt "v" (.var "other")))
      (.assign "child" (.var "other"))
      .skip)
    .skip

/-- Compare binds + swap-or-break: read both words (miss is
    loud), swap through `vecSet` and advance on `aR < aC`,
    `break` otherwise. -/
def siftSwap : CStmt :=
  .seq (.assign "aR" (.stdVecAt "v" (.var "root")))
  (.seq (.assign "aC" (.stdVecAt "v" (.var "child")))
  (.if_ (.slt (.var "aR") (.var "aC"))
    (.seq (.vecSet "v" (.var "root") (.var "aC"))
      (.seq (.vecSet "v" (.var "child") (.var "aR"))
        (.assign "root" (.var "child"))))
    .break_))

/-- One sift iteration: indices, bound-break exit, pick,
    compare binds, swap-or-break (fall-through re-sifts). -/
def heapSiftBody : CStmt :=
  .seq siftIdx
  (.if_ (.ult (.var "child") (.var "B"))
    (.seq siftPick siftSwap)
    .break_)

/-- The sift: `while (true)` with break exits. -/
def heapSift : CStmt :=
  .while_ (.lit (.b true)) heapSiftBody

/-- Heapify drain body: `i--`, sift from `i`. -/
def heapDrainBody : CStmt :=
  .seq (.assign "i" (.usub (.var "i") (.lit (.u64 1))))
  (.seq (.assign "root" (.var "i"))
    heapSift)

/-- Heapify drain: `while (i != 0)`. -/
def heapDrain : CStmt :=
  .while_ (.une (.var "i") (.lit (.u64 0))) heapDrainBody

/-- Extract swap: exchange root/last words, shrink the sift
    bound to the new `last`. -/
def extrSwap : CStmt :=
  .seq (.assign "aR" (.stdVecAt "v" (.lit (.u64 0))))
  (.seq (.assign "aC" (.stdVecAt "v" (.var "last")))
  (.seq (.vecSet "v" (.lit (.u64 0)) (.var "aC"))
  (.seq (.vecSet "v" (.var "last") (.var "aR"))
    (.assign "B" (.var "last")))))

/-- Extract drain body: `last--`, swap, sift from the root. -/
def extrDrainBody : CStmt :=
  .seq (.assign "last" (.usub (.var "last") (.lit (.u64 1))))
  (.seq extrSwap
  (.seq (.assign "root" (.lit (.u64 0)))
    heapSift))

/-- Extract drain: `while (last != 0)`. -/
def extrDrain : CStmt :=
  .while_ (.une (.var "last") (.lit (.u64 0))) extrDrainBody

/-- Canonical CoreIR for `heap_sort`: seed, heapify, extract,
    return of the updated words (C++ `void` functionalizes as
    words threading, the R precedent). -/
def heapSortFunc : Func :=
  ⟨heapName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "n", ty := .u 64, role := .owned }],
   stdVecObjTy,
   (.seq heapSeed
     (.seq heapDrain
       (.seq extrDrain
         (.return_ (.var "v")))))⟩

/-- Whole-program wrapper: the single-function `heapSortFunc`
    program (no calls; the singleton list suffices for
    `evalProgFunc` composition in the differential test). -/
def heapSortProg : Prog := [heapSortFunc]

/-- Sift environment: reified words, heap length, down-counters,
    sift bound, cursors, compare binds. Built as an `envExtend`
    chain in seed order, so the seed lets land on it exactly. -/
def mkHeapEnv (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) : Env :=
  envExtend (envExtend (envExtend (envExtend (envExtend (envExtend
    (envExtend (envExtend [("v", .stdVecVal vL), ("n", .u64 n)]
      "i" (.u64 i)) "last" (.u64 last)) "B" (.u64 B))
      "root" (.u64 root)) "child" (.u64 child))
      "other" (.u64 other)) "aR" (.i32 aR)) "aC" (.i32 aC)

theorem mkHeapEnv_v (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) := by
  simp [mkHeapEnv, envExtend, envLookup]

theorem mkHeapEnv_n (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "n" =
      some (.u64 n) := by
  simp [mkHeapEnv, envExtend, envLookup]

theorem mkHeapEnv_i (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "i" =
      some (.u64 i) := by
  simp [mkHeapEnv, envExtend, envLookup]

theorem mkHeapEnv_last (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "last" =
      some (.u64 last) := by
  simp [mkHeapEnv, envExtend, envLookup]

theorem mkHeapEnv_B (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "B" =
      some (.u64 B) := by
  simp [mkHeapEnv, envExtend, envLookup]

theorem mkHeapEnv_root (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "root" =
      some (.u64 root) := by
  simp [mkHeapEnv, envExtend, envLookup]

theorem mkHeapEnv_child (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "child" =
      some (.u64 child) := by
  simp [mkHeapEnv, envExtend, envLookup]

theorem mkHeapEnv_other (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "other" =
      some (.u64 other) := by
  simp [mkHeapEnv, envExtend, envLookup]

theorem mkHeapEnv_aR (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "aR" =
      some (.i32 aR) := by
  simp [mkHeapEnv, envExtend, envLookup]

theorem mkHeapEnv_aC (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64)
    (aR aC : BitVec 32) :
    envLookup (mkHeapEnv vL n i last B root child other aR aC) "aC" =
      some (.i32 aC) := by
  simp [mkHeapEnv, envExtend, envLookup]

/-! ## Forward mirrors (fuel-threaded) -/

/-- One sift level: bound-break exit, child pick (read-guarded),
    compare + swap-recurse (each `at()` site gets its own match,
    evaluator fidelity — reads and ptr-stores at the same index
    coincide since nothing mutates between them). -/
def siftFwd (F : Nat) (v : List (BitVec 32))
    (bound root : BitVec 64) : Result (List (BitVec 32)) :=
  match F with
  | 0 => .error .AssertFail
  | F + 1 =>
    let child := root * 2 + 1
    if child.ult bound then
      let other := child + 1
      if other.ult bound then
        match v[other.toNat]?, v[child.toNat]? with
        | some wo, some wc =>
          let cand := if wc.slt wo then other else child
          match v[root.toNat]?, v[cand.toNat]? with
          | some a, some b =>
            if a.slt b then
              siftFwd F (v.set root.toNat b |>.set cand.toNat a)
                bound cand
            else .ok v
          | _, _ => .error .OOB
        | _, _ => .error .OOB
      else
        match v[root.toNat]?, v[child.toNat]? with
        | some a, some b =>
          if a.slt b then
            siftFwd F (v.set root.toNat b |>.set child.toNat a)
              bound child
          else .ok v
        | _, _ => .error .OOB
    else .ok v

/-- Heapify drain: count `i` down, sifting from each. -/
def heapifyFwd (F : Nat) (v : List (BitVec 32))
    (n i : BitVec 64) : Result (List (BitVec 32)) :=
  match F with
  | 0 => if i != 0 then .error .AssertFail else .ok v
  | F + 1 =>
    if i != 0 then
      let i' := i - 1
      match siftFwd F v n i' with
      | .error e => .error e
      | .ok v' => heapifyFwd F v' n i'
    else .ok v

/-- Extract drain: count `last` down, swapping root/last and
    re-sifting the shrunk heap. -/
def extractFwd (F : Nat) (v : List (BitVec 32))
    (n last : BitVec 64) : Result (List (BitVec 32)) :=
  match F with
  | 0 => if last != 0 then .error .AssertFail else .ok v
  | F + 1 =>
    if last != 0 then
      let last' := last - 1
      match v[0]?, v[last'.toNat]? with
      | some a, some b =>
        match siftFwd F (v.set 0 b |>.set last'.toNat a) last' 0 with
        | .error e => .error e
        | .ok v' => extractFwd F v' n last'
      | _, _ => .error .OOB
    else .ok v

/-- Entry mirror: heapify, then extract; the words out. -/
def heapSortFwd (F : Nat) (v : List (BitVec 32))
    (n : BitVec 64) : Result Value :=
  match heapifyFwd F v n n with
  | .error e => .error e
  | .ok v' =>
    match extractFwd F v' n n with
    | .error e => .error e
    | .ok v'' => .ok (.stdVecVal v'')

/-! ## Sift fragment twins (straight-line, J2-shaped) -/

/-- Index computation: `child = root*2+1`, `other = child+1`
    (any fuel). -/
theorem siftIdx_ok (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32) :
    evalStmtFuel F siftIdx
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1) aR aC,
        .fellThrough) := by
  have hbody : siftIdx =
      (.seq (.assign "child"
        (.uadd (.umul (.var "root") (.lit (.u64 2))) (.lit (.u64 1))))
      (.assign "other"
        (.uadd (.var "child") (.lit (.u64 1))))) := rfl
  have hroot : evalExpr (.var "root")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 root) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_root _ _ _ _ _ _ _ _ _ _)
  have h2 : evalExpr (.lit (.u64 2))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 2) := rfl
  have h1 : evalExpr (.lit (.u64 1))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 1) := rfl
  have hmul := evalExpr_umul_u64 _ _ _ _ _ hroot h2
  have hchildE := evalExpr_uadd_u64 _ _ _ _ _ hmul h1
  have hchild : evalExpr
      (.uadd (.umul (.var "root") (.lit (.u64 2))) (.lit (.u64 1)))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 (root*2+1)) := hchildE
  have huC : envUpdate
      (mkHeapEnv vL n i last B root child other aR aC) "child"
      (.u64 (root*2+1)) =
      some (mkHeapEnv vL n i last B root (root*2+1) other aR aC) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignC := evalStmtFuel_assign F "child"
    (.uadd (.umul (.var "root") (.lit (.u64 2))) (.lit (.u64 1)))
    (mkHeapEnv vL n i last B root child other aR aC) _ _ hchild huC
  have hchild2 : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root (root*2+1) other aR aC) =
      .ok (.u64 (root*2+1)) :=
    evalExpr_var_hit _ _ _
      (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have h1' : evalExpr (.lit (.u64 1))
      (mkHeapEnv vL n i last B root (root*2+1) other aR aC) =
      .ok (.u64 1) := rfl
  have hotherE := evalExpr_uadd_u64 _ _ _ _ _ hchild2 h1'
  have hother : evalExpr (.uadd (.var "child") (.lit (.u64 1)))
      (mkHeapEnv vL n i last B root (root*2+1) other aR aC) =
      .ok (.u64 (root*2+1+1)) := hotherE
  have huO : envUpdate
      (mkHeapEnv vL n i last B root (root*2+1) other aR aC) "other"
      (.u64 (root*2+1+1)) =
      some (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1)
        aR aC) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignO := evalStmtFuel_assign F "other"
    (.uadd (.var "child") (.lit (.u64 1)))
    (mkHeapEnv vL n i last B root (root*2+1) other aR aC) _ _
    hother huO
  have hidx : evalStmtFuel F
      (.seq (.assign "child"
        (.uadd (.umul (.var "root") (.lit (.u64 2))) (.lit (.u64 1))))
      (.assign "other" (.uadd (.var "child") (.lit (.u64 1)))))
      (mkHeapEnv vL n i last B root child other aR aC) =
      evalStmtFuel F
      (.assign "other" (.uadd (.var "child") (.lit (.u64 1))))
      (mkHeapEnv vL n i last B root (root*2+1) other aR aC) :=
    evalStmtFuel_seq_fallthrough F _ _ _ _ hassignC
  rw [hbody]
  exact hidx.trans hassignO

/-- Pick taken: `other < B` with the larger word at `other`. -/
theorem siftPick_take (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (wo wc : BitVec 32)
    (ho : other.ult B = true)
    (hgo : vL[other.toNat]? = some wo)
    (hgc : vL[child.toNat]? = some wc)
    (hlt : wc.slt wo = true) :
    evalStmtFuel F siftPick
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (mkHeapEnv vL n i last B root other other aR aC,
        .fellThrough) := by
  have hbody : siftPick =
      (.if_ (.ult (.var "other") (.var "B"))
        (.if_ (.slt (.stdVecAt "v" (.var "child"))
                    (.stdVecAt "v" (.var "other")))
          (.assign "child" (.var "other"))
          .skip)
        .skip) := rfl
  have hother : evalExpr (.var "other")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 other) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_other _ _ _ _ _ _ _ _ _ _)
  have hB : evalExpr (.var "B")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 B) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
  have hcond := evalExpr_ult_u64 _ _ _ _ _ hother hB
  rw [ho] at hcond
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hchild : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hro : evalExpr (.stdVecAt "v" (.var "other"))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.i32 wo) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hother hgo
  have hrc : evalExpr (.stdVecAt "v" (.var "child"))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.i32 wc) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hchild hgc
  have hcond2 := evalExpr_slt_i32 _ _ _ _ _ hrc hro
  rw [hlt] at hcond2
  have htake : evalExpr (.var "other")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 other) := hother
  have hu : envUpdate
      (mkHeapEnv vL n i last B root child other aR aC) "child"
      (.u64 other) =
      some (mkHeapEnv vL n i last B root other other aR aC) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassign := evalStmtFuel_assign F "child" (.var "other")
    (mkHeapEnv vL n i last B root child other aR aC) _ _ htake hu
  rw [hbody]
  exact ((evalStmtFuel_if_true F _ _ _ _ hcond).trans
    ((evalStmtFuel_if_true F _ _ _ _ hcond2).trans hassign))

/-- Pick skipped: `other` out of the heap. -/
theorem siftPick_skipO (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (ho : other.ult B = false) :
    evalStmtFuel F siftPick
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (mkHeapEnv vL n i last B root child other aR aC,
        .fellThrough) := by
  have hother : evalExpr (.var "other")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 other) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_other _ _ _ _ _ _ _ _ _ _)
  have hB : evalExpr (.var "B")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 B) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
  have hcond := evalExpr_ult_u64 _ _ _ _ _ hother hB
  rw [ho] at hcond
  have hbody : siftPick =
      (.if_ (.ult (.var "other") (.var "B"))
        (.if_ (.slt (.stdVecAt "v" (.var "child"))
                    (.stdVecAt "v" (.var "other")))
          (.assign "child" (.var "other"))
          .skip)
        .skip) := rfl
  rw [hbody]
  exact (evalStmtFuel_if_false F _ _ _ _ hcond).trans
    (by cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])

/-- Pick skipped: `child` already holds the larger word. -/
theorem siftPick_skipC (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (wo wc : BitVec 32)
    (ho : other.ult B = true)
    (hgo : vL[other.toNat]? = some wo)
    (hgc : vL[child.toNat]? = some wc)
    (hlt : wc.slt wo = false) :
    evalStmtFuel F siftPick
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (mkHeapEnv vL n i last B root child other aR aC,
        .fellThrough) := by
  have hother : evalExpr (.var "other")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 other) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_other _ _ _ _ _ _ _ _ _ _)
  have hB : evalExpr (.var "B")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 B) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
  have hcond := evalExpr_ult_u64 _ _ _ _ _ hother hB
  rw [ho] at hcond
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hchild : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hro : evalExpr (.stdVecAt "v" (.var "other"))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.i32 wo) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hother hgo
  have hrc : evalExpr (.stdVecAt "v" (.var "child"))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.i32 wc) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hchild hgc
  have hcond2 := evalExpr_slt_i32 _ _ _ _ _ hrc hro
  rw [hlt] at hcond2
  have hbody : siftPick =
      (.if_ (.ult (.var "other") (.var "B"))
        (.if_ (.slt (.stdVecAt "v" (.var "child"))
                    (.stdVecAt "v" (.var "other")))
          (.assign "child" (.var "other"))
          .skip)
        .skip) := rfl
  rw [hbody]
  exact ((evalStmtFuel_if_true F _ _ _ _ hcond).trans
    ((evalStmtFuel_if_false F _ _ _ _ hcond2).trans
      (by cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])))

/-- Pick misses on `other` (read order: `child` first). -/
theorem siftPick_errO (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (wc : BitVec 32)
    (ho : other.ult B = true)
    (hgc : vL[child.toNat]? = some wc)
    (hgo : vL[other.toNat]? = none) :
    evalStmtFuel F siftPick
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB := by
  have hother : evalExpr (.var "other")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 other) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_other _ _ _ _ _ _ _ _ _ _)
  have hB : evalExpr (.var "B")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 B) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
  have hcond := evalExpr_ult_u64 _ _ _ _ _ hother hB
  rw [ho] at hcond
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hchild : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hrc : evalExpr (.stdVecAt "v" (.var "child"))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.i32 wc) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hchild hgc
  have hro : evalExpr (.stdVecAt "v" (.var "other"))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB :=
    evalExpr_stdVecAt_oob _ _ _ _ _ hv hother hgo
  have hunfold : evalExpr
      (.slt (.stdVecAt "v" (.var "child"))
            (.stdVecAt "v" (.var "other")))
      (mkHeapEnv vL n i last B root child other aR aC) =
      match evalExpr (.stdVecAt "v" (.var "child"))
              (mkHeapEnv vL n i last B root child other aR aC),
            evalExpr (.stdVecAt "v" (.var "other"))
              (mkHeapEnv vL n i last B root child other aR aC) with
      | .ok (.i32 x), .ok (.i32 y) => .ok (.b (x.slt y))
      | .ok _, .ok _ => .error .AssertFail
      | .error e, _ => .error e
      | _, .error e => .error e := rfl
  have herr : evalExpr
      (.slt (.stdVecAt "v" (.var "child"))
            (.stdVecAt "v" (.var "other")))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB := by
    rw [hunfold, hrc, hro]
  have hbody : siftPick =
      (.if_ (.ult (.var "other") (.var "B"))
        (.if_ (.slt (.stdVecAt "v" (.var "child"))
                    (.stdVecAt "v" (.var "other")))
          (.assign "child" (.var "other"))
          .skip)
        .skip) := rfl
  rw [hbody]
  exact (evalStmtFuel_if_true F _ _ _ _ hcond).trans
    (by cases F <;> simp only [evalStmtFuel, evalStmtZero, evalStmtWith, herr])

/-- Pick misses on `child` (evaluated first). -/
theorem siftPick_errC (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (hgc : vL[child.toNat]? = none)
    (ho : other.ult B = true) :
    evalStmtFuel F siftPick
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB := by
  have hother : evalExpr (.var "other")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 other) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_other _ _ _ _ _ _ _ _ _ _)
  have hB : evalExpr (.var "B")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 B) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
  have hcond := evalExpr_ult_u64 _ _ _ _ _ hother hB
  rw [ho] at hcond
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hchild : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hrc : evalExpr (.stdVecAt "v" (.var "child"))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB :=
    evalExpr_stdVecAt_oob _ _ _ _ _ hv hchild hgc
  have hunfold : evalExpr
      (.slt (.stdVecAt "v" (.var "child"))
            (.stdVecAt "v" (.var "other")))
      (mkHeapEnv vL n i last B root child other aR aC) =
      match evalExpr (.stdVecAt "v" (.var "child"))
              (mkHeapEnv vL n i last B root child other aR aC),
            evalExpr (.stdVecAt "v" (.var "other"))
              (mkHeapEnv vL n i last B root child other aR aC) with
      | .ok (.i32 x), .ok (.i32 y) => .ok (.b (x.slt y))
      | .ok _, .ok _ => .error .AssertFail
      | .error e, _ => .error e
      | _, .error e => .error e := rfl
  have herr : evalExpr
      (.slt (.stdVecAt "v" (.var "child"))
            (.stdVecAt "v" (.var "other")))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB := by
    rw [hunfold, hrc]
  have hbody : siftPick =
      (.if_ (.ult (.var "other") (.var "B"))
        (.if_ (.slt (.stdVecAt "v" (.var "child"))
                    (.stdVecAt "v" (.var "other")))
          (.assign "child" (.var "other"))
          .skip)
        .skip) := rfl
  rw [hbody]
  exact (evalStmtFuel_if_true F _ _ _ _ hcond).trans
    (by cases F <;> simp only [evalStmtFuel, evalStmtZero, evalStmtWith, herr])

/-- Swap taken: `aR < aC` rewrites both links and advances. -/
theorem siftSwap_swap (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (a b : BitVec 32)
    (hgr : vL[root.toNat]? = some a)
    (hgc : vL[child.toNat]? = some b)
    (hne : root.toNat ≠ child.toNat)
    (hlt : a.slt b = true) :
    evalStmtFuel F siftSwap
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (mkHeapEnv ((vL.set root.toNat b).set child.toNat a)
        n i last B child child other a b, .fellThrough) := by
  have hbody : siftSwap =
      (.seq (.assign "aR" (.stdVecAt "v" (.var "root")))
      (.seq (.assign "aC" (.stdVecAt "v" (.var "child")))
      (.if_ (.slt (.var "aR") (.var "aC"))
        (.seq (.vecSet "v" (.var "root") (.var "aC"))
          (.seq (.vecSet "v" (.var "child") (.var "aR"))
            (.assign "root" (.var "child"))))
        .break_))) := rfl
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hroot : evalExpr (.var "root")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 root) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_root _ _ _ _ _ _ _ _ _ _)
  have hchild : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hreadR := evalExpr_stdVecAt_some _ _ _ _ _ _ hv hroot hgr
  have huR : envUpdate
      (mkHeapEnv vL n i last B root child other aR aC) "aR"
      (.i32 a) =
      some (mkHeapEnv vL n i last B root child other a aC) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignR := evalStmtFuel_assign F "aR"
    (.stdVecAt "v" (.var "root"))
    (mkHeapEnv vL n i last B root child other aR aC) _ _ hreadR huR
  have hchild2 : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other a aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _
      (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hv2 : envLookup
      (mkHeapEnv vL n i last B root child other a aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hreadC := evalExpr_stdVecAt_some _ _ _ _ _ _ hv2 hchild2 hgc
  have huC : envUpdate
      (mkHeapEnv vL n i last B root child other a aC) "aC"
      (.i32 b) =
      some (mkHeapEnv vL n i last B root child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignC := evalStmtFuel_assign F "aC"
    (.stdVecAt "v" (.var "child"))
    (mkHeapEnv vL n i last B root child other a aC) _ _ hreadC huC
  have haR : evalExpr (.var "aR")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.i32 a) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aR _ _ _ _ _ _ _ _ _ _)
  have haC : evalExpr (.var "aC")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.i32 b) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aC _ _ _ _ _ _ _ _ _ _)
  have hcond := evalExpr_slt_i32 _ _ _ _ _ haR haC
  rw [hlt] at hcond
  have hroot2 : evalExpr (.var "root")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.u64 root) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_root _ _ _ _ _ _ _ _ _ _)
  have hchild3 : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hv3 : envLookup
      (mkHeapEnv vL n i last B root child other a b) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have huR : envUpdate
      (mkHeapEnv vL n i last B root child other a b) "v"
      (.stdVecVal (vL.set root.toNat b)) =
      some (mkHeapEnv (vL.set root.toNat b) n i last B root child
        other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hsetR := evalStmtFuel_vecSet F "v" (.var "root") (.var "aC")
    (mkHeapEnv vL n i last B root child other a b)
    root b vL a _ hroot2 haC hv3 hgr huR
  have hroot3 : evalExpr (.var "root")
      (mkHeapEnv (vL.set root.toNat b) n i last B root child other
        a b) =
      .ok (.u64 root) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_root _ _ _ _ _ _ _ _ _ _)
  have hchild4 : evalExpr (.var "child")
      (mkHeapEnv (vL.set root.toNat b) n i last B root child other
        a b) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have haR2 : evalExpr (.var "aR")
      (mkHeapEnv (vL.set root.toNat b) n i last B root child other
        a b) =
      .ok (.i32 a) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aR _ _ _ _ _ _ _ _ _ _)
  have hv4 : envLookup
      (mkHeapEnv (vL.set root.toNat b) n i last B root child other
        a b) "v" =
      some (.stdVecVal (vL.set root.toNat b)) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hget2 : ((vL.set root.toNat b)[child.toNat]? = some b) := by
    simp [hne, hgc]
  have huC : envUpdate
      (mkHeapEnv (vL.set root.toNat b) n i last B root child other
        a b) "v"
      (.stdVecVal ((vL.set root.toNat b).set child.toNat a)) =
      some (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n i
        last B root child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hsetC := evalStmtFuel_vecSet F "v" (.var "child") (.var "aR")
    (mkHeapEnv (vL.set root.toNat b) n i last B root child other
      a b)
    child a (vL.set root.toNat b) b _ hchild4 haR2 hv4 hget2 huC
  have hchild5 : evalExpr (.var "child")
      (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n i last
        B root child other a b) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have huRt : envUpdate
      (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n i last
        B root child other a b) "root" (.u64 child) =
      some (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n
        i last B child child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignRt := evalStmtFuel_assign F "root" (.var "child")
    (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n i last
      B root child other a b) _ _ hchild5 huRt
  rw [hbody]
  exact ((evalStmtFuel_seq_fallthrough F _ _ _ _ hassignR).trans
    ((evalStmtFuel_seq_fallthrough F _ _ _ _ hassignC).trans
      ((evalStmtFuel_if_true F _ _ _ _ hcond).trans
        (((evalStmtFuel_seq_fallthrough F _ _ _ _ hsetR).trans
          ((evalStmtFuel_seq_fallthrough F _ _ _ _ hsetC).trans
            hassignRt))))))

/-- Swap skipped: heap order already holds (`broke`, binds kept). -/
theorem siftSwap_break (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (a b : BitVec 32)
    (hgr : vL[root.toNat]? = some a)
    (hgc : vL[child.toNat]? = some b)
    (hlt : a.slt b = false) :
    evalStmtFuel F siftSwap
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (mkHeapEnv vL n i last B root child other a b,
        .broke) := by
  have hbody : siftSwap =
      (.seq (.assign "aR" (.stdVecAt "v" (.var "root")))
      (.seq (.assign "aC" (.stdVecAt "v" (.var "child")))
      (.if_ (.slt (.var "aR") (.var "aC"))
        (.seq (.vecSet "v" (.var "root") (.var "aC"))
          (.seq (.vecSet "v" (.var "child") (.var "aR"))
            (.assign "root" (.var "child"))))
        .break_))) := rfl
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hroot : evalExpr (.var "root")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 root) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_root _ _ _ _ _ _ _ _ _ _)
  have hchild : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hreadR := evalExpr_stdVecAt_some _ _ _ _ _ _ hv hroot hgr
  have huR : envUpdate
      (mkHeapEnv vL n i last B root child other aR aC) "aR"
      (.i32 a) =
      some (mkHeapEnv vL n i last B root child other a aC) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignR := evalStmtFuel_assign F "aR"
    (.stdVecAt "v" (.var "root"))
    (mkHeapEnv vL n i last B root child other aR aC) _ _ hreadR huR
  have hchild2 : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other a aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _
      (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hv2 : envLookup
      (mkHeapEnv vL n i last B root child other a aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hreadC := evalExpr_stdVecAt_some _ _ _ _ _ _ hv2 hchild2 hgc
  have huC : envUpdate
      (mkHeapEnv vL n i last B root child other a aC) "aC"
      (.i32 b) =
      some (mkHeapEnv vL n i last B root child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignC := evalStmtFuel_assign F "aC"
    (.stdVecAt "v" (.var "child"))
    (mkHeapEnv vL n i last B root child other a aC) _ _ hreadC huC
  have haR : evalExpr (.var "aR")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.i32 a) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aR _ _ _ _ _ _ _ _ _ _)
  have haC : evalExpr (.var "aC")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.i32 b) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aC _ _ _ _ _ _ _ _ _ _)
  have hcond := evalExpr_slt_i32 _ _ _ _ _ haR haC
  rw [hlt] at hcond
  have hbrk : evalStmtFuel F .break_
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (mkHeapEnv vL n i last B root child other a b,
        .broke) := by
    cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
  rw [hbody]
  exact ((evalStmtFuel_seq_fallthrough F _ _ _ _ hassignR).trans
    ((evalStmtFuel_seq_fallthrough F _ _ _ _ hassignC).trans
      ((evalStmtFuel_if_false F _ _ _ _ hcond).trans hbrk)))

/-- Swap misses on the root read. -/
theorem siftSwap_errR (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (hgr : vL[root.toNat]? = none) :
    evalStmtFuel F siftSwap
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB := by
  have hbody : siftSwap =
      (.seq (.assign "aR" (.stdVecAt "v" (.var "root")))
      (.seq (.assign "aC" (.stdVecAt "v" (.var "child")))
      (.if_ (.slt (.var "aR") (.var "aC"))
        (.seq (.vecSet "v" (.var "root") (.var "aC"))
          (.seq (.vecSet "v" (.var "child") (.var "aR"))
            (.assign "root" (.var "child"))))
        .break_))) := rfl
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hroot : evalExpr (.var "root")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 root) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_root _ _ _ _ _ _ _ _ _ _)
  have herr : evalExpr (.stdVecAt "v" (.var "root"))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB :=
    evalExpr_stdVecAt_oob _ _ _ _ _ hv hroot hgr
  have herrS : evalStmtFuel F
      (.assign "aR" (.stdVecAt "v" (.var "root")))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB := by
    cases F <;> simp only [evalStmtFuel, evalStmtZero, evalStmtWith, herr]
  rw [hbody]
  exact evalStmtFuel_seq_err F _ _ _ _ herrS

/-- Swap misses on the child read (root read fine). -/
theorem siftSwap_errC (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (a : BitVec 32)
    (hgr : vL[root.toNat]? = some a)
    (hgc : vL[child.toNat]? = none) :
    evalStmtFuel F siftSwap
      (mkHeapEnv vL n i last B root child other aR aC) =
      .error .OOB := by
  have hbody : siftSwap =
      (.seq (.assign "aR" (.stdVecAt "v" (.var "root")))
      (.seq (.assign "aC" (.stdVecAt "v" (.var "child")))
      (.if_ (.slt (.var "aR") (.var "aC"))
        (.seq (.vecSet "v" (.var "root") (.var "aC"))
          (.seq (.vecSet "v" (.var "child") (.var "aR"))
            (.assign "root" (.var "child"))))
        .break_))) := rfl
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hroot : evalExpr (.var "root")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 root) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_root _ _ _ _ _ _ _ _ _ _)
  have hreadR := evalExpr_stdVecAt_some _ _ _ _ _ _ hv hroot hgr
  have huR : envUpdate
      (mkHeapEnv vL n i last B root child other aR aC) "aR"
      (.i32 a) =
      some (mkHeapEnv vL n i last B root child other a aC) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignR := evalStmtFuel_assign F "aR"
    (.stdVecAt "v" (.var "root"))
    (mkHeapEnv vL n i last B root child other aR aC) _ _ hreadR huR
  have hchild : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other a aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hv2 : envLookup
      (mkHeapEnv vL n i last B root child other a aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have herr : evalExpr (.stdVecAt "v" (.var "child"))
      (mkHeapEnv vL n i last B root child other a aC) =
      .error .OOB :=
    evalExpr_stdVecAt_oob _ _ _ _ _ hv2 hchild hgc
  have herrS : evalStmtFuel F
      (.assign "aC" (.stdVecAt "v" (.var "child")))
      (mkHeapEnv vL n i last B root child other a aC) =
      .error .OOB := by
    cases F <;> simp only [evalStmtFuel, evalStmtZero, evalStmtWith, herr]
  rw [hbody]
  have hseq : evalStmtFuel F
      (.seq (.assign "aC" (.stdVecAt "v" (.var "child")))
        (.if_ (.slt (.var "aR") (.var "aC"))
          (.seq (.vecSet "v" (.var "root") (.var "aC"))
            (.seq (.vecSet "v" (.var "child") (.var "aR"))
              (.assign "root" (.var "child"))))
          .break_))
      (mkHeapEnv vL n i last B root child other a aC) =
      .error .OOB :=
    evalStmtFuel_seq_err F _ _ _ _ herrS
  exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hassignR).trans hseq

/-- Swap taken on aliased indices (`root = child`, the wraparound
    corner): both stores hit the same cell, the net effect is
    `v[root] := a` with the cursor unmoved. -/
theorem siftSwap_swap_alias (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (a b : BitVec 32)
    (hgr : vL[root.toNat]? = some a)
    (hgc : vL[child.toNat]? = some b)
    (hal : root.toNat = child.toNat)
    (hlt : a.slt b = true) :
    evalStmtFuel F siftSwap
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (mkHeapEnv ((vL.set root.toNat b).set child.toNat a)
        n i last B child child other a b, .fellThrough) := by
  have hbody : siftSwap =
      (.seq (.assign "aR" (.stdVecAt "v" (.var "root")))
      (.seq (.assign "aC" (.stdVecAt "v" (.var "child")))
      (.if_ (.slt (.var "aR") (.var "aC"))
        (.seq (.vecSet "v" (.var "root") (.var "aC"))
          (.seq (.vecSet "v" (.var "child") (.var "aR"))
            (.assign "root" (.var "child"))))
        .break_))) := rfl
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hroot : evalExpr (.var "root")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 root) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_root _ _ _ _ _ _ _ _ _ _)
  have hchild : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hreadR := evalExpr_stdVecAt_some _ _ _ _ _ _ hv hroot hgr
  have huR : envUpdate
      (mkHeapEnv vL n i last B root child other aR aC) "aR"
      (.i32 a) =
      some (mkHeapEnv vL n i last B root child other a aC) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignR := evalStmtFuel_assign F "aR"
    (.stdVecAt "v" (.var "root"))
    (mkHeapEnv vL n i last B root child other aR aC) _ _ hreadR huR
  have hchild2 : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other a aC) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _
      (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hv2 : envLookup
      (mkHeapEnv vL n i last B root child other a aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hreadC := evalExpr_stdVecAt_some _ _ _ _ _ _ hv2 hchild2 hgc
  have huC : envUpdate
      (mkHeapEnv vL n i last B root child other a aC) "aC"
      (.i32 b) =
      some (mkHeapEnv vL n i last B root child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignC := evalStmtFuel_assign F "aC"
    (.stdVecAt "v" (.var "child"))
    (mkHeapEnv vL n i last B root child other a aC) _ _ hreadC huC
  have haR : evalExpr (.var "aR")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.i32 a) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aR _ _ _ _ _ _ _ _ _ _)
  have haC : evalExpr (.var "aC")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.i32 b) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aC _ _ _ _ _ _ _ _ _ _)
  have hcond := evalExpr_slt_i32 _ _ _ _ _ haR haC
  rw [hlt] at hcond
  have hroot2 : evalExpr (.var "root")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.u64 root) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_root _ _ _ _ _ _ _ _ _ _)
  have hchild3 : evalExpr (.var "child")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hv3 : envLookup
      (mkHeapEnv vL n i last B root child other a b) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have huRw : envUpdate
      (mkHeapEnv vL n i last B root child other a b) "v"
      (.stdVecVal (vL.set root.toNat b)) =
      some (mkHeapEnv (vL.set root.toNat b) n i last B root child
        other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hsetR := evalStmtFuel_vecSet F "v" (.var "root") (.var "aC")
    (mkHeapEnv vL n i last B root child other a b)
    root b vL a _ hroot2 haC hv3 hgr huRw
  have hchild4 : evalExpr (.var "child")
      (mkHeapEnv (vL.set root.toNat b) n i last B root child other
        a b) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have haR2 : evalExpr (.var "aR")
      (mkHeapEnv (vL.set root.toNat b) n i last B root child other
        a b) =
      .ok (.i32 a) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aR _ _ _ _ _ _ _ _ _ _)
  have hv4 : envLookup
      (mkHeapEnv (vL.set root.toNat b) n i last B root child other
        a b) "v" =
      some (.stdVecVal (vL.set root.toNat b)) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hltRoot : root.toNat < vL.length :=
    (List.getElem?_eq_some_iff.mp hgr).1
  have hget2 : ((vL.set root.toNat b)[child.toNat]? = some b) := by
    rw [← hal]
    exact List.getElem?_set_self hltRoot
  have huCw : envUpdate
      (mkHeapEnv (vL.set root.toNat b) n i last B root child other
        a b) "v"
      (.stdVecVal ((vL.set root.toNat b).set child.toNat a)) =
      some (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n i
        last B root child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hsetC := evalStmtFuel_vecSet F "v" (.var "child") (.var "aR")
    (mkHeapEnv (vL.set root.toNat b) n i last B root child other
      a b)
    child a (vL.set root.toNat b) b _
    hchild4 haR2 hv4 hget2 huCw
  have hchild5 : evalExpr (.var "child")
      (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n i last
        B root child other a b) =
      .ok (.u64 child) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
  have hrootEq : root = child := BitVec.eq_of_toNat_eq hal
  have huRt : envUpdate
      (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n i last
        B root child other a b) "root" (.u64 child) =
      some (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n i
        last B child child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate, hrootEq]
  have hassignRt := evalStmtFuel_assign F "root" (.var "child")
    (mkHeapEnv ((vL.set root.toNat b).set child.toNat a) n i last
      B root child other a b) _ _ hchild5 huRt
  rw [hbody]
  exact ((evalStmtFuel_seq_fallthrough F _ _ _ _ hassignR).trans
    ((evalStmtFuel_seq_fallthrough F _ _ _ _ hassignC).trans
      ((evalStmtFuel_if_true F _ _ _ _ hcond).trans
        (((evalStmtFuel_seq_fallthrough F _ _ _ _ hsetR).trans
          ((evalStmtFuel_seq_fallthrough F _ _ _ _ hsetC).trans
            hassignRt))))))

/-! ## Sift loop agreement (ok direction) -/

/-- The sift loop agrees with the forward on success: fuel-indexed
    induction, one unfolded iteration per case. -/
theorem siftLoop_ok (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (v' : List (BitVec 32))
    (hok : siftFwd F vL B root = .ok v') :
    ∃ root' child' other' aR' aC',
      evalStmtFuel F heapSift
        (mkHeapEnv vL n i last B root child other aR aC) =
        .ok (mkHeapEnv v' n i last B root' child' other' aR' aC',
          .fellThrough) := by
  induction F generalizing vL root child other aR aC with
  | zero => simp [siftFwd] at hok
  | succ F IH =>
    simp only [siftFwd] at hok
    have htrue : evalExpr (.lit (.b true))
        (mkHeapEnv vL n i last B root child other aR aC) =
        .ok (.b true) := rfl
    by_cases hcb : (root*2+1).ult B = true
    · -- bound holds: run one iteration, then recurse
      have hidx :=
        siftIdx_ok F vL n i last B root child other aR aC
      by_cases hob : (root*2+1+1).ult B = true
      · match hgo : vL[(root*2+1+1).toNat]? with
        | some wo =>
          match hgc : vL[(root*2+1).toNat]? with
          | some wc =>
            by_cases hlt : wc.slt wo = true
            · -- pick taken: cand = other
              have hpick := siftPick_take F vL n i last B
                root (root*2+1) (root*2+1+1) aR aC wo wc hob hgo
                hgc hlt
              match hgr : vL[root.toNat]? with
              | some a =>
                match hgc2 : vL[(root*2+1+1).toNat]? with
                | some b =>
                  -- same index as `hgo`: the cand read value is `wo`
                  have hbw : b = wo := by
                    simpa using hgc2.symm.trans hgo
                  by_cases hlt2 : a.slt b = true
                  · by_cases heq : root.toNat = (root*2+1+1).toNat
                    · -- aliased descend: same-cell double store
                      have hswap := siftSwap_swap_alias F vL n i
                        last B root (root*2+1+1) (root*2+1+1) aR aC
                        a b hgr hgc2 heq hlt2
                      have hcb' : evalExpr
                          (.ult (.var "child") (.var "B"))
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (.b true) := by
                        have hc : evalExpr (.var "child")
                            (mkHeapEnv vL n i last B root (root*2+1)
                              (root*2+1+1) aR aC) =
                            .ok (.u64 (root*2+1)) :=
                          evalExpr_var_hit _ _ _
                            (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
                        have hB : evalExpr (.var "B")
                            (mkHeapEnv vL n i last B root (root*2+1)
                              (root*2+1+1) aR aC) =
                            .ok (.u64 B) :=
                          evalExpr_var_hit _ _ _
                            (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
                        have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
                        rw [hcb] at h
                        exact h
                      have hbody : evalStmtFuel F heapSiftBody
                          (mkHeapEnv vL n i last B root child other
                            aR aC) =
                          .ok (mkHeapEnv ((vL.set root.toNat b).set
                            (root*2+1+1).toNat a) n i last B
                            (root*2+1+1) (root*2+1+1)
                            (root*2+1+1) a b, .fellThrough) := by
                        have hseq : evalStmtFuel F
                            (.seq siftPick siftSwap)
                            (mkHeapEnv vL n i last B root (root*2+1)
                              (root*2+1+1) aR aC) =
                            .ok (mkHeapEnv ((vL.set root.toNat b).set
                              (root*2+1+1).toNat a) n i last B
                              (root*2+1+1) (root*2+1+1)
                              (root*2+1+1) a b, .fellThrough) :=
                          (evalStmtFuel_seq_fallthrough F _ _ _ _
                            hpick).trans hswap
                        have hif : evalStmtFuel F
                            (.if_ (.ult (.var "child") (.var "B"))
                              (.seq siftPick siftSwap) .break_)
                            (mkHeapEnv vL n i last B root (root*2+1)
                              (root*2+1+1) aR aC) =
                            .ok (mkHeapEnv ((vL.set root.toNat b).set
                              (root*2+1+1).toNat a) n i last B
                              (root*2+1+1) (root*2+1+1)
                              (root*2+1+1) a b, .fellThrough) :=
                          (evalStmtFuel_if_true F _ _ _ _ hcb').trans
                            hseq
                        have hunfold : heapSiftBody =
                            .seq siftIdx
                              (.if_ (.ult (.var "child") (.var "B"))
                                (.seq siftPick siftSwap)
                                .break_) := rfl
                        rw [hunfold]
                        exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                          hidx).trans hif
                      have hstep : evalStmtFuel (F+1) heapSift
                          (mkHeapEnv vL n i last B root child other
                            aR aC) =
                          evalStmtFuel F heapSift
                            (mkHeapEnv ((vL.set root.toNat b).set
                              (root*2+1+1).toNat a) n i last B
                              (root*2+1+1) (root*2+1+1)
                              (root*2+1+1) a b) := by
                        simp [heapSift, evalStmtFuel,
                          evalStmtSuccHandler, evalStmtWith, htrue,
                          hbody]
                      rw [hstep]
                      simp only [hcb, hob, hgo, hgc, hlt, hgr,
                        ite_true] at hok
                      rw [←hbw] at hok
                      simp only [hlt2, ite_true] at hok
                      exact IH _ _ _ _ _ _ hok
                    · -- unaliased descend
                      have hne : root.toNat ≠ (root*2+1+1).toNat :=
                        heq
                      have hswap := siftSwap_swap F vL n i last B
                        root (root*2+1+1) (root*2+1+1) aR aC a b
                        hgr hgc2 hne hlt2
                      have hcb' : evalExpr
                          (.ult (.var "child") (.var "B"))
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (.b true) := by
                        have hc : evalExpr (.var "child")
                            (mkHeapEnv vL n i last B root (root*2+1)
                              (root*2+1+1) aR aC) =
                            .ok (.u64 (root*2+1)) :=
                          evalExpr_var_hit _ _ _
                            (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
                        have hB : evalExpr (.var "B")
                            (mkHeapEnv vL n i last B root (root*2+1)
                              (root*2+1+1) aR aC) =
                            .ok (.u64 B) :=
                          evalExpr_var_hit _ _ _
                            (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
                        have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
                        rw [hcb] at h
                        exact h
                      have hbody : evalStmtFuel F heapSiftBody
                          (mkHeapEnv vL n i last B root child other
                            aR aC) =
                          .ok (mkHeapEnv ((vL.set root.toNat b).set
                            (root*2+1+1).toNat a) n i last B
                            (root*2+1+1) (root*2+1+1)
                            (root*2+1+1) a b, .fellThrough) := by
                        have hseq : evalStmtFuel F
                            (.seq siftPick siftSwap)
                            (mkHeapEnv vL n i last B root (root*2+1)
                              (root*2+1+1) aR aC) =
                            .ok (mkHeapEnv ((vL.set root.toNat b).set
                              (root*2+1+1).toNat a) n i last B
                              (root*2+1+1) (root*2+1+1)
                              (root*2+1+1) a b, .fellThrough) :=
                          (evalStmtFuel_seq_fallthrough F _ _ _ _
                            hpick).trans hswap
                        have hif : evalStmtFuel F
                            (.if_ (.ult (.var "child") (.var "B"))
                              (.seq siftPick siftSwap) .break_)
                            (mkHeapEnv vL n i last B root (root*2+1)
                              (root*2+1+1) aR aC) =
                            .ok (mkHeapEnv ((vL.set root.toNat b).set
                              (root*2+1+1).toNat a) n i last B
                              (root*2+1+1) (root*2+1+1)
                              (root*2+1+1) a b, .fellThrough) :=
                          (evalStmtFuel_if_true F _ _ _ _ hcb').trans
                            hseq
                        have hunfold : heapSiftBody =
                            .seq siftIdx
                              (.if_ (.ult (.var "child") (.var "B"))
                                (.seq siftPick siftSwap)
                                .break_) := rfl
                        rw [hunfold]
                        exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                          hidx).trans hif
                      have hstep : evalStmtFuel (F+1) heapSift
                          (mkHeapEnv vL n i last B root child other
                            aR aC) =
                          evalStmtFuel F heapSift
                            (mkHeapEnv ((vL.set root.toNat b).set
                              (root*2+1+1).toNat a) n i last B
                              (root*2+1+1) (root*2+1+1)
                              (root*2+1+1) a b) := by
                        simp [heapSift, evalStmtFuel,
                          evalStmtSuccHandler, evalStmtWith, htrue,
                          hbody]
                      rw [hstep]
                      simp only [hcb, hob, hgo, hgc, hlt, hgr,
                        ite_true] at hok
                      rw [←hbw] at hok
                      simp only [hlt2, ite_true] at hok
                      exact IH _ _ _ _ _ _ hok
                  · -- no swap: one broke iteration, exit
                    have hltF : a.slt b = false :=
                      Bool.eq_false_of_ne_true hlt2
                    have hswap := siftSwap_break F vL n i last B
                      root (root*2+1+1) (root*2+1+1) aR aC a b hgr
                      hgc2 hltF
                    have hcb' : evalExpr
                        (.ult (.var "child") (.var "B"))
                        (mkHeapEnv vL n i last B root (root*2+1)
                          (root*2+1+1) aR aC) =
                        .ok (.b true) := by
                      have hc : evalExpr (.var "child")
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (.u64 (root*2+1)) :=
                        evalExpr_var_hit _ _ _
                          (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
                      have hB : evalExpr (.var "B")
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (.u64 B) :=
                        evalExpr_var_hit _ _ _
                          (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
                      have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
                      rw [hcb] at h
                      exact h
                    have hbody : evalStmtFuel F heapSiftBody
                        (mkHeapEnv vL n i last B root child other
                          aR aC) =
                        .ok (mkHeapEnv vL n i last B root
                          (root*2+1+1) (root*2+1+1) a b, .broke) := by
                      have hseq : evalStmtFuel F
                          (.seq siftPick siftSwap)
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (mkHeapEnv vL n i last B root
                            (root*2+1+1) (root*2+1+1) a b,
                            .broke) :=
                        (evalStmtFuel_seq_fallthrough F _ _ _ _
                          hpick).trans hswap
                      have hif : evalStmtFuel F
                          (.if_ (.ult (.var "child") (.var "B"))
                            (.seq siftPick siftSwap) .break_)
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (mkHeapEnv vL n i last B root
                            (root*2+1+1) (root*2+1+1) a b,
                            .broke) :=
                        (evalStmtFuel_if_true F _ _ _ _ hcb').trans
                          hseq
                      have hunfold : heapSiftBody =
                          .seq siftIdx
                            (.if_ (.ult (.var "child") (.var "B"))
                              (.seq siftPick siftSwap)
                              .break_) := rfl
                      rw [hunfold]
                      exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                        hidx).trans hif
                    have hstep : evalStmtFuel (F+1) heapSift
                        (mkHeapEnv vL n i last B root child other
                          aR aC) =
                        .ok (mkHeapEnv vL n i last B root
                          (root*2+1+1) (root*2+1+1) a b,
                          .fellThrough) := by
                      simp [heapSift, evalStmtFuel,
                        evalStmtSuccHandler, evalStmtWith, htrue,
                        hbody]
                    simp only [hcb, hob, hgo, hgc, hlt, hgr,
                      ite_true] at hok
                    rw [←hbw] at hok
                    simp only [hlt2] at hok
                    have hv : vL = v' := by simpa using hok
                    subst hv
                    exact ⟨root, (root*2+1+1), (root*2+1+1), a, b,
                      hstep⟩
                | none =>
                  -- same index as `hgo`: the reads contradict
                  rw [hgc2] at hgo
                  simp at hgo
              | none =>
                simp only [hcb, hob, hgo, hgc, hlt, hgr, ite_true] at hok
                simp at hok
            · -- pick skipped (child holds the larger word): cand = child
              have hltF : wc.slt wo = false :=
                Bool.eq_false_of_ne_true hlt
              have hpick := siftPick_skipC F vL n i last B
                root (root*2+1) (root*2+1+1) aR aC wo wc hob hgo
                hgc hltF
              match hgr : vL[root.toNat]? with
              | some a =>
                by_cases hlt2 : a.slt wc = true
                · by_cases heq : root.toNat = (root*2+1).toNat
                  · -- aliased descend: same-cell double store
                    have hswap := siftSwap_swap_alias F vL n i
                      last B root (root*2+1) (root*2+1+1) aR aC
                      a wc hgr hgc heq hlt2
                    have hcb' : evalExpr
                        (.ult (.var "child") (.var "B"))
                        (mkHeapEnv vL n i last B root (root*2+1)
                          (root*2+1+1) aR aC) =
                        .ok (.b true) := by
                      have hc : evalExpr (.var "child")
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (.u64 (root*2+1)) :=
                        evalExpr_var_hit _ _ _
                          (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
                      have hB : evalExpr (.var "B")
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (.u64 B) :=
                        evalExpr_var_hit _ _ _
                          (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
                      have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
                      rw [hcb] at h
                      exact h
                    have hbody : evalStmtFuel F heapSiftBody
                        (mkHeapEnv vL n i last B root child other
                          aR aC) =
                        .ok (mkHeapEnv ((vL.set root.toNat wc).set
                          (root*2+1).toNat a) n i last B
                          (root*2+1) (root*2+1) (root*2+1+1) a wc,
                          .fellThrough) := by
                      have hseq : evalStmtFuel F
                          (.seq siftPick siftSwap)
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (mkHeapEnv ((vL.set root.toNat wc).set
                            (root*2+1).toNat a) n i last B
                            (root*2+1) (root*2+1) (root*2+1+1) a wc,
                            .fellThrough) :=
                        (evalStmtFuel_seq_fallthrough F _ _ _ _
                          hpick).trans hswap
                      have hif : evalStmtFuel F
                          (.if_ (.ult (.var "child") (.var "B"))
                            (.seq siftPick siftSwap) .break_)
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (mkHeapEnv ((vL.set root.toNat wc).set
                            (root*2+1).toNat a) n i last B
                            (root*2+1) (root*2+1) (root*2+1+1) a wc,
                            .fellThrough) :=
                        (evalStmtFuel_if_true F _ _ _ _ hcb').trans
                          hseq
                      have hunfold : heapSiftBody =
                          .seq siftIdx
                            (.if_ (.ult (.var "child") (.var "B"))
                              (.seq siftPick siftSwap)
                              .break_) := rfl
                      rw [hunfold]
                      exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                        hidx).trans hif
                    have hstep : evalStmtFuel (F+1) heapSift
                        (mkHeapEnv vL n i last B root child other
                          aR aC) =
                        evalStmtFuel F heapSift
                          (mkHeapEnv ((vL.set root.toNat wc).set
                            (root*2+1).toNat a) n i last B
                            (root*2+1) (root*2+1) (root*2+1+1) a
                            wc) := by
                      simp [heapSift, evalStmtFuel,
                        evalStmtSuccHandler, evalStmtWith, htrue,
                        hbody]
                    rw [hstep]
                    simp only [hcb, hob, hgo, hgc, hltF, hgr, hlt2,
                      Bool.false_eq_true, ite_true, ite_false] at hok
                    exact IH _ _ _ _ _ _ hok
                  · -- unaliased descend
                    have hne : root.toNat ≠ (root*2+1).toNat :=
                      heq
                    have hswap := siftSwap_swap F vL n i last B
                      root (root*2+1) (root*2+1+1) aR aC a wc
                      hgr hgc hne hlt2
                    have hcb' : evalExpr
                        (.ult (.var "child") (.var "B"))
                        (mkHeapEnv vL n i last B root (root*2+1)
                          (root*2+1+1) aR aC) =
                        .ok (.b true) := by
                      have hc : evalExpr (.var "child")
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (.u64 (root*2+1)) :=
                        evalExpr_var_hit _ _ _
                          (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
                      have hB : evalExpr (.var "B")
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (.u64 B) :=
                        evalExpr_var_hit _ _ _
                          (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
                      have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
                      rw [hcb] at h
                      exact h
                    have hbody : evalStmtFuel F heapSiftBody
                        (mkHeapEnv vL n i last B root child other
                          aR aC) =
                        .ok (mkHeapEnv ((vL.set root.toNat wc).set
                          (root*2+1).toNat a) n i last B
                          (root*2+1) (root*2+1) (root*2+1+1) a wc,
                          .fellThrough) := by
                      have hseq : evalStmtFuel F
                          (.seq siftPick siftSwap)
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (mkHeapEnv ((vL.set root.toNat wc).set
                            (root*2+1).toNat a) n i last B
                            (root*2+1) (root*2+1) (root*2+1+1) a wc,
                            .fellThrough) :=
                        (evalStmtFuel_seq_fallthrough F _ _ _ _
                          hpick).trans hswap
                      have hif : evalStmtFuel F
                          (.if_ (.ult (.var "child") (.var "B"))
                            (.seq siftPick siftSwap) .break_)
                          (mkHeapEnv vL n i last B root (root*2+1)
                            (root*2+1+1) aR aC) =
                          .ok (mkHeapEnv ((vL.set root.toNat wc).set
                            (root*2+1).toNat a) n i last B
                            (root*2+1) (root*2+1) (root*2+1+1) a wc,
                            .fellThrough) :=
                        (evalStmtFuel_if_true F _ _ _ _ hcb').trans
                          hseq
                      have hunfold : heapSiftBody =
                          .seq siftIdx
                            (.if_ (.ult (.var "child") (.var "B"))
                              (.seq siftPick siftSwap)
                              .break_) := rfl
                      rw [hunfold]
                      exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                        hidx).trans hif
                    have hstep : evalStmtFuel (F+1) heapSift
                        (mkHeapEnv vL n i last B root child other
                          aR aC) =
                        evalStmtFuel F heapSift
                          (mkHeapEnv ((vL.set root.toNat wc).set
                            (root*2+1).toNat a) n i last B
                            (root*2+1) (root*2+1) (root*2+1+1) a
                            wc) := by
                      simp [heapSift, evalStmtFuel,
                        evalStmtSuccHandler, evalStmtWith, htrue,
                        hbody]
                    rw [hstep]
                    simp only [hcb, hob, hgo, hgc, hltF, hgr, hlt2,
                      Bool.false_eq_true, ite_true, ite_false] at hok
                    exact IH _ _ _ _ _ _ hok
                · -- no swap: one broke iteration, exit
                  have hltF2 : a.slt wc = false :=
                    Bool.eq_false_of_ne_true hlt2
                  have hswap := siftSwap_break F vL n i last B
                    root (root*2+1) (root*2+1+1) aR aC a wc hgr
                    hgc hltF2
                  have hcb' : evalExpr
                      (.ult (.var "child") (.var "B"))
                      (mkHeapEnv vL n i last B root (root*2+1)
                        (root*2+1+1) aR aC) =
                      .ok (.b true) := by
                    have hc : evalExpr (.var "child")
                        (mkHeapEnv vL n i last B root (root*2+1)
                          (root*2+1+1) aR aC) =
                          .ok (.u64 (root*2+1)) :=
                      evalExpr_var_hit _ _ _
                        (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
                    have hB : evalExpr (.var "B")
                        (mkHeapEnv vL n i last B root (root*2+1)
                          (root*2+1+1) aR aC) =
                        .ok (.u64 B) :=
                      evalExpr_var_hit _ _ _
                        (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
                    have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
                    rw [hcb] at h
                    exact h
                  have hbody : evalStmtFuel F heapSiftBody
                      (mkHeapEnv vL n i last B root child other
                        aR aC) =
                      .ok (mkHeapEnv vL n i last B root
                        (root*2+1) (root*2+1+1) a wc, .broke) := by
                    have hseq : evalStmtFuel F
                        (.seq siftPick siftSwap)
                        (mkHeapEnv vL n i last B root (root*2+1)
                          (root*2+1+1) aR aC) =
                        .ok (mkHeapEnv vL n i last B root
                          (root*2+1) (root*2+1+1) a wc,
                          .broke) :=
                      (evalStmtFuel_seq_fallthrough F _ _ _ _
                        hpick).trans hswap
                    have hif : evalStmtFuel F
                        (.if_ (.ult (.var "child") (.var "B"))
                          (.seq siftPick siftSwap) .break_)
                        (mkHeapEnv vL n i last B root (root*2+1)
                          (root*2+1+1) aR aC) =
                        .ok (mkHeapEnv vL n i last B root
                          (root*2+1) (root*2+1+1) a wc,
                          .broke) :=
                      (evalStmtFuel_if_true F _ _ _ _ hcb').trans
                        hseq
                    have hunfold : heapSiftBody =
                        .seq siftIdx
                          (.if_ (.ult (.var "child") (.var "B"))
                            (.seq siftPick siftSwap)
                            .break_) := rfl
                    rw [hunfold]
                    exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                      hidx).trans hif
                  have hstep : evalStmtFuel (F+1) heapSift
                      (mkHeapEnv vL n i last B root child other
                        aR aC) =
                      .ok (mkHeapEnv vL n i last B root
                        (root*2+1) (root*2+1+1) a wc,
                        .fellThrough) := by
                    simp [heapSift, evalStmtFuel,
                      evalStmtSuccHandler, evalStmtWith, htrue,
                      hbody]
                  simp only [hcb, hob, hgo, hgc, hltF, hgr, hlt2,
                    Bool.false_eq_true, ite_true, ite_false] at hok
                  have hv : vL = v' := by simpa using hok
                  subst hv
                  exact ⟨root, (root*2+1), (root*2+1+1), a, wc,
                    hstep⟩
              | none =>
                simp only [hcb, hob, hgo, hgc, hltF, hgr, ite_true,
                  ite_false] at hok
                simp at hok
          | none =>
            simp only [hcb, hob, hgo, hgc, ite_true] at hok
            simp at hok
        | none =>
          simp only [hcb, hob, hgo, ite_true] at hok
          simp at hok
      · -- pick skipped (other out of bound): cand = child
        -- the skip path never reads `other`: match only root/child
        have hoF : (root*2+1+1).ult B = false :=
          Bool.eq_false_of_ne_true hob
        have hpick := siftPick_skipO F vL n i last B
          root (root*2+1) (root*2+1+1) aR aC hoF
        match hgr : vL[root.toNat]?, hgc : vL[(root*2+1).toNat]? with
        | some a, some wc =>
          by_cases hlt2 : a.slt wc = true
          · by_cases heq : root.toNat = (root*2+1).toNat
            · -- aliased descend: same-cell double store
              have hswap := siftSwap_swap_alias F vL n i
                last B root (root*2+1) (root*2+1+1) aR aC
                a wc hgr hgc heq hlt2
              have hcb' : evalExpr
                  (.ult (.var "child") (.var "B"))
                  (mkHeapEnv vL n i last B root (root*2+1)
                    (root*2+1+1) aR aC) =
                  .ok (.b true) := by
                have hc : evalExpr (.var "child")
                    (mkHeapEnv vL n i last B root (root*2+1)
                      (root*2+1+1) aR aC) =
                    .ok (.u64 (root*2+1)) :=
                  evalExpr_var_hit _ _ _
                    (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
                have hB : evalExpr (.var "B")
                    (mkHeapEnv vL n i last B root (root*2+1)
                      (root*2+1+1) aR aC) =
                    .ok (.u64 B) :=
                  evalExpr_var_hit _ _ _
                    (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
                have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
                rw [hcb] at h
                exact h
              have hbody : evalStmtFuel F heapSiftBody
                  (mkHeapEnv vL n i last B root child other
                    aR aC) =
                  .ok (mkHeapEnv ((vL.set root.toNat wc).set
                    (root*2+1).toNat a) n i last B
                    (root*2+1) (root*2+1) (root*2+1+1) a wc,
                    .fellThrough) := by
                have hseq : evalStmtFuel F
                    (.seq siftPick siftSwap)
                    (mkHeapEnv vL n i last B root (root*2+1)
                      (root*2+1+1) aR aC) =
                    .ok (mkHeapEnv ((vL.set root.toNat wc).set
                      (root*2+1).toNat a) n i last B
                      (root*2+1) (root*2+1) (root*2+1+1) a wc,
                      .fellThrough) :=
                  (evalStmtFuel_seq_fallthrough F _ _ _ _
                    hpick).trans hswap
                have hif : evalStmtFuel F
                    (.if_ (.ult (.var "child") (.var "B"))
                      (.seq siftPick siftSwap) .break_)
                    (mkHeapEnv vL n i last B root (root*2+1)
                      (root*2+1+1) aR aC) =
                    .ok (mkHeapEnv ((vL.set root.toNat wc).set
                      (root*2+1).toNat a) n i last B
                      (root*2+1) (root*2+1) (root*2+1+1) a wc,
                      .fellThrough) :=
                  (evalStmtFuel_if_true F _ _ _ _ hcb').trans
                    hseq
                have hunfold : heapSiftBody =
                    .seq siftIdx
                      (.if_ (.ult (.var "child") (.var "B"))
                        (.seq siftPick siftSwap)
                        .break_) := rfl
                rw [hunfold]
                exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                  hidx).trans hif
              have hstep : evalStmtFuel (F+1) heapSift
                  (mkHeapEnv vL n i last B root child other
                    aR aC) =
                  evalStmtFuel F heapSift
                    (mkHeapEnv ((vL.set root.toNat wc).set
                      (root*2+1).toNat a) n i last B
                      (root*2+1) (root*2+1) (root*2+1+1) a
                      wc) := by
                simp [heapSift, evalStmtFuel,
                  evalStmtSuccHandler, evalStmtWith, htrue,
                  hbody]
              rw [hstep]
              simp only [hcb, hob, hgc, hgr, hlt2,
                ite_true] at hok
              exact IH _ _ _ _ _ _ hok
            · -- unaliased descend
              have hne : root.toNat ≠ (root*2+1).toNat :=
                heq
              have hswap := siftSwap_swap F vL n i last B
                root (root*2+1) (root*2+1+1) aR aC a wc
                hgr hgc hne hlt2
              have hcb' : evalExpr
                  (.ult (.var "child") (.var "B"))
                  (mkHeapEnv vL n i last B root (root*2+1)
                    (root*2+1+1) aR aC) =
                  .ok (.b true) := by
                have hc : evalExpr (.var "child")
                    (mkHeapEnv vL n i last B root (root*2+1)
                      (root*2+1+1) aR aC) =
                      .ok (.u64 (root*2+1)) :=
                  evalExpr_var_hit _ _ _
                    (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
                have hB : evalExpr (.var "B")
                    (mkHeapEnv vL n i last B root (root*2+1)
                      (root*2+1+1) aR aC) =
                    .ok (.u64 B) :=
                  evalExpr_var_hit _ _ _
                    (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
                have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
                rw [hcb] at h
                exact h
              have hbody : evalStmtFuel F heapSiftBody
                  (mkHeapEnv vL n i last B root child other
                    aR aC) =
                  .ok (mkHeapEnv ((vL.set root.toNat wc).set
                    (root*2+1).toNat a) n i last B
                    (root*2+1) (root*2+1) (root*2+1+1) a wc,
                    .fellThrough) := by
                have hseq : evalStmtFuel F
                    (.seq siftPick siftSwap)
                    (mkHeapEnv vL n i last B root (root*2+1)
                      (root*2+1+1) aR aC) =
                    .ok (mkHeapEnv ((vL.set root.toNat wc).set
                      (root*2+1).toNat a) n i last B
                      (root*2+1) (root*2+1) (root*2+1+1) a wc,
                      .fellThrough) :=
                  (evalStmtFuel_seq_fallthrough F _ _ _ _
                    hpick).trans hswap
                have hif : evalStmtFuel F
                    (.if_ (.ult (.var "child") (.var "B"))
                      (.seq siftPick siftSwap) .break_)
                    (mkHeapEnv vL n i last B root (root*2+1)
                      (root*2+1+1) aR aC) =
                    .ok (mkHeapEnv ((vL.set root.toNat wc).set
                      (root*2+1).toNat a) n i last B
                      (root*2+1) (root*2+1) (root*2+1+1) a wc,
                      .fellThrough) :=
                  (evalStmtFuel_if_true F _ _ _ _ hcb').trans
                    hseq
                have hunfold : heapSiftBody =
                    .seq siftIdx
                      (.if_ (.ult (.var "child") (.var "B"))
                        (.seq siftPick siftSwap)
                        .break_) := rfl
                rw [hunfold]
                exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                  hidx).trans hif
              have hstep : evalStmtFuel (F+1) heapSift
                  (mkHeapEnv vL n i last B root child other
                    aR aC) =
                  evalStmtFuel F heapSift
                    (mkHeapEnv ((vL.set root.toNat wc).set
                      (root*2+1).toNat a) n i last B
                      (root*2+1) (root*2+1) (root*2+1+1) a
                      wc) := by
                simp [heapSift, evalStmtFuel,
                  evalStmtSuccHandler, evalStmtWith, htrue,
                  hbody]
              rw [hstep]
              simp only [hcb, hob, hgc, hgr, hlt2,
                ite_true] at hok
              exact IH _ _ _ _ _ _ hok
          · -- no swap: one broke iteration, exit
            have hltF2 : a.slt wc = false :=
              Bool.eq_false_of_ne_true hlt2
            have hswap := siftSwap_break F vL n i last B
              root (root*2+1) (root*2+1+1) aR aC a wc hgr
              hgc hltF2
            have hcb' : evalExpr
                (.ult (.var "child") (.var "B"))
                (mkHeapEnv vL n i last B root (root*2+1)
                  (root*2+1+1) aR aC) =
                .ok (.b true) := by
              have hc : evalExpr (.var "child")
                  (mkHeapEnv vL n i last B root (root*2+1)
                    (root*2+1+1) aR aC) =
                    .ok (.u64 (root*2+1)) :=
                evalExpr_var_hit _ _ _
                  (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
              have hB : evalExpr (.var "B")
                  (mkHeapEnv vL n i last B root (root*2+1)
                    (root*2+1+1) aR aC) =
                  .ok (.u64 B) :=
                evalExpr_var_hit _ _ _
                  (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
              have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
              rw [hcb] at h
              exact h
            have hbody : evalStmtFuel F heapSiftBody
                (mkHeapEnv vL n i last B root child other
                  aR aC) =
                .ok (mkHeapEnv vL n i last B root
                  (root*2+1) (root*2+1+1) a wc, .broke) := by
              have hseq : evalStmtFuel F
                  (.seq siftPick siftSwap)
                  (mkHeapEnv vL n i last B root (root*2+1)
                    (root*2+1+1) aR aC) =
                  .ok (mkHeapEnv vL n i last B root
                    (root*2+1) (root*2+1+1) a wc,
                    .broke) :=
                (evalStmtFuel_seq_fallthrough F _ _ _ _
                  hpick).trans hswap
              have hif : evalStmtFuel F
                  (.if_ (.ult (.var "child") (.var "B"))
                    (.seq siftPick siftSwap) .break_)
                  (mkHeapEnv vL n i last B root (root*2+1)
                    (root*2+1+1) aR aC) =
                  .ok (mkHeapEnv vL n i last B root
                    (root*2+1) (root*2+1+1) a wc,
                    .broke) :=
                (evalStmtFuel_if_true F _ _ _ _ hcb').trans
                  hseq
              have hunfold : heapSiftBody =
                  .seq siftIdx
                    (.if_ (.ult (.var "child") (.var "B"))
                      (.seq siftPick siftSwap)
                      .break_) := rfl
              rw [hunfold]
              exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                hidx).trans hif
            have hstep : evalStmtFuel (F+1) heapSift
                (mkHeapEnv vL n i last B root child other
                  aR aC) =
                .ok (mkHeapEnv vL n i last B root
                  (root*2+1) (root*2+1+1) a wc,
                  .fellThrough) := by
              simp [heapSift, evalStmtFuel,
                evalStmtSuccHandler, evalStmtWith, htrue,
                hbody]
            simp only [hcb, hob, hgc, hgr, hlt2,
              ite_true] at hok
            have hv : vL = v' := by simpa using hok
            subst hv
            exact ⟨root, (root*2+1), (root*2+1+1), a, wc,
              hstep⟩
            | some a, none =>
              simp only [hcb, hob, hgc, hgr, ite_true] at hok
              simp at hok
            | none, some wc =>
              simp only [hcb, hob, hgr, ite_true] at hok
              simp at hok
            | none, none =>
              simp only [hcb, hob, hgr, ite_true] at hok
              simp at hok
    · -- bound fails on entry: one broke iteration, exit
      have hidx :=
        siftIdx_ok F vL n i last B root child other aR aC
      have hcbF : (root*2+1).ult B = false :=
        Bool.eq_false_of_ne_true hcb
      have hcb' : evalExpr (.ult (.var "child") (.var "B"))
          (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1) aR
            aC) =
          .ok (.b false) := by
        have hc : evalExpr (.var "child")
            (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1) aR
              aC) =
            .ok (.u64 (root*2+1)) :=
          evalExpr_var_hit _ _ _
            (mkHeapEnv_child _ _ _ _ _ _ _ _ _ _)
        have hB : evalExpr (.var "B")
            (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1) aR
              aC) =
            .ok (.u64 B) :=
          evalExpr_var_hit _ _ _ (mkHeapEnv_B _ _ _ _ _ _ _ _ _ _)
        have h := evalExpr_ult_u64 _ _ _ _ _ hc hB
        rw [hcbF] at h
        exact h
      have hbody : evalStmtFuel F heapSiftBody
          (mkHeapEnv vL n i last B root child other aR aC) =
          .ok (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1)
            aR aC, .broke) := by
        have hunfold : heapSiftBody =
            .seq siftIdx
              (.if_ (.ult (.var "child") (.var "B"))
                (.seq siftPick siftSwap) .break_) := rfl
        have hbrk := evalStmtFuel_break F
          (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1) aR aC)
        have hif : evalStmtFuel F
            (.if_ (.ult (.var "child") (.var "B"))
              (.seq siftPick siftSwap) .break_)
            (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1) aR
              aC) =
            .ok (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1)
              aR aC, .broke) :=
          (evalStmtFuel_if_false F _ _ _ _ hcb').trans hbrk
        rw [hunfold]
        exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hidx).trans hif
      have hstep : evalStmtFuel (F+1) heapSift
          (mkHeapEnv vL n i last B root child other aR aC) =
          .ok (mkHeapEnv vL n i last B root (root*2+1) (root*2+1+1)
            aR aC, .fellThrough) := by
        simp [heapSift, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          htrue, hbody]
      simp only [hcb] at hok
      have hv : vL = v' := by simpa using hok
      subst hv
      exact ⟨root, (root*2+1), (root*2+1+1), aR, aC, hstep⟩

/-! ## Heapify drain agreement (ok direction) -/

/-- The heapify countdown agrees with the forward on success: `i`
    ticks down first, then the freshly rooted sift runs and the
    loop recurses. The sift bound is pinned to `n` (heapify phase),
    so no arithmetic side conditions appear. -/
theorem heapDrain_ok (F : Nat) (vL : List (BitVec 32))
    (n i last root child other : BitVec 64) (aR aC : BitVec 32)
    (v' : List (BitVec 32))
    (hok : heapifyFwd F vL n i = .ok v') :
    ∃ root' child' other' aR' aC',
      evalStmtFuel F heapDrain
        (mkHeapEnv vL n i last n root child other aR aC) =
        .ok (mkHeapEnv v' n 0 last n root' child' other' aR' aC',
          .fellThrough) := by
  induction F generalizing vL i root child other aR aC with
  | zero =>
    by_cases h0 : i = 0
    · -- counter exhausted on entry: forward ok, loop exits
      subst h0
      have hiF : ((0 : BitVec 64) != 0) = false := by decide
      have hguard : evalExpr (.une (.var "i") (.lit (.u64 0)))
          (mkHeapEnv vL n 0 last n root child other aR aC) =
          .ok (.b false) := by
        have hiI : evalExpr (.var "i")
            (mkHeapEnv vL n 0 last n root child other aR aC) =
            .ok (.u64 0) :=
          evalExpr_var_hit _ _ _ (mkHeapEnv_i _ _ _ _ _ _ _ _ _ _)
        have hz : evalExpr (.lit (.u64 0))
            (mkHeapEnv vL n 0 last n root child other aR aC) =
            .ok (.u64 0) := rfl
        have h := evalExpr_une_u64 _ _ _ _ _ hiI hz
        rw [hiF] at h
        exact h
      have hstep : evalStmtFuel 0 heapDrain
          (mkHeapEnv vL n 0 last n root child other aR aC) =
          .ok (mkHeapEnv vL n 0 last n root child other aR aC,
            .fellThrough) :=
        evalStmtFuel_zero_while_exit _ _ _ hguard
      simp [heapifyFwd] at hok
      have hv : vL = v' := by simpa using hok
      subst hv
      exact ⟨root, child, other, aR, aC, hstep⟩
    · -- counter live but no fuel: forward loud
      have hi : (i != 0) = true := by simpa using h0
      have hbeq : (i == 0) = false := by simpa using hi
      simp only [heapifyFwd, hi, ite_true] at hok
      simp at hok
  | succ F IH =>
    simp only [heapifyFwd] at hok
    by_cases hi : (i != 0) = true
    · -- iterate: tick down, sift, recurse
      have hiI : evalExpr (.var "i")
          (mkHeapEnv vL n i last n root child other aR aC) =
          .ok (.u64 i) :=
        evalExpr_var_hit _ _ _ (mkHeapEnv_i _ _ _ _ _ _ _ _ _ _)
      have hz : evalExpr (.lit (.u64 0))
          (mkHeapEnv vL n i last n root child other aR aC) =
          .ok (.u64 0) := rfl
      have hguard : evalExpr (.une (.var "i") (.lit (.u64 0)))
          (mkHeapEnv vL n i last n root child other aR aC) =
          .ok (.b true) := by
        have h := evalExpr_une_u64 _ _ _ _ _ hiI hz
        rw [hi] at h
        exact h
      have hsub : evalExpr (.usub (.var "i") (.lit (.u64 1)))
          (mkHeapEnv vL n i last n root child other aR aC) =
          .ok (.u64 (i - 1)) :=
        evalExpr_u64_usub i 1 (.var "i") _ hiI
      have huI : envUpdate
          (mkHeapEnv vL n i last n root child other aR aC) "i"
          (.u64 (i - 1)) =
          some (mkHeapEnv vL n (i - 1) last n root child other
            aR aC) := by
        simp [mkHeapEnv, envExtend, envUpdate]
      have hassignI := evalStmtFuel_assign F "i"
        (.usub (.var "i") (.lit (.u64 1)))
        (mkHeapEnv vL n i last n root child other aR aC) _ _ hsub
        huI
      have hi2 : evalExpr (.var "i")
          (mkHeapEnv vL n (i - 1) last n root child other aR aC) =
          .ok (.u64 (i - 1)) :=
        evalExpr_var_hit _ _ _ (mkHeapEnv_i _ _ _ _ _ _ _ _ _ _)
      have huR : envUpdate
          (mkHeapEnv vL n (i - 1) last n root child other aR aC)
          "root" (.u64 (i - 1)) =
          some (mkHeapEnv vL n (i - 1) last n (i - 1) child other
            aR aC) := by
        simp [mkHeapEnv, envExtend, envUpdate]
      have hassignR := evalStmtFuel_assign F "root" (.var "i")
        (mkHeapEnv vL n (i - 1) last n root child other aR aC) _ _
        hi2 huR
      match hsift : siftFwd F vL n (i - 1) with
      | .error e =>
        simp only [hi, hsift, ite_true, ite_false] at hok
        simp at hok
      | .ok v1 =>
        simp only [hi, hsift, ite_true, ite_false] at hok
        obtain ⟨r', c', o', ar', ac', hsiftok⟩ :=
          siftLoop_ok F vL n (i - 1) last n (i - 1) child other aR
            aC v1 hsift
        have hbody : evalStmtFuel F heapDrainBody
            (mkHeapEnv vL n i last n root child other aR aC) =
            .ok (mkHeapEnv v1 n (i - 1) last n r' c' o' ar' ac',
              .fellThrough) := by
          have hmid : evalStmtFuel F
              (.seq (.assign "root" (.var "i")) heapSift)
              (mkHeapEnv vL n (i - 1) last n root child other aR
                aC) =
              .ok (mkHeapEnv v1 n (i - 1) last n r' c' o' ar' ac',
                .fellThrough) :=
            (evalStmtFuel_seq_fallthrough F _ _ _ _ hassignR).trans
              hsiftok
          have hunfold : heapDrainBody =
              .seq (.assign "i" (.usub (.var "i") (.lit (.u64 1))))
                (.seq (.assign "root" (.var "i")) heapSift) := rfl
          rw [hunfold]
          exact (evalStmtFuel_seq_fallthrough F _ _ _ _
            hassignI).trans hmid
        have hstep : evalStmtFuel (F + 1) heapDrain
            (mkHeapEnv vL n i last n root child other aR aC) =
            evalStmtFuel F heapDrain
              (mkHeapEnv v1 n (i - 1) last n r' c' o' ar' ac') := by
          simp only [heapDrain, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hguard, hbody]
        rw [hstep]
        exact IH _ _ _ _ _ _ _ hok
    · -- drained: exit with `i = 0`
      have hiF : (i != 0) = false := Bool.eq_false_of_ne_true hi
      have hi0 : i = 0 := by simpa using hi
      have hguard : evalExpr (.une (.var "i") (.lit (.u64 0)))
          (mkHeapEnv vL n i last n root child other aR aC) =
          .ok (.b false) := by
        have hiI : evalExpr (.var "i")
            (mkHeapEnv vL n i last n root child other aR aC) =
            .ok (.u64 i) :=
          evalExpr_var_hit _ _ _ (mkHeapEnv_i _ _ _ _ _ _ _ _ _ _)
        have hz : evalExpr (.lit (.u64 0))
            (mkHeapEnv vL n i last n root child other aR aC) =
            .ok (.u64 0) := rfl
        have h := evalExpr_une_u64 _ _ _ _ _ hiI hz
        rw [hiF] at h
        exact h
      have hstep : evalStmtFuel (F + 1) heapDrain
          (mkHeapEnv vL n i last n root child other aR aC) =
          .ok (mkHeapEnv vL n i last n root child other aR aC,
            .fellThrough) := by
        simp only [heapDrain, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hguard]
      simp only [heapifyFwd, hiF, ite_false] at hok
      have hv : vL = v' := by simpa using hok
      subst hv
      subst hi0
      exact ⟨root, child, other, aR, aC, hstep⟩

/-! ## Extract swap + drain agreement (ok direction) -/

/-- Exchange root/last words and shrink the sift bound: five
    straight-line ops. The `0` index is stated in `Nat` form to
    match the forward; `rfl`-level `toNat` unfolds bridge the
    evaluator side. -/
theorem extrSwap_ok (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (a b : BitVec 32)
    (hg0 : vL[0]? = some a)
    (hgL : vL[last.toNat]? = some b) :
    evalStmtFuel F extrSwap
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (mkHeapEnv ((vL.set 0 b).set last.toNat a) n i last last
        root child other a b, .fellThrough) := by
  have hbody : extrSwap =
      (.seq (.assign "aR" (.stdVecAt "v" (.lit (.u64 0))))
      (.seq (.assign "aC" (.stdVecAt "v" (.var "last")))
      (.seq (.vecSet "v" (.lit (.u64 0)) (.var "aC"))
      (.seq (.vecSet "v" (.var "last") (.var "aR"))
        (.assign "B" (.var "last")))))) := rfl
  have hv : envLookup
      (mkHeapEnv vL n i last B root child other aR aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have h0 : evalExpr (.lit (.u64 0))
      (mkHeapEnv vL n i last B root child other aR aC) =
      .ok (.u64 0) := rfl
  have hreadR := evalExpr_stdVecAt_some _ _ _ _ _ _ hv h0 hg0
  have huR : envUpdate
      (mkHeapEnv vL n i last B root child other aR aC) "aR"
      (.i32 a) =
      some (mkHeapEnv vL n i last B root child other a aC) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignR := evalStmtFuel_assign F "aR"
    (.stdVecAt "v" (.lit (.u64 0)))
    (mkHeapEnv vL n i last B root child other aR aC) _ _ hreadR huR
  have hlast : evalExpr (.var "last")
      (mkHeapEnv vL n i last B root child other a aC) =
      .ok (.u64 last) :=
    evalExpr_var_hit _ _ _
      (mkHeapEnv_last _ _ _ _ _ _ _ _ _ _)
  have hv2 : envLookup
      (mkHeapEnv vL n i last B root child other a aC) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hreadC := evalExpr_stdVecAt_some _ _ _ _ _ _ hv2 hlast hgL
  have huC : envUpdate
      (mkHeapEnv vL n i last B root child other a aC) "aC"
      (.i32 b) =
      some (mkHeapEnv vL n i last B root child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignC := evalStmtFuel_assign F "aC"
    (.stdVecAt "v" (.var "last"))
    (mkHeapEnv vL n i last B root child other a aC) _ _ hreadC huC
  have haC : evalExpr (.var "aC")
      (mkHeapEnv vL n i last B root child other a b) =
      .ok (.i32 b) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aC _ _ _ _ _ _ _ _ _ _)
  have hv3 : envLookup
      (mkHeapEnv vL n i last B root child other a b) "v" =
      some (.stdVecVal vL) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hu0 : envUpdate
      (mkHeapEnv vL n i last B root child other a b) "v"
      (.stdVecVal ((vL.set 0 b))) =
      some (mkHeapEnv (vL.set 0 b) n i last B root child other
        a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hset0 := evalStmtFuel_vecSet F "v" (.lit (.u64 0))
    (.var "aC")
    (mkHeapEnv vL n i last B root child other a b)
    0 b vL a _ h0 haC hv3 hg0 hu0
  have haR : evalExpr (.var "aR")
      (mkHeapEnv (vL.set 0 b) n i last B root child other a b) =
      .ok (.i32 a) :=
    evalExpr_var_hit _ _ _ (mkHeapEnv_aR _ _ _ _ _ _ _ _ _ _)
  have hlast2 : evalExpr (.var "last")
      (mkHeapEnv (vL.set 0 b) n i last B root child other a b) =
      .ok (.u64 last) :=
    evalExpr_var_hit _ _ _
      (mkHeapEnv_last _ _ _ _ _ _ _ _ _ _)
  have hv4 : envLookup
      (mkHeapEnv (vL.set 0 b) n i last B root child other a b) "v" =
      some (.stdVecVal (vL.set 0 b)) :=
    mkHeapEnv_v _ _ _ _ _ _ _ _ _ _
  have hgetL : ((vL.set 0 b)[last.toNat]? = some b) := by
    by_cases hLL : last.toNat = 0
    · rw [hLL]
      have hlen : 0 < vL.length :=
        (List.getElem?_eq_some_iff.mp hg0).1
      exact List.getElem?_set_self hlen
    · have hne0 : (0 : Nat) ≠ last.toNat := Ne.symm hLL
      simp [hne0, hgL]
  have huL : envUpdate
      (mkHeapEnv (vL.set 0 b) n i last B root child other a b) "v"
      (.stdVecVal ((vL.set 0 b).set last.toNat a)) =
      some (mkHeapEnv ((vL.set 0 b).set last.toNat a) n i last B
        root child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hsetL := evalStmtFuel_vecSet F "v" (.var "last") (.var "aR")
    (mkHeapEnv (vL.set 0 b) n i last B root child other a b)
    last a (vL.set 0 b) b _ hlast2 haR hv4 hgetL huL
  have hlast3 : evalExpr (.var "last")
      (mkHeapEnv ((vL.set 0 b).set last.toNat a) n i last B root
        child other a b) =
      .ok (.u64 last) :=
    evalExpr_var_hit _ _ _
      (mkHeapEnv_last _ _ _ _ _ _ _ _ _ _)
  have huB : envUpdate
      (mkHeapEnv ((vL.set 0 b).set last.toNat a) n i last B root
        child other a b) "B" (.u64 last) =
      some (mkHeapEnv ((vL.set 0 b).set last.toNat a) n i last
        last root child other a b) := by
    simp [mkHeapEnv, envExtend, envUpdate]
  have hassignB := evalStmtFuel_assign F "B" (.var "last")
    (mkHeapEnv ((vL.set 0 b).set last.toNat a) n i last B root
      child other a b) _ _ hlast3 huB
  rw [hbody]
  exact ((evalStmtFuel_seq_fallthrough F _ _ _ _ hassignR).trans
    ((evalStmtFuel_seq_fallthrough F _ _ _ _ hassignC).trans
      ((evalStmtFuel_seq_fallthrough F _ _ _ _ hset0).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hsetL).trans
          hassignB))))

/-- The extract countdown agrees with the forward on success:
    `last` ticks down, root/last exchange, the root is reset and
    the shrunk heap re-sifts. The post bound stays existential
    (internal cursor); only `last = 0` is pinned. -/
theorem extrDrain_ok (F : Nat) (vL : List (BitVec 32))
    (n i last B root child other : BitVec 64) (aR aC : BitVec 32)
    (v' : List (BitVec 32))
    (hok : extractFwd F vL n last = .ok v') :
    ∃ B' root' child' other' aR' aC',
      evalStmtFuel F extrDrain
        (mkHeapEnv vL n i last B root child other aR aC) =
        .ok (mkHeapEnv v' n i 0 B' root' child' other' aR' aC',
          .fellThrough) := by
  induction F generalizing vL last B root child other aR aC with
  | zero =>
    by_cases h0 : last = 0
    · -- counter exhausted on entry: forward ok, loop exits
      subst h0
      have hiF : ((0 : BitVec 64) != 0) = false := by decide
      have hguard : evalExpr (.une (.var "last") (.lit (.u64 0)))
          (mkHeapEnv vL n i 0 B root child other aR aC) =
          .ok (.b false) := by
        have hiL : evalExpr (.var "last")
            (mkHeapEnv vL n i 0 B root child other aR aC) =
            .ok (.u64 0) :=
          evalExpr_var_hit _ _ _
            (mkHeapEnv_last _ _ _ _ _ _ _ _ _ _)
        have hz : evalExpr (.lit (.u64 0))
            (mkHeapEnv vL n i 0 B root child other aR aC) =
            .ok (.u64 0) := rfl
        have h := evalExpr_une_u64 _ _ _ _ _ hiL hz
        rw [hiF] at h
        exact h
      have hstep : evalStmtFuel 0 extrDrain
          (mkHeapEnv vL n i 0 B root child other aR aC) =
          .ok (mkHeapEnv vL n i 0 B root child other aR aC,
            .fellThrough) :=
        evalStmtFuel_zero_while_exit _ _ _ hguard
      simp [extractFwd] at hok
      have hv : vL = v' := by simpa using hok
      subst hv
      exact ⟨B, root, child, other, aR, aC, hstep⟩
    · -- counter live but no fuel: forward loud
      have hi : (last != 0) = true := by simpa using h0
      simp only [extractFwd, hi, ite_true] at hok
      simp at hok
  | succ F IH =>
    simp only [extractFwd] at hok
    by_cases hi : (last != 0) = true
    · -- iterate: tick down, swap, reset root, sift, recurse
      have hiL : evalExpr (.var "last")
          (mkHeapEnv vL n i last B root child other aR aC) =
          .ok (.u64 last) :=
        evalExpr_var_hit _ _ _
          (mkHeapEnv_last _ _ _ _ _ _ _ _ _ _)
      have hz : evalExpr (.lit (.u64 0))
          (mkHeapEnv vL n i last B root child other aR aC) =
          .ok (.u64 0) := rfl
      have hguard : evalExpr (.une (.var "last") (.lit (.u64 0)))
          (mkHeapEnv vL n i last B root child other aR aC) =
          .ok (.b true) := by
        have h := evalExpr_une_u64 _ _ _ _ _ hiL hz
        rw [hi] at h
        exact h
      have hsub : evalExpr (.usub (.var "last") (.lit (.u64 1)))
          (mkHeapEnv vL n i last B root child other aR aC) =
          .ok (.u64 (last - 1)) :=
        evalExpr_u64_usub last 1 (.var "last") _ hiL
      have huL : envUpdate
          (mkHeapEnv vL n i last B root child other aR aC) "last"
          (.u64 (last - 1)) =
          some (mkHeapEnv vL n i (last - 1) B root child other
            aR aC) := by
        simp [mkHeapEnv, envExtend, envUpdate]
      have hassignL := evalStmtFuel_assign F "last"
        (.usub (.var "last") (.lit (.u64 1)))
        (mkHeapEnv vL n i last B root child other aR aC) _ _ hsub
        huL
      match hgr0 : vL[0]? with
      | some a =>
        match hgrL : vL[(last - 1).toNat]? with
        | some b =>
          have hswap := extrSwap_ok F vL n i (last - 1) B root
            child other aR aC a b hgr0 hgrL
          have h0lit : evalExpr (.lit (.u64 0))
              (mkHeapEnv ((vL.set 0 b).set (last - 1).toNat a) n i
                (last - 1) (last - 1) root child other a b) =
              .ok (.u64 0) := rfl
          have huR : envUpdate
              (mkHeapEnv ((vL.set 0 b).set (last - 1).toNat a) n i
                (last - 1) (last - 1) root child other a b)
              "root" (.u64 0) =
              some (mkHeapEnv ((vL.set 0 b).set (last - 1).toNat a)
                n i (last - 1) (last - 1) 0 child other a b) := by
            simp [mkHeapEnv, envExtend, envUpdate]
          have hassignR := evalStmtFuel_assign F "root"
            (.lit (.u64 0))
            (mkHeapEnv ((vL.set 0 b).set (last - 1).toNat a) n i
              (last - 1) (last - 1) root child other a b) _ _
            h0lit huR
          match hsift : siftFwd F ((vL.set 0 b).set (last - 1).toNat a)
              (last - 1) 0 with
          | .error e =>
            simp only [hi, hgr0, hgrL, hsift, ite_true,
              ite_false] at hok
            simp at hok
          | .ok v1 =>
            simp only [hi, hgr0, hgrL, hsift, ite_true,
              ite_false] at hok
            obtain ⟨r', c', o', ar', ac', hsiftok⟩ :=
              siftLoop_ok F ((vL.set 0 b).set (last - 1).toNat a) n
                i (last - 1) (last - 1) 0 child other a b v1 hsift
            have hbody : evalStmtFuel F extrDrainBody
                (mkHeapEnv vL n i last B root child other aR aC) =
                .ok (mkHeapEnv v1 n i (last - 1) (last - 1) r' c' o'
                  ar' ac', .fellThrough) := by
              have hmid : evalStmtFuel F
                  (.seq extrSwap
                    (.seq (.assign "root" (.lit (.u64 0)))
                      heapSift))
                  (mkHeapEnv vL n i (last - 1) B root child other
                    aR aC) =
                  .ok (mkHeapEnv v1 n i (last - 1) (last - 1) r' c'
                    o' ar' ac', .fellThrough) := by
                have hmid2 : evalStmtFuel F
                    (.seq (.assign "root" (.lit (.u64 0)))
                      heapSift)
                    (mkHeapEnv ((vL.set 0 b).set (last - 1).toNat a)
                      n i (last - 1) (last - 1) root child other a
                      b) =
                    .ok (mkHeapEnv v1 n i (last - 1) (last - 1) r'
                      c' o' ar' ac', .fellThrough) :=
                  (evalStmtFuel_seq_fallthrough F _ _ _ _
                    hassignR).trans hsiftok
                exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                  hswap).trans hmid2
              have hunfold : extrDrainBody =
                  .seq (.assign "last"
                    (.usub (.var "last") (.lit (.u64 1))))
                    (.seq extrSwap
                      (.seq (.assign "root" (.lit (.u64 0)))
                        heapSift)) := rfl
              rw [hunfold]
              exact (evalStmtFuel_seq_fallthrough F _ _ _ _
                hassignL).trans hmid
            have hstep : evalStmtFuel (F + 1) extrDrain
                (mkHeapEnv vL n i last B root child other aR aC) =
                evalStmtFuel F extrDrain
                  (mkHeapEnv v1 n i (last - 1) (last - 1) r' c' o'
                    ar' ac') := by
              simp only [extrDrain, evalStmtFuel,
                evalStmtSuccHandler, evalStmtWith, hguard, hbody]
            rw [hstep]
            exact IH _ _ _ _ _ _ _ _ hok
        | none =>
          simp only [hi, hgr0, hgrL, ite_true, ite_false] at hok
          simp at hok
      | none =>
        simp only [hi, hgr0, ite_true, ite_false] at hok
        simp at hok
    · -- drained: exit with `last = 0`
      have hiF : (last != 0) = false := Bool.eq_false_of_ne_true hi
      have hi0 : last = 0 := by simpa using hi
      have hguard : evalExpr (.une (.var "last") (.lit (.u64 0)))
          (mkHeapEnv vL n i last B root child other aR aC) =
          .ok (.b false) := by
        have hiL : evalExpr (.var "last")
            (mkHeapEnv vL n i last B root child other aR aC) =
            .ok (.u64 last) :=
          evalExpr_var_hit _ _ _
            (mkHeapEnv_last _ _ _ _ _ _ _ _ _ _)
        have hz : evalExpr (.lit (.u64 0))
            (mkHeapEnv vL n i last B root child other aR aC) =
            .ok (.u64 0) := rfl
        have h := evalExpr_une_u64 _ _ _ _ _ hiL hz
        rw [hiF] at h
        exact h
      have hstep : evalStmtFuel (F + 1) extrDrain
          (mkHeapEnv vL n i last B root child other aR aC) =
          .ok (mkHeapEnv vL n i last B root child other aR aC,
            .fellThrough) := by
        simp only [extrDrain, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hguard]
      simp only [extractFwd, hiF, ite_false] at hok
      have hv : vL = v' := by simpa using hok
      subst hv
      subst hi0
      exact ⟨B, root, child, other, aR, aC, hstep⟩

/-! ## Entry: seed, both drains, return -/

/-- The seed lands exactly on `mkHeapEnv` (env order matches the
    chain by construction). -/
theorem heapSeed_ok (F : Nat) (vL : List (BitVec 32))
    (N : BitVec 64) :
    evalStmtFuel F heapSeed [("v", .stdVecVal vL), ("n", .u64 N)] =
      .ok (mkHeapEnv vL N N N N 0 0 0 0 0, .fellThrough) := by
  have hbody : heapSeed =
      (.seq (.let_ "i" (.u 64) (.var "n"))
      (.seq (.let_ "last" (.u 64) (.var "n"))
      (.seq (.let_ "B" (.u 64) (.var "n"))
      (.seq (.let_ "root" (.u 64) (.lit (.u64 0)))
      (.seq (.let_ "child" (.u 64) (.lit (.u64 0)))
      (.seq (.let_ "other" (.u 64) (.lit (.u64 0)))
      (.seq (.let_ "aR" (.i 32) (.lit (.i32 0)))
        (.let_ "aC" (.i 32) (.lit (.i32 0)))))))))) := rfl
  have hn : envLookup [("v", .stdVecVal vL), ("n", .u64 N)] "n" =
      some (.u64 N) := by
    simp [envLookup]
  have hnv : evalExpr (.var "n")
      [("v", .stdVecVal vL), ("n", .u64 N)] = .ok (.u64 N) :=
    evalExpr_var_hit _ _ _ hn
  have h0u : evalExpr (.lit (.u64 0))
      [("v", .stdVecVal vL), ("n", .u64 N)] = .ok (.u64 0) := rfl
  have h0i : evalExpr (.lit (.i32 0))
      [("v", .stdVecVal vL), ("n", .u64 N)] = .ok (.i32 0) := rfl
  have li := evalStmtFuel_let_ F "i" (.u 64) (.var "n")
    [("v", .stdVecVal vL), ("n", .u64 N)] (.u64 N) hnv
  have hlk1 : envLookup
      (envExtend [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N))
      "n" = some (.u64 N) := by
    simp [envExtend, envLookup]
  have hnv1 : evalExpr (.var "n")
      (envExtend [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N)) =
      .ok (.u64 N) :=
    evalExpr_var_hit _ _ _ hlk1
  have hlast := evalStmtFuel_let_ F "last" (.u 64) (.var "n")
    (envExtend [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N))
    (.u64 N) hnv1
  have hlk2 : envLookup
      (envExtend (envExtend [("v", .stdVecVal vL), ("n", .u64 N)] "i"
        (.u64 N)) "last" (.u64 N)) "n" = some (.u64 N) := by
    simp [envExtend, envLookup]
  have hnv2 : evalExpr (.var "n")
      (envExtend (envExtend [("v", .stdVecVal vL), ("n", .u64 N)] "i"
        (.u64 N)) "last" (.u64 N)) = .ok (.u64 N) :=
    evalExpr_var_hit _ _ _ hlk2
  have hB := evalStmtFuel_let_ F "B" (.u 64) (.var "n")
    (envExtend (envExtend [("v", .stdVecVal vL), ("n", .u64 N)] "i"
      (.u64 N)) "last" (.u64 N))
    (.u64 N) hnv2
  have h0u3 : evalExpr (.lit (.u64 0))
      (envExtend (envExtend (envExtend
        [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N)) "last"
        (.u64 N)) "B" (.u64 N)) = .ok (.u64 0) := rfl
  have hroot := evalStmtFuel_let_ F "root" (.u 64) (.lit (.u64 0))
    (envExtend (envExtend (envExtend
      [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N)) "last"
      (.u64 N)) "B" (.u64 N))
    (.u64 0) h0u3
  have h0u4 : evalExpr (.lit (.u64 0))
      (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N)) "last"
        (.u64 N)) "B" (.u64 N)) "root" (.u64 0)) = .ok (.u64 0) :=
    rfl
  have hchild := evalStmtFuel_let_ F "child" (.u 64) (.lit (.u64 0))
    (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N)) "last"
      (.u64 N)) "B" (.u64 N)) "root" (.u64 0))
    (.u64 0) h0u4
  have h0u5 : evalExpr (.lit (.u64 0))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N)) "last"
        (.u64 N)) "B" (.u64 N)) "root" (.u64 0)) "child"
        (.u64 0)) = .ok (.u64 0) := rfl
  have hother := evalStmtFuel_let_ F "other" (.u 64) (.lit (.u64 0))
    (envExtend (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N)) "last"
      (.u64 N)) "B" (.u64 N)) "root" (.u64 0)) "child" (.u64 0))
    (.u64 0) h0u5
  have h0i6 : evalExpr (.lit (.i32 0))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N))
        "last" (.u64 N)) "B" (.u64 N)) "root" (.u64 0)) "child"
        (.u64 0)) "other" (.u64 0)) = .ok (.i32 0) := rfl
  have haR := evalStmtFuel_let_ F "aR" (.i 32) (.lit (.i32 0))
    (envExtend (envExtend (envExtend (envExtend (envExtend
      (envExtend [("v", .stdVecVal vL), ("n", .u64 N)] "i" (.u64 N))
      "last" (.u64 N)) "B" (.u64 N)) "root" (.u64 0)) "child"
      (.u64 0)) "other" (.u64 0))
    (.i32 0) h0i6
  have h0i7 : evalExpr (.lit (.i32 0))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend [("v", .stdVecVal vL), ("n", .u64 N)]
        "i" (.u64 N)) "last" (.u64 N)) "B" (.u64 N)) "root"
        (.u64 0)) "child" (.u64 0)) "other" (.u64 0)) "aR"
        (.i32 0)) = .ok (.i32 0) := rfl
  have haC := evalStmtFuel_let_ F "aC" (.i 32) (.lit (.i32 0))
    (envExtend (envExtend (envExtend (envExtend (envExtend
      (envExtend (envExtend [("v", .stdVecVal vL), ("n", .u64 N)]
      "i" (.u64 N)) "last" (.u64 N)) "B" (.u64 N)) "root"
      (.u64 0)) "child" (.u64 0)) "other" (.u64 0)) "aR"
      (.i32 0))
    (.i32 0) h0i7
  rw [hbody]
  exact ((evalStmtFuel_seq_fallthrough F _ _ _ _ li).trans
    ((evalStmtFuel_seq_fallthrough F _ _ _ _ hlast).trans
      ((evalStmtFuel_seq_fallthrough F _ _ _ _ hB).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hroot).trans
          ((evalStmtFuel_seq_fallthrough F _ _ _ _ hchild).trans
            ((evalStmtFuel_seq_fallthrough F _ _ _ _ hother).trans
              ((evalStmtFuel_seq_fallthrough F _ _ _ _ haR).trans
                haC)))))))

/-- Body-level entry: seed, heapify, extract, return. The two
    forward hypotheses pin the heap phase and the final order;
    sortedness/permutation is an H4 contract layer. -/
theorem heapSort_body_ok (F : Nat) (vL : List (BitVec 32))
    (N : BitVec 64) (vH v' : List (BitVec 32))
    (hH : heapifyFwd F vL N N = .ok vH)
    (hE : extractFwd F vH N N = .ok v') :
    ∃ ρ',
      evalStmtFuel F heapSortFunc.body
        [("v", .stdVecVal vL), ("n", .u64 N)] =
        .ok (ρ', .returned (.stdVecVal v')) := by
  have hseed := heapSeed_ok F vL N
  obtain ⟨rH, cH, oH, arH, acH, hdrain⟩ :=
    heapDrain_ok F vL N N N 0 0 0 0 0 vH hH
  obtain ⟨B', rE, cE, oE, arE, acE, hextr⟩ :=
    extrDrain_ok F vH N 0 N N rH cH oH arH acH v' hE
  have hv : evalExpr (.var "v")
      (mkHeapEnv v' N 0 0 B' rE cE oE arE acE) =
      .ok (.stdVecVal v') :=
    evalExpr_var_hit _ _ _
      (mkHeapEnv_v _ _ _ _ _ _ _ _ _ _)
  have hret := evalStmtFuel_return F (.var "v")
    (mkHeapEnv v' N 0 0 B' rE cE oE arE acE) _ hv
  have hfun : heapSortFunc.body =
      (.seq heapSeed
        (.seq heapDrain
          (.seq extrDrain
            (.return_ (.var "v"))))) := rfl
  rw [hfun]
  exact ⟨_,
    ((evalStmtFuel_seq_fallthrough F _ _ _ _ hseed).trans
      ((evalStmtFuel_seq_fallthrough F _ _ _ _ hdrain).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hextr).trans
          hret)))⟩

/-! ## H4: pure heapsort mirror + sort contract.

The fuel-threaded `siftFwd`/`heapifyFwd`/`extractFwd` use `BitVec 64`
cursors; the contract is proved about a pure `Nat`-indexed mirror
with the same recursion scheme, then transferred across by a
fuel-sufficiency bridge (`v.length + 1 ≤ F`, lengths below `2^63`
so no cursor wraps). Ascending means
`Pairwise (fun a b => (b.slt a) = false)` (the M5a relation);
order facts go through `toInt` + `omega` (the `slt_ge_trans`
precedent). -/

/-- Subtree membership: `r` is `root` or descends from it via
    `child = 2*r+1 / 2*r+2` (heap links, no division). -/
inductive InSubtree (root : Nat) : Nat → Prop
  | self : InSubtree root root
  | left {r : Nat} : InSubtree root r → InSubtree root (2 * r + 1)
  | right {r : Nat} : InSubtree root r → InSubtree root (2 * r + 2)

/-- Subtree nodes sit at or below the root. -/
theorem InSubtree.ge {root r : Nat} (h : InSubtree root r) :
    root ≤ r := by
  induction h with
  | self => exact Nat.le_refl _
  | left _ ih => omega
  | right _ ih => omega

/-- Children of a subtree node stay in the subtree. -/
theorem InSubtree.child {root r c : Nat}
    (h : InSubtree root r) (hc : c = 2 * r + 1 ∨ c = 2 * r + 2) :
    InSubtree root c := by
  rcases hc with rfl | rfl
  · exact .left h
  · exact .right h

/-- Subtrees nest: membership below a member. -/
theorem InSubtree.trans' {root m r : Nat}
    (h1 : InSubtree root m) (h2 : InSubtree m r) :
    InSubtree root r := by
  induction h2 with
  | self => exact h1
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- Every index is in the whole heap (`0`-rooted subtree): auxiliary
    induction on an upper bound (the parent sits below it). -/
theorem mem_subtree_zero_aux : ∀ n m : Nat, m ≤ n → InSubtree 0 m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    exact .self
  | succ n ih =>
    intro m hm
    by_cases h : m ≤ n
    · exact ih m h
    · have hm' : m = n + 1 := by omega
      subst hm'
      have hp : ((n + 1 - 1) / 2) ≤ n := by omega
      have h2 : n + 1 = 2 * ((n + 1 - 1) / 2) + 1 ∨
          n + 1 = 2 * ((n + 1 - 1) / 2) + 2 := by omega
      exact (ih _ hp).child h2

/-- Every index is in the whole heap (`0`-rooted subtree). -/
theorem mem_subtree_zero : ∀ n : Nat, InSubtree 0 n :=
  fun n => mem_subtree_zero_aux n n (Nat.le_refl _)

/-- `v[i]? = some x` forces `i < v.length`. -/
theorem lt_length_of_getElem?_eq_some {v : List (BitVec 32)}
    {i : Nat} {x : BitVec 32} (h : v[i]? = some x) :
    i < v.length := by
  by_cases hm : i < v.length
  · exact hm
  · have hle : v.length ≤ i := by omega
    rw [List.getElem?_eq_none_iff.mpr hle] at h
    cases h

/-- Reading back a just-read value. -/
theorem getElem_of_getElem?_eq_some {v : List (BitVec 32)}
    {i : Nat} {x : BitVec 32} (h : v[i]? = some x)
    (hil : i < v.length) : v[i] = x := by
  have h2 := List.getElem?_eq_getElem hil
  rw [h] at h2
  exact (Option.some.inj h2).symm

/-- Swapping two read positions preserves the permutation (count
    argument: each `set` adjusts one count, the two adjustments
    cancel). -/
theorem swapPerm (v : List (BitVec 32)) (i j : Nat)
    (x y : BitVec 32)
    (hi : v[i]? = some x) (hj : v[j]? = some y) :
    List.Perm (v.set i y |>.set j x) v := by
  have hil : i < v.length := lt_length_of_getElem?_eq_some hi
  have hjl : j < v.length := lt_length_of_getElem?_eq_some hj
  have hxi : v[i] = x := getElem_of_getElem?_eq_some hi hil
  have hyj : v[j] = y := getElem_of_getElem?_eq_some hj hjl
  apply List.perm_iff_count.mpr
  intro c
  have hlen : (v.set i y).length = v.length := List.length_set
  rw [List.count_set (by rw [hlen]; exact hjl), List.count_set hil]
  have e1 : ((v.set i y)[j] == c) = (y == c) := by
    rw [List.getElem_set (by rw [hlen]; exact hjl)]
    split
    · rfl
    · next h => rw [hyj]
  rw [e1, hxi]
  have hmemx : x ∈ v := by
    rw [← hxi]
    exact List.getElem_mem hil
  cases hxb : (x == c) with
  | true =>
    have hxeq : x = c := beq_iff_eq.mp hxb
    have h1 : 1 ≤ List.count c v := by
      rw [← hxeq]
      have hpos : 0 < List.count x v :=
        List.count_pos_iff.mpr hmemx
      omega
    cases hyb : (y == c) with
    | true =>
      simp only [hxb, hyb, ite_true]
      omega
    | false =>
      simp only [hxb, hyb, Bool.false_eq_true, ite_false, ite_true]
      omega
  | false =>
    cases hyb : (y == c) with
    | true =>
      simp only [hxb, hyb, Bool.false_eq_true, ite_false, ite_true]
      omega
    | false =>
      simp only [hxb, hyb, Bool.false_eq_true, ite_false]
      omega

/-- `slt` is asymmetric (via `toInt` + `omega`). -/
theorem slt_asymm {x y : BitVec 32} (h : (x.slt y) = true) :
    (y.slt x) = false := by
  rw [BitVec.slt_eq_decide] at h ⊢
  simp only [decide_eq_true_eq] at h
  simp only [decide_eq_false_iff_not]
  omega

/-- One sift level, pure `Nat` mirror of `siftFwd` (same recursion
    scheme; out-of-range reads fall back to `v`, dead under the
    bridge invariant). -/
def siftDown (bound root : Nat) (v : List (BitVec 32)) :
    List (BitVec 32) :=
  if hcb : root * 2 + 1 < bound then
    match v[root * 2 + 1]? with
    | some wc =>
      if hob : root * 2 + 1 + 1 < bound then
        match v[root * 2 + 1 + 1]? with
        | some wo =>
          match v[root]? with
          | some a =>
            if hcand : wc.slt wo then
              if hab : a.slt wo then
                siftDown bound (root * 2 + 1 + 1)
                  (v.set root wo |>.set (root * 2 + 1 + 1) a)
              else v
            else
              if hab : a.slt wc then
                siftDown bound (root * 2 + 1)
                  (v.set root wc |>.set (root * 2 + 1) a)
              else v
          | none => v
        | none => v
      else
        match v[root]? with
        | some a =>
          if hab : a.slt wc then
            siftDown bound (root * 2 + 1)
              (v.set root wc |>.set (root * 2 + 1) a)
          else v
        | none => v
    | none => v
  else v
termination_by bound - root
decreasing_by
  all_goals omega

/-- Heapify drain, pure mirror of `heapifyFwd` (count down from
    `i`, sifting each). -/
def heapifyDown (bound i : Nat) (v : List (BitVec 32)) :
    List (BitVec 32) :=
  match i with
  | 0 => v
  | n + 1 => heapifyDown bound n (siftDown bound n v)

/-- Extract drain, pure mirror of `extractFwd` (swap root/`last`,
    re-sift the shrunk heap). -/
def extractDown (bound last : Nat) (v : List (BitVec 32)) :
    List (BitVec 32) :=
  match last with
  | 0 => v
  | l + 1 =>
    match v[0]?, v[l]? with
    | some a, some b =>
      extractDown bound l (siftDown l 0 (v.set 0 b |>.set l a))
    | _, _ => v

/-- Pure heapsort: heapify, then extract. -/
def heapSortList (v : List (BitVec 32)) : List (BitVec 32) :=
  extractDown v.length v.length (heapifyDown v.length v.length v)

/-- Sifting permutes (functional induction: stops/misses are `rfl`,
    swaps chain the swap lemma with the IH). -/
theorem siftDown_perm (bound root : Nat) (v : List (BitVec 32)) :
    List.Perm (siftDown bound root v) v := by
  induction root, v using siftDown.induct with
  | bound => exact bound
  | case1 r l hcb wc hwc hob wo hwo a hro hcand hab ih =>
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true, List.Perm.refl]
    exact ih.trans (swapPerm l r (r * 2 + 1 + 1) a wo hro hwo)
  | case2 r l hcb wc hwc hob wo hwo a hro hcand hab =>
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true, List.Perm.refl]
  | case3 r l hcb wc hwc hob wo hwo a hro hcand hab ih =>
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true, List.Perm.refl]
    exact ih.trans (swapPerm l r (r * 2 + 1) a wc hro hwc)
  | case4 r l hcb wc hwc hob wo hwo a hro hcand hab =>
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true, List.Perm.refl]
  | case5 r l hcb wc hwc hob wo hwo hro =>
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, dite_true, dite_false, List.Perm.refl]
  | case6 r l hcb wc hwc hob hwo =>
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, dite_true, dite_false, List.Perm.refl]
  | case7 r l hcb wc hwc hob a hro hab ih =>
    unfold siftDown
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false, Bool.false_eq_true,
      List.Perm.refl]
    exact ih.trans (swapPerm l r (r * 2 + 1) a wc hro hwc)
  | case8 r l hcb wc hwc hob a hro hab =>
    unfold siftDown
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false, Bool.false_eq_true,
      List.Perm.refl]
  | case9 r l hcb wc hwc hob hro =>
    unfold siftDown
    simp only [hcb, hwc, hob, hro, dite_true, dite_false, List.Perm.refl]
  | case10 r l hcb hwc =>
    unfold siftDown
    simp only [hcb, hwc, dite_true, dite_false, List.Perm.refl]
  | case11 r l hcb =>
    unfold siftDown
    simp only [hcb, dite_true, dite_false, List.Perm.refl]

/-- Heapify drain permutes: each sift permutes, chained by induction. -/
theorem heapifyDown_perm (bound i : Nat) (v : List (BitVec 32)) :
    List.Perm (heapifyDown bound i v) v := by
  induction i generalizing v with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    simp only [heapifyDown]
    exact (ih _).trans (siftDown_perm bound n v)

/-- Extract drain permutes: the root/`last` swap permutes, the re-sift
    permutes, chained by induction. -/
theorem extractDown_perm (bound last : Nat) (v : List (BitVec 32)) :
    List.Perm (extractDown bound last v) v := by
  induction last generalizing v with
  | zero => exact List.Perm.refl _
  | succ l ih =>
    simp only [extractDown]
    cases h0 : v[0]? with
    | none =>
      cases hl : v[l]? with
      | none => exact List.Perm.refl _
      | some _ => exact List.Perm.refl _
    | some a =>
      cases hl : v[l]? with
      | none => exact List.Perm.refl _
      | some b =>
        simp only [h0, hl]
        exact (ih _).trans
          ((siftDown_perm l 0 _).trans (swapPerm v 0 l a b h0 hl))

/-- Pure heapsort permutes its input. -/
theorem heapSortList_perm (v : List (BitVec 32)) :
    List.Perm (heapSortList v) v := by
  simp only [heapSortList]
  exact (extractDown_perm _ _ _).trans (heapifyDown_perm _ _ _)

/-! ## H4b: max-heap invariant -/

/-- Heap order at one subtree: every in-bound child is `≤` its parent
    (`a.slt b = false` with `a` at the parent: the parent is never
    strictly below a child). -/
def HeapAt (bound j : Nat) (l : List (BitVec 32)) : Prop :=
  ∀ s t a b, InSubtree j s → (t = 2 * s + 1 ∨ t = 2 * s + 2) → t < bound →
    l[s]? = some a → l[t]? = some b → a.slt b = false

/-- Heap order at every subtree rooted at or above `n`. -/
def HeapAbove (bound n : Nat) (l : List (BitVec 32)) : Prop :=
  ∀ j, n ≤ j → j < bound → HeapAt bound j l

/-- Max-heap: heap order at every subtree. -/
def IsHeap (bound : Nat) (l : List (BitVec 32)) : Prop :=
  HeapAbove bound 0 l

/-- Reading a valid index always succeeds. -/
theorem getElem?_some_of_lt_length {l : List (BitVec 32)} {k : Nat}
    (h : k < l.length) : ∃ x, l[k]? = some x :=
  ⟨l[k], List.getElem?_eq_getElem h⟩

/-- `HeapAt` survives a write outside the subtree. -/
theorem HeapAt_set_ne {bound j p : Nat} {x : BitVec 32}
    {l : List (BitVec 32)} (hp : ¬ InSubtree j p)
    (h : HeapAt bound j l) : HeapAt bound j (l.set p x) := by
  intro s t a b hs ht htb hsa hsb
  have hsne : s ≠ p := fun e => hp (e ▸ hs)
  have htne : t ≠ p := by
    intro e
    apply hp
    subst e
    exact hs.child ht
  rw [List.getElem?_set_ne hsne.symm] at hsa
  rw [List.getElem?_set_ne htne.symm] at hsb
  exact h s t a b hs ht htb hsa hsb

/-- Subtree membership splits at the root: either the root itself or a
    strict descendant with an explicit intermediate parent. -/
theorem InSubtree.eq_or_parent {j c : Nat} (h : InSubtree j c) :
    j = c ∨ ∃ r, InSubtree j r ∧ (c = 2 * r + 1 ∨ c = 2 * r + 2) := by
  cases h with
  | self => exact Or.inl rfl
  | left h' => exact Or.inr ⟨_, h', Or.inl rfl⟩
  | right h' => exact Or.inr ⟨_, h', Or.inr rfl⟩

/-- A node strictly above a child link is outside the child's
    subtree unless it is the child itself. -/
theorem not_mem_child_of {j c r : Nat} (hrj : r < j) (hne : j ≠ c)
    (hc : c = 2 * r + 1 ∨ c = 2 * r + 2) (h : InSubtree j c) : False := by
  rcases h.eq_or_parent with rfl | ⟨r', hr', hc'⟩
  · exact hne rfl
  · have heq : r' = r := by
      rcases hc with hc | hc <;> rcases hc' with hc' | hc' <;> omega
    subst heq
    have := hr'.ge
    omega

/-- A heap-ordered subtree root bounds every value below it. -/
theorem HeapAt_all {bound j : Nat} {l : List (BitVec 32)}
    (h : HeapAt bound j l) {x : BitVec 32} (hx : l[j]? = some x)
    {s : Nat} (hs : InSubtree j s) (hlt : s < bound)
    {y : BitVec 32} (hy : l[s]? = some y) :
    x.slt y = false := by
  refine InSubtree.rec
    (motive := fun s _ => ∀ (hlt : s < bound) (y : BitVec 32)
      (hy : l[s]? = some y), x.slt y = false)
    ?_ ?_ ?_ hs hlt y hy
  · intro hlt y hy
    have heq : x = y := Option.some.inj (hx.symm.trans hy)
    subst heq
    exact VecSelectionSort.slt_irrefl x
  · intro r' h' ih hlt y hy
    obtain ⟨z, hz⟩ := getElem?_some_of_lt_length
      (l := l) (k := r')
      (by have hlen := lt_length_of_getElem?_eq_some hy; omega)
    have h1 : x.slt z = false := ih (by omega) z hz
    have h2 : z.slt y = false :=
      h r' (2 * r' + 1) z y h' (Or.inl rfl) hlt hz hy
    exact VecSelectionSort.slt_ge_trans h1 h2
  · intro r' h' ih hlt y hy
    obtain ⟨z, hz⟩ := getElem?_some_of_lt_length
      (l := l) (k := r')
      (by have hlen := lt_length_of_getElem?_eq_some hy; omega)
    have h1 : x.slt z = false := ih (by omega) z hz
    have h2 : z.slt y = false :=
      h r' (2 * r' + 2) z y h' (Or.inr rfl) hlt hz hy
    exact VecSelectionSort.slt_ge_trans h1 h2

/-- Subtree membership splits at an explicit child pair. -/
theorem InSubtree.child_or {n c o s : Nat}
    (hc : c = 2 * n + 1) (ho : o = 2 * n + 2)
    (hs : InSubtree n s) :
    s = n ∨ InSubtree c s ∨ InSubtree o s := by
  induction hs with
  | self => exact Or.inl rfl
  | left h' ih =>
    rcases ih with rfl | h1 | h2
    · exact Or.inr (Or.inl (hc ▸ InSubtree.self))
    · exact Or.inr (Or.inl (InSubtree.left h1))
    · exact Or.inr (Or.inr (InSubtree.left h2))
  | right h' ih =>
    rcases ih with rfl | h1 | h2
    · exact Or.inr (Or.inr (ho ▸ InSubtree.self))
    · exact Or.inr (Or.inl (InSubtree.right h1))
    · exact Or.inr (Or.inr (InSubtree.right h2))

/-- `slt` bridge facts (via `toInt`, the `slt_ge_trans` precedent). -/
theorem slt_lt_of_true {a b : BitVec 32} (h : a.slt b = true) :
    a.toInt < b.toInt := by
  rw [BitVec.slt_eq_decide] at h
  simpa using h

theorem slt_nlt_of_false {a b : BitVec 32} (h : a.slt b = false) :
    ¬ a.toInt < b.toInt := by
  rw [BitVec.slt_eq_decide] at h
  simpa using h

theorem slt_nlt_of_notrue {a b : BitVec 32} (h : ¬ a.slt b = true) :
    ¬ a.toInt < b.toInt := by
  rw [BitVec.slt_eq_decide] at h
  simpa using h

theorem slt_of_nlt {a b : BitVec 32} (h : ¬ a.toInt < b.toInt) :
    a.slt b = false := by
  rw [BitVec.slt_eq_decide]
  simpa using h

/-- Child links with source-syntax indices. -/
theorem mem_child_left (r : Nat) : InSubtree r (r * 2 + 1) := by
  have h : r * 2 + 1 = 2 * r + 1 := by omega
  rw [h]
  exact InSubtree.left InSubtree.self

theorem mem_child_right (r : Nat) : InSubtree r (r * 2 + 1 + 1) := by
  have h : r * 2 + 1 + 1 = 2 * r + 2 := by omega
  rw [h]
  exact InSubtree.right InSubtree.self

/-- Sifting only writes inside the sift root's subtree: reads anywhere
    else are preserved. -/
theorem siftDown_get_outside (bound r : Nat) (l : List (BitVec 32))
    (t : Nat) (ht : ¬ InSubtree r t) :
    (siftDown bound r l)[t]? = l[t]? := by
  refine siftDown.induct bound
    (fun r l => ¬ InSubtree r t → (siftDown bound r l)[t]? = l[t]?)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ ht
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih ht
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
    have hcr : InSubtree r (r * 2 + 1 + 1) := mem_child_right r
    have hct : ¬ InSubtree (r * 2 + 1 + 1) t :=
      fun hc' => ht (hcr.trans' hc')
    have hne1 : r * 2 + 1 + 1 ≠ t := by
      intro e; subst e; exact hct InSubtree.self
    have hne2 : r ≠ t := by
      intro e; subst e; exact ht InSubtree.self
    rw [ih hct, List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ht
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih ht
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
    have hcr : InSubtree r (r * 2 + 1) := mem_child_left r
    have hct : ¬ InSubtree (r * 2 + 1) t :=
      fun hc' => ht (hcr.trans' hc')
    have hne1 : r * 2 + 1 ≠ t := by
      intro e; subst e; exact hct InSubtree.self
    have hne2 : r ≠ t := by
      intro e; subst e; exact ht InSubtree.self
    rw [ih hct, List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ht
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob wo hwo hro ht
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob hwo ht
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob a hro hab ih ht
    unfold siftDown
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
      Bool.false_eq_true]
    have hcr : InSubtree r (r * 2 + 1) := mem_child_left r
    have hct : ¬ InSubtree (r * 2 + 1) t :=
      fun hc' => ht (hcr.trans' hc')
    have hne1 : r * 2 + 1 ≠ t := by
      intro e; subst e; exact hct InSubtree.self
    have hne2 : r ≠ t := by
      intro e; subst e; exact ht InSubtree.self
    rw [ih hct, List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
  · intro r l hcb wc hwc hob a hro hab ht
    unfold siftDown
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob hro ht
    unfold siftDown
    simp only [hcb, hwc, hob, hro, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb hwc ht
    unfold siftDown
    simp only [hcb, hwc, dite_true, dite_false, Bool.false_eq_true]
  · intro r l hcb ht
    unfold siftDown
    simp only [hcb, dite_true, dite_false, Bool.false_eq_true]

/-- Values landing in-bound inside the sift region come from in-bound
    positions of the original region. -/
theorem siftDown_mem_region (bound r : Nat) (l : List (BitVec 32))
    (t : Nat) (x : BitVec 32) (htt : InSubtree r t) (htb : t < bound)
    (hx : (siftDown bound r l)[t]? = some x) :
    ∃ t', InSubtree r t' ∧ t' < bound ∧ l[t']? = some x := by
  refine siftDown.induct bound
    (fun r l => ∀ (t : Nat) (x : BitVec 32), InSubtree r t → t < bound →
      (siftDown bound r l)[t]? = some x →
      ∃ t', InSubtree r t' ∧ t' < bound ∧ l[t']? = some x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ r l t x htt htb hx
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true] at hx
    rcases Classical.em (InSubtree (r * 2 + 1 + 1) t) with hmem | hmem
    · obtain ⟨t', ht', htb', hsw⟩ := ih t x hmem htb hx
      by_cases he2 : t' = r * 2 + 1 + 1
      · rw [he2] at hsw
        have hswa : ((l.set r wo).set (r * 2 + 1 + 1) a)[r * 2 + 1 + 1]? =
            some a :=
          List.getElem?_set_self (by
            rw [List.length_set]
            exact lt_length_of_getElem?_eq_some hwo)
        have hxa : a = x := Option.some.inj (hswa.symm.trans hsw)
        exact ⟨r, InSubtree.self, by omega, hxa ▸ hro⟩
      · have htr : t' ≠ r := by
          intro e; subst e; have := ht'.ge; omega
        have hswl : l[t']? = some x := by
          have e1 : r ≠ t' := fun e => htr e.symm
          have e2 : r * 2 + 1 + 1 ≠ t' := fun e => he2 e.symm
          rw [List.getElem?_set_ne e2] at hsw
          rw [List.getElem?_set_ne e1] at hsw
          exact hsw
        exact ⟨t', (mem_child_right r).trans' ht', htb', hswl⟩
    · rw [siftDown_get_outside _ _ _ _ hmem] at hx
      by_cases he1 : t = r
      · rw [he1] at hx
        have hswr : ((l.set r wo).set (r * 2 + 1 + 1) a)[r]? = some wo := by
          have hne : r * 2 + 1 + 1 ≠ r := by omega
          have hlt : r < l.length := lt_length_of_getElem?_eq_some hro
          rw [List.getElem?_set_ne hne]
          rw [List.getElem?_set_self hlt]
        have hxw : wo = x := Option.some.inj (hswr.symm.trans hx)
        exact ⟨r * 2 + 1 + 1, mem_child_right r, hob, hxw ▸ hwo⟩
      · by_cases he2 : t = r * 2 + 1 + 1
        · rw [he2] at hmem
          exact False.elim (hmem InSubtree.self)
        · have hswl : l[t]? = some x := by
            have e1 : r ≠ t := fun e => he1 e.symm
            have e2 : r * 2 + 1 + 1 ≠ t := fun e => he2 e.symm
            rw [List.getElem?_set_ne e2] at hx
            rw [List.getElem?_set_ne e1] at hx
            exact hx
          exact ⟨t, htt, htb, hswl⟩
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true] at hx
    exact ⟨t, htt, htb, hx⟩
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true] at hx
    rcases Classical.em (InSubtree (r * 2 + 1) t) with hmem | hmem
    · obtain ⟨t', ht', htb', hsw⟩ := ih t x hmem htb hx
      by_cases he2 : t' = r * 2 + 1
      · rw [he2] at hsw
        have hswa : ((l.set r wc).set (r * 2 + 1) a)[r * 2 + 1]? =
            some a :=
          List.getElem?_set_self (by
            rw [List.length_set]
            exact lt_length_of_getElem?_eq_some hwc)
        have hxa : a = x := Option.some.inj (hswa.symm.trans hsw)
        exact ⟨r, InSubtree.self, by omega, hxa ▸ hro⟩
      · have htr : t' ≠ r := by
          intro e; subst e; have := ht'.ge; omega
        have hswl : l[t']? = some x := by
          have e1 : r ≠ t' := fun e => htr e.symm
          have e2 : r * 2 + 1 ≠ t' := fun e => he2 e.symm
          rw [List.getElem?_set_ne e2] at hsw
          rw [List.getElem?_set_ne e1] at hsw
          exact hsw
        exact ⟨t', (mem_child_left r).trans' ht', htb', hswl⟩
    · rw [siftDown_get_outside _ _ _ _ hmem] at hx
      by_cases he1 : t = r
      · rw [he1] at hx
        have hswr : ((l.set r wc).set (r * 2 + 1) a)[r]? = some wc := by
          have hne : r * 2 + 1 ≠ r := by omega
          have hlt : r < l.length := lt_length_of_getElem?_eq_some hro
          rw [List.getElem?_set_ne hne]
          rw [List.getElem?_set_self hlt]
        have hxw : wc = x := Option.some.inj (hswr.symm.trans hx)
        exact ⟨r * 2 + 1, mem_child_left r, hcb, hxw ▸ hwc⟩
      · by_cases he2 : t = r * 2 + 1
        · rw [he2] at hmem
          exact False.elim (hmem InSubtree.self)
        · have hswl : l[t]? = some x := by
            have e1 : r ≠ t := fun e => he1 e.symm
            have e2 : r * 2 + 1 ≠ t := fun e => he2 e.symm
            rw [List.getElem?_set_ne e2] at hx
            rw [List.getElem?_set_ne e1] at hx
            exact hx
          exact ⟨t, htt, htb, hswl⟩
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true] at hx
    exact ⟨t, htt, htb, hx⟩
  · intro r l hcb wc hwc hob wo hwo hro t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, hob, hwo, hro, dite_true, dite_false,
      Bool.false_eq_true] at hx
    exact ⟨t, htt, htb, hx⟩
  · intro r l hcb wc hwc hob hwo t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, hob, hwo, dite_true, dite_false,
      Bool.false_eq_true] at hx
    exact ⟨t, htt, htb, hx⟩
  · intro r l hcb wc hwc hob a hro hab ih t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
      Bool.false_eq_true] at hx
    rcases Classical.em (InSubtree (r * 2 + 1) t) with hmem | hmem
    · obtain ⟨t', ht', htb', hsw⟩ := ih t x hmem htb hx
      by_cases he2 : t' = r * 2 + 1
      · rw [he2] at hsw
        have hswa : ((l.set r wc).set (r * 2 + 1) a)[r * 2 + 1]? =
            some a :=
          List.getElem?_set_self (by
            rw [List.length_set]
            exact lt_length_of_getElem?_eq_some hwc)
        have hxa : a = x := Option.some.inj (hswa.symm.trans hsw)
        exact ⟨r, InSubtree.self, by omega, hxa ▸ hro⟩
      · have htr : t' ≠ r := by
          intro e; subst e; have := ht'.ge; omega
        have hswl : l[t']? = some x := by
          have e1 : r ≠ t' := fun e => htr e.symm
          have e2 : r * 2 + 1 ≠ t' := fun e => he2 e.symm
          rw [List.getElem?_set_ne e2] at hsw
          rw [List.getElem?_set_ne e1] at hsw
          exact hsw
        exact ⟨t', (mem_child_left r).trans' ht', htb', hswl⟩
    · rw [siftDown_get_outside _ _ _ _ hmem] at hx
      by_cases he1 : t = r
      · rw [he1] at hx
        have hswr : ((l.set r wc).set (r * 2 + 1) a)[r]? = some wc := by
          have hne : r * 2 + 1 ≠ r := by omega
          have hlt : r < l.length := lt_length_of_getElem?_eq_some hro
          rw [List.getElem?_set_ne hne]
          rw [List.getElem?_set_self hlt]
        have hxw : wc = x := Option.some.inj (hswr.symm.trans hx)
        exact ⟨r * 2 + 1, mem_child_left r, hcb, hxw ▸ hwc⟩
      · by_cases he2 : t = r * 2 + 1
        · rw [he2] at hmem
          exact False.elim (hmem InSubtree.self)
        · have hswl : l[t]? = some x := by
            have e1 : r ≠ t := fun e => he1 e.symm
            have e2 : r * 2 + 1 ≠ t := fun e => he2 e.symm
            rw [List.getElem?_set_ne e2] at hx
            rw [List.getElem?_set_ne e1] at hx
            exact hx
          exact ⟨t, htt, htb, hswl⟩
  · intro r l hcb wc hwc hob a hro hab t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
      Bool.false_eq_true] at hx
    exact ⟨t, htt, htb, hx⟩
  · intro r l hcb wc hwc hob hro t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, hob, hro, dite_true, dite_false,
      Bool.false_eq_true] at hx
    exact ⟨t, htt, htb, hx⟩
  · intro r l hcb hwc t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, hwc, dite_true, dite_false, Bool.false_eq_true] at hx
    exact ⟨t, htt, htb, hx⟩
  · intro r l hcb t x htt htb hx
    unfold siftDown at hx
    simp only [hcb, dite_true, dite_false, Bool.false_eq_true] at hx
    exact ⟨t, htt, htb, hx⟩

/-- Subtree co-members are comparable by inclusion. -/
theorem subtree_comparable {j c' t : Nat} (h1 : InSubtree j t)
    (h2 : InSubtree c' t) : InSubtree j c' ∨ InSubtree c' j := by
  induction h1 with
  | self => exact Or.inr h2
  | left h' ih =>
    rename_i r''
    rcases h2.eq_or_parent with rfl | ⟨p, hcp, htp⟩
    · exact Or.inl (InSubtree.left h')
    · have hpp : p = r'' := by
        rcases htp with htp | htp <;> omega
      subst hpp
      exact ih hcp
  | right h' ih =>
    rename_i r''
    rcases h2.eq_or_parent with rfl | ⟨p, hcp, htp⟩
    · exact Or.inl (InSubtree.right h')
    · have hpp : p = r'' := by
        rcases htp with htp | htp <;> omega
      subst hpp
      exact ih hcp

/-- A child of the middle region reached from inside stays inside. -/
theorem middle_child_closed {r c' j s t : Nat}
    (hc' : c' = 2 * r + 1 ∨ c' = 2 * r + 2)
    (hjr : r < j) (hjc : j < c') (hjs : InSubtree j s)
    (hct : InSubtree c' t) (ht : t = 2 * s + 1 ∨ t = 2 * s + 2) :
    InSubtree c' s := by
  have hsr : s ≠ r := by
    intro e; subst e; have := hjs.ge; omega
  rcases hct.eq_or_parent with rfl | ⟨p, hcp, htp⟩
  · have hsr' : s = r := by
      rcases hc' with hc' | hc' <;> rcases ht with ht | ht <;> omega
    exact absurd hsr' hsr
  · have hps : p = s := by
      rcases ht with ht | ht <;> rcases htp with htp | htp <;> omega
    subst hps
    exact hcp

/-- A node strictly between a link stays outside the child's subtree. -/
theorem not_mem_child_above {j r c : Nat}
    (hc : c = r * 2 + 1 ∨ c = r * 2 + 1 + 1)
    (hjr : r < j) (hjc : j < c) : ¬ InSubtree j c := by
  intro hc'
  rcases hc'.eq_or_parent with hjj | ⟨p, hjp, hpc⟩
  · omega
  · have hpr : p = r := by
      rcases hc with hc | hc <;> rcases hpc with hpc | hpc <;> omega
    subst hpr
    have := hjp.ge
    omega

/-- Subtree membership splits at source-syntax child indices. -/
theorem InSubtree.child_or2 {r s : Nat} (hs : InSubtree r s) :
    s = r ∨ InSubtree (r * 2 + 1) s ∨ InSubtree (r * 2 + 1 + 1) s := by
  have hc : r * 2 + 1 = 2 * r + 1 := by omega
  have ho : r * 2 + 1 + 1 = 2 * r + 2 := by omega
  rcases InSubtree.child_or (c := r * 2 + 1) (o := r * 2 + 1 + 1) hc ho hs with
    h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The other child sits outside the recursed sibling subtree. -/
theorem not_mem_sibling {r c o : Nat} (hc : c = r * 2 + 1)
    (ho : o = r * 2 + 1 + 1) : ¬ InSubtree c o := by
  intro hco
  rcases hco.eq_or_parent with hcon | ⟨p, hcp, hpo⟩
  · omega
  · have hpr : p = r := by
      rcases hpo with hpo | hpo <;> omega
    subst hpr
    have := hcp.ge
    omega

/-- Sifting restores heap order at and above the sift root. The bound
    must sit inside the list so missing-node cases are contradictory. -/
theorem sift_step (bound r : Nat) (l : List (BitVec 32))
    (hlen : bound ≤ l.length)
    (h : HeapAbove bound (r + 1) l) :
    HeapAbove bound r (siftDown bound r l) := by
  refine siftDown.induct bound
    (fun r l => bound ≤ l.length → HeapAbove bound (r + 1) l →
      HeapAbove bound r (siftDown bound r l))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ r l hlen h
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih hlen h
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
    have hlen' : bound ≤ ((l.set r wo).set (r * 2 + 1 + 1) a).length := by
      rwa [List.length_set, List.length_set]
    have hpres : HeapAbove bound (r * 2 + 1 + 1 + 1)
        ((l.set r wo).set (r * 2 + 1 + 1) a) := by
      intro j hj1 hj2
      have hrj : ¬ InSubtree j r := by
        intro hr; have := hr.ge; omega
      have hoj : ¬ InSubtree j (r * 2 + 1 + 1) := by
        intro ho'; have := ho'.ge; omega
      exact HeapAt_set_ne hoj
        (HeapAt_set_ne hrj (h j (by omega) hj2))
    have ihc := ih hlen' hpres
    have hmax : ∀ t' y, InSubtree r t' → t' < bound → l[t']? = some y →
        wo.slt y = false := by
      intro t' y ht' htb' hl'
      by_cases he : t' = r
      · rw [he] at hl'
        have hya : y = a := Option.some.inj (hl'.symm.trans hro)
        rw [hya]
        exact slt_of_nlt (by have := slt_lt_of_true hab; omega)
      · rcases InSubtree.child_or2 ht' with hcon | hcs | hos
        · exact absurd hcon he
        · have h1 := HeapAt_all (h (r * 2 + 1) (by omega) hcb) hwc hcs
            htb' hl'
          have hc1 := slt_lt_of_true hcand
          have hn1 := slt_nlt_of_false h1
          exact slt_of_nlt (by omega)
        · exact HeapAt_all (h (r * 2 + 1 + 1) (by omega) hob) hwo hos
            htb' hl'
    have hmid : ∀ j, r < j → j < r * 2 + 1 + 1 → j < bound →
        HeapAt bound j
          (siftDown bound (r * 2 + 1 + 1) ((l.set r wo).set (r * 2 + 1 + 1) a)) := by
      intro j hjr hjc hjb s t x y hs ht htb hsx hsy
      rcases Nat.lt_or_ge s (r * 2 + 1 + 1) with hlt | hge
      · have hns : ¬ InSubtree (r * 2 + 1 + 1) s := by
          intro hs'; have := hs'.ge; omega
        have hnt : ¬ InSubtree (r * 2 + 1 + 1) t := by
          intro ht'
          exact hns (middle_child_closed (Or.inr (by omega)) hjr hjc hs ht' ht)
        rw [siftDown_get_outside _ _ _ _ hns] at hsx
        rw [siftDown_get_outside _ _ _ _ hnt] at hsy
        have hSW : HeapAt bound j ((l.set r wo).set (r * 2 + 1 + 1) a) := by
          apply HeapAt_set_ne
            (not_mem_child_above (Or.inr rfl) hjr hjc)
          apply HeapAt_set_ne (by intro hr'; have := hr'.ge; omega)
          exact h j (by omega) hjb
        exact hSW s t x y hs ht htb hsx hsy
      · exact ihc s hge (by omega) s t x y InSubtree.self ht htb hsx hsy

    have hroot : HeapAt bound r
        (siftDown bound (r * 2 + 1 + 1) ((l.set r wo).set (r * 2 + 1 + 1) a)) := by
      have hRr : (siftDown bound (r * 2 + 1 + 1)
          ((l.set r wo).set (r * 2 + 1 + 1) a))[r]? = some wo := by
        have hnr : ¬ InSubtree (r * 2 + 1 + 1) r := by
          intro hr; have := hr.ge; omega
        rw [siftDown_get_outside _ _ _ _ hnr]
        have hne : r * 2 + 1 + 1 ≠ r := by omega
        have hlt : r < l.length := lt_length_of_getElem?_eq_some hro
        rw [List.getElem?_set_ne hne]
        rw [List.getElem?_set_self hlt]
      intro s t x y hs ht htb hsx hsy
      rcases InSubtree.child_or2 hs with hsr | hcs | hos
      rw [hsr] at hs ht hsx
      · have hxw : x = wo := Option.some.inj (hsx.symm.trans hRr)
        rw [hxw]
        rcases (by rcases ht with h | h <;> omega : t = r * 2 + 1 ∨ t = r * 2 + 1 + 1) with rfl | rfl
        · have hnc : ¬ InSubtree (r * 2 + 1 + 1) (r * 2 + 1) := by
            intro hc'; have := hc'.ge; omega
          have hRc : (siftDown bound (r * 2 + 1 + 1)
              ((l.set r wo).set (r * 2 + 1 + 1) a))[r * 2 + 1]? = some wc := by
            rw [siftDown_get_outside _ _ _ _ hnc]
            have e1 : r ≠ r * 2 + 1 := by omega
            have e2 : r * 2 + 1 + 1 ≠ r * 2 + 1 := by omega
            rw [List.getElem?_set_ne e2]
            rw [List.getElem?_set_ne e1]
            exact hwc
          have hyw : y = wc := Option.some.inj (hsy.symm.trans hRc)
          rw [hyw]
          exact slt_of_nlt (by have := slt_lt_of_true hcand; omega)
        · obtain ⟨t', ht', htb', hl'⟩ :=
            siftDown_mem_region bound (r * 2 + 1 + 1)
              ((l.set r wo).set (r * 2 + 1 + 1) a) (r * 2 + 1 + 1) y
              InSubtree.self htb hsy
          by_cases heo : t' = r * 2 + 1 + 1
          · rw [heo] at hl'
            have hswa : ((l.set r wo).set (r * 2 + 1 + 1) a)[r * 2 + 1 + 1]? =
                some a :=
              List.getElem?_set_self (by
                rw [List.length_set]
                exact lt_length_of_getElem?_eq_some hwo)
            have hya : a = y := Option.some.inj (hswa.symm.trans hl')
            rw [← hya]
            exact slt_of_nlt (by have := slt_lt_of_true hab; omega)
          · have htr : t' ≠ r := by
              intro e
              have hge := ht'.ge
              omega
            have hswl : l[t']? = some y := by
              have e1 : r ≠ t' := fun e => htr e.symm
              have e2 : r * 2 + 1 + 1 ≠ t' := fun e => heo e.symm
              rw [List.getElem?_set_ne e2] at hl'
              rw [List.getElem?_set_ne e1] at hl'
              exact hl'
            have htr' : InSubtree r t' :=
              (mem_child_right r).trans' ht'
            exact hmax t' y htr' htb' hswl
      · by_cases hso : r * 2 + 1 + 1 ≤ s
        · exact ihc s hso (by omega) s t x y InSubtree.self ht htb hsx hsy
        · exact hmid s (by have := hcs.ge; omega) (by omega) (by omega)
            s t x y InSubtree.self ht htb hsx hsy
      · exact ihc s (hos.ge) (by omega) s t x y InSubtree.self ht htb hsx hsy
    intro j hj1 hj2
    by_cases hjn : j = r
    · subst j; exact hroot
    · by_cases hjc : j < r * 2 + 1 + 1
      · exact hmid j (by omega) hjc hj2
      · exact ihc j (by omega) hj2
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab hlen h
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
    intro j hj1 hj2
    by_cases hjn : j = r
    · subst j
      intro s t x y hs ht htb hsx hsy
      rcases InSubtree.child_or2 hs with hsr | hcs | hos
      rw [hsr] at hs ht hsx
      · rcases (by rcases ht with h | h <;> omega : t = r * 2 + 1 ∨ t = r * 2 + 1 + 1) with rfl | rfl
        · have hx : x = a := Option.some.inj (hsx.symm.trans hro)
          have hy : y = wc := Option.some.inj (hsy.symm.trans hwc)
          rw [hx, hy]
          have hc1 := slt_lt_of_true hcand
          have hn1 := slt_nlt_of_notrue hab
          exact slt_of_nlt (by omega)
        · have hx : x = a := Option.some.inj (hsx.symm.trans hro)
          have hy : y = wo := Option.some.inj (hsy.symm.trans hwo)
          rw [hx, hy]; exact (by simpa using hab)
      · exact h (r * 2 + 1) (by omega) hcb s t x y hcs ht htb hsx hsy
      · exact h (r * 2 + 1 + 1) (by omega) hob s t x y hos ht htb hsx hsy
    · exact h j (by omega) hj2
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih hlen h
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
    have hlen' : bound ≤ ((l.set r wc).set (r * 2 + 1) a).length := by
      rwa [List.length_set, List.length_set]
    have hpres : HeapAbove bound (r * 2 + 1 + 1)
        ((l.set r wc).set (r * 2 + 1) a) := by
      intro j hj1 hj2
      have hrj : ¬ InSubtree j r := by
        intro hr; have := hr.ge; omega
      have hcj : ¬ InSubtree j (r * 2 + 1) := by
        intro hc'; have := hc'.ge; omega
      exact HeapAt_set_ne hcj
        (HeapAt_set_ne hrj (h j (by omega) hj2))
    have ihc := ih hlen' hpres
    have hroot : HeapAt bound r
        (siftDown bound (r * 2 + 1) ((l.set r wc).set (r * 2 + 1) a)) := by
      have hRr : (siftDown bound (r * 2 + 1)
          ((l.set r wc).set (r * 2 + 1) a))[r]? = some wc := by
        have hnr : ¬ InSubtree (r * 2 + 1) r := by
          intro hr; have := hr.ge; omega
        rw [siftDown_get_outside _ _ _ _ hnr]
        have hne : r * 2 + 1 ≠ r := by omega
        have hlt : r < l.length := lt_length_of_getElem?_eq_some hro
        rw [List.getElem?_set_ne hne]
        rw [List.getElem?_set_self hlt]
      intro s t x y hs ht htb hsx hsy
      rcases InSubtree.child_or2 hs with hsr | hcs | hos
      rw [hsr] at hs ht hsx
      · have hxw : x = wc := Option.some.inj (hsx.symm.trans hRr)
        rw [hxw]
        rcases (by rcases ht with h | h <;> omega : t = r * 2 + 1 ∨ t = r * 2 + 1 + 1) with rfl | rfl
        · obtain ⟨t', ht', htb', hl'⟩ :=
            siftDown_mem_region bound (r * 2 + 1)
              ((l.set r wc).set (r * 2 + 1) a) (r * 2 + 1) y
              InSubtree.self htb hsy
          by_cases heo : t' = r * 2 + 1
          · rw [heo] at hl'
            have hswa : ((l.set r wc).set (r * 2 + 1) a)[r * 2 + 1]? =
                some a :=
              List.getElem?_set_self (by
                rw [List.length_set]
                exact lt_length_of_getElem?_eq_some hwc)
            have hya : a = y := Option.some.inj (hswa.symm.trans hl')
            rw [← hya]
            exact slt_of_nlt (by have := slt_lt_of_true hab; omega)
          · have htr : t' ≠ r := by
              intro e
              have hge := ht'.ge
              omega
            have hswl : l[t']? = some y := by
              have e1 : r ≠ t' := fun e => htr e.symm
              have e2 : r * 2 + 1 ≠ t' := fun e => heo e.symm
              rw [List.getElem?_set_ne e2] at hl'
              rw [List.getElem?_set_ne e1] at hl'
              exact hl'
            exact HeapAt_all (h (r * 2 + 1) (by omega) hcb) hwc ht' htb' hswl
        · have hno : ¬ InSubtree (r * 2 + 1) (r * 2 + 1 + 1) :=
            not_mem_sibling rfl rfl
          have hRo : (siftDown bound (r * 2 + 1)
              ((l.set r wc).set (r * 2 + 1) a))[r * 2 + 1 + 1]? = some wo := by
            rw [siftDown_get_outside _ _ _ _ hno]
            have e1 : r ≠ r * 2 + 1 + 1 := by omega
            have e2 : r * 2 + 1 ≠ r * 2 + 1 + 1 := by omega
            rw [List.getElem?_set_ne e2]
            rw [List.getElem?_set_ne e1]
            exact hwo
          have hyw : y = wo := Option.some.inj (hsy.symm.trans hRo)
          rw [hyw]
          exact (by simpa using hcand)
      · exact ihc s (hcs.ge) (by omega) s t x y InSubtree.self ht htb hsx hsy
      · exact ihc s (by have := hos.ge; omega) (by omega)
          s t x y InSubtree.self ht htb hsx hsy
    have hmid : ∀ j, r < j → j < r * 2 + 1 → j < bound →
        HeapAt bound j
          (siftDown bound (r * 2 + 1) ((l.set r wc).set (r * 2 + 1) a)) := by
      intro j hjr hjc hjb s t x y hs ht htb hsx hsy
      rcases Nat.lt_or_ge s (r * 2 + 1) with hlt | hge
      · have hns : ¬ InSubtree (r * 2 + 1) s := by
          intro hs'; have := hs'.ge; omega
        have hnt : ¬ InSubtree (r * 2 + 1) t := by
          intro ht'
          exact hns (middle_child_closed (Or.inl (by omega)) hjr hjc hs ht' ht)
        rw [siftDown_get_outside _ _ _ _ hns] at hsx
        rw [siftDown_get_outside _ _ _ _ hnt] at hsy
        have hSW : HeapAt bound j ((l.set r wc).set (r * 2 + 1) a) := by
          apply HeapAt_set_ne
            (not_mem_child_above (Or.inl rfl) hjr hjc)
          apply HeapAt_set_ne (by intro hr'; have := hr'.ge; omega)
          exact h j (by omega) hjb
        exact hSW s t x y hs ht htb hsx hsy
      · exact ihc s hge (by omega) s t x y InSubtree.self ht htb hsx hsy
    intro j hj1 hj2
    by_cases hjn : j = r
    · subst j; exact hroot
    · by_cases hjc : j < r * 2 + 1
      · exact hmid j (by omega) hjc hj2
      · exact ihc j (by omega) hj2
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab hlen h
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
    intro j hj1 hj2
    by_cases hjn : j = r
    · subst j
      intro s t x y hs ht htb hsx hsy
      rcases InSubtree.child_or2 hs with hsr | hcs | hos
      rw [hsr] at hs ht hsx
      · rcases (by rcases ht with h | h <;> omega : t = r * 2 + 1 ∨ t = r * 2 + 1 + 1) with rfl | rfl
        · have hx : x = a := Option.some.inj (hsx.symm.trans hro)
          have hy : y = wc := Option.some.inj (hsy.symm.trans hwc)
          rw [hx, hy]; exact (by simpa using hab)
        · have hx : x = a := Option.some.inj (hsx.symm.trans hro)
          have hy : y = wo := Option.some.inj (hsy.symm.trans hwo)
          rw [hx, hy]
          have hcand' : wc.slt wo = false := by simpa using hcand
          have hab' : a.slt wc = false := by simpa using hab
          exact VecSelectionSort.slt_ge_trans hab' hcand'
      · exact h (r * 2 + 1) (by omega) hcb s t x y hcs ht htb hsx hsy
      · exact h (r * 2 + 1 + 1) (by omega) hob s t x y hos ht htb hsx hsy
    · exact h j (by omega) hj2
  · intro r l hcb wc hwc hob wo hwo hro hlen h
    have hlt : r < l.length := by omega
    obtain ⟨w, hw⟩ := getElem?_some_of_lt_length (l := l) (k := r) hlt
    rw [hro] at hw
    simp at hw
  · intro r l hcb wc hwc hob hwo hlen h
    have hlt : r * 2 + 1 + 1 < l.length := by omega
    obtain ⟨w, hw⟩ := getElem?_some_of_lt_length (l := l)
      (k := r * 2 + 1 + 1) hlt
    rw [hwo] at hw
    simp at hw
  · intro r l hcb wc hwc hob a hro hab ih hlen h
    unfold siftDown
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
      Bool.false_eq_true]
    have hlen' : bound ≤ ((l.set r wc).set (r * 2 + 1) a).length := by
      rwa [List.length_set, List.length_set]
    have hpres : HeapAbove bound (r * 2 + 1 + 1)
        ((l.set r wc).set (r * 2 + 1) a) := by
      intro j hj1 hj2
      have hrj : ¬ InSubtree j r := by
        intro hr; have := hr.ge; omega
      have hcj : ¬ InSubtree j (r * 2 + 1) := by
        intro hc'; have := hc'.ge; omega
      exact HeapAt_set_ne hcj
        (HeapAt_set_ne hrj (h j (by omega) hj2))
    have ihc := ih hlen' hpres
    have hroot : HeapAt bound r
        (siftDown bound (r * 2 + 1) ((l.set r wc).set (r * 2 + 1) a)) := by
      have hRr : (siftDown bound (r * 2 + 1)
          ((l.set r wc).set (r * 2 + 1) a))[r]? = some wc := by
        have hnr : ¬ InSubtree (r * 2 + 1) r := by
          intro hr; have := hr.ge; omega
        rw [siftDown_get_outside _ _ _ _ hnr]
        have hne : r * 2 + 1 ≠ r := by omega
        have hlt : r < l.length := lt_length_of_getElem?_eq_some hro
        rw [List.getElem?_set_ne hne]
        rw [List.getElem?_set_self hlt]
      intro s t x y hs ht htb hsx hsy
      rcases InSubtree.child_or2 hs with hsr | hcs | hos
      rw [hsr] at hs ht hsx
      · have hxw : x = wc := Option.some.inj (hsx.symm.trans hRr)
        rw [hxw]
        rcases (by rcases ht with h | h <;> omega : t = r * 2 + 1 ∨ t = r * 2 + 1 + 1) with rfl | rfl
        · obtain ⟨t', ht', htb', hl'⟩ :=
            siftDown_mem_region bound (r * 2 + 1)
              ((l.set r wc).set (r * 2 + 1) a) (r * 2 + 1) y
              InSubtree.self htb hsy
          by_cases heo : t' = r * 2 + 1
          · rw [heo] at hl'
            have hswa : ((l.set r wc).set (r * 2 + 1) a)[r * 2 + 1]? =
                some a :=
              List.getElem?_set_self (by
                rw [List.length_set]
                exact lt_length_of_getElem?_eq_some hwc)
            have hya : a = y := Option.some.inj (hswa.symm.trans hl')
            rw [← hya]
            exact slt_of_nlt (by have := slt_lt_of_true hab; omega)
          · have htr : t' ≠ r := by
              intro e
              have hge := ht'.ge
              omega
            have hswl : l[t']? = some y := by
              have e1 : r ≠ t' := fun e => htr e.symm
              have e2 : r * 2 + 1 ≠ t' := fun e => heo e.symm
              rw [List.getElem?_set_ne e2] at hl'
              rw [List.getElem?_set_ne e1] at hl'
              exact hl'
            exact HeapAt_all (h (r * 2 + 1) (by omega) hcb) hwc ht' htb' hswl
        · exact False.elim (by omega)
      · exact ihc s (hcs.ge) (by omega) s t x y InSubtree.self ht htb hsx hsy
      · have hso := hos.ge
        exact False.elim (by omega)
    have hmid : ∀ j, r < j → j < r * 2 + 1 → j < bound →
        HeapAt bound j
          (siftDown bound (r * 2 + 1) ((l.set r wc).set (r * 2 + 1) a)) := by
      intro j hjr hjc hjb s t x y hs ht htb hsx hsy
      rcases Nat.lt_or_ge s (r * 2 + 1) with hlt | hge
      · have hns : ¬ InSubtree (r * 2 + 1) s := by
          intro hs'; have := hs'.ge; omega
        have hnt : ¬ InSubtree (r * 2 + 1) t := by
          intro ht'
          exact hns (middle_child_closed (Or.inl (by omega)) hjr hjc hs ht' ht)
        rw [siftDown_get_outside _ _ _ _ hns] at hsx
        rw [siftDown_get_outside _ _ _ _ hnt] at hsy
        have hSW : HeapAt bound j ((l.set r wc).set (r * 2 + 1) a) := by
          apply HeapAt_set_ne
            (not_mem_child_above (Or.inl rfl) hjr hjc)
          apply HeapAt_set_ne (by intro hr'; have := hr'.ge; omega)
          exact h j (by omega) hjb
        exact hSW s t x y hs ht htb hsx hsy
      · exact ihc s hge (by omega) s t x y InSubtree.self ht htb hsx hsy
    intro j hj1 hj2
    by_cases hjn : j = r
    · subst j; exact hroot
    · by_cases hjc : j < r * 2 + 1
      · exact hmid j (by omega) hjc hj2
      · exact ihc j (by omega) hj2
  · intro r l hcb wc hwc hob a hro hab hlen h
    unfold siftDown
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
      Bool.false_eq_true]
    intro j hj1 hj2
    by_cases hjn : j = r
    · subst j
      intro s t x y hs ht htb hsx hsy
      rcases InSubtree.child_or2 hs with hsr | hcs | hos
      rw [hsr] at hs ht hsx
      · rcases (by rcases ht with h | h <;> omega : t = r * 2 + 1 ∨ t = r * 2 + 1 + 1) with rfl | rfl
        · have hx : x = a := Option.some.inj (hsx.symm.trans hro)
          have hy : y = wc := Option.some.inj (hsy.symm.trans hwc)
          rw [hx, hy]; exact (by simpa using hab)
        · exact False.elim (by omega)
      · exact h (r * 2 + 1) (by omega) hcb s t x y hcs ht htb hsx hsy
      · have hso := hos.ge
        exact False.elim (by omega)
    · exact h j (by omega) hj2
  · intro r l hcb wc hwc hob hro hlen h
    have hlt : r < l.length := by omega
    obtain ⟨w, hw⟩ := getElem?_some_of_lt_length (l := l) (k := r) hlt
    rw [hro] at hw
    simp at hw
  · intro r l hcb hwc hlen h
    have hlt : r * 2 + 1 < l.length := by omega
    obtain ⟨w, hw⟩ := getElem?_some_of_lt_length (l := l)
      (k := r * 2 + 1) hlt
    rw [hwc] at hw
    simp at hw
  · intro r l hcb hlen h
    unfold siftDown
    simp only [hcb, dite_true, dite_false, Bool.false_eq_true]
    intro j hj1 hj2
    by_cases hjn : j = r
    · subst j
      intro s t x y hs ht htb hsx hsy
      have hsn := hs.ge
      rcases ht with rfl | rfl <;> omega
    · exact h j (by omega) hj2


/-- Sifting with bound never touches positions at or above the bound. -/
theorem siftDown_get_ge (bound r : Nat) (l : List (BitVec 32))
    (t : Nat) (hge : bound ≤ t) :
    (siftDown bound r l)[t]? = l[t]? := by
  refine siftDown.induct bound
    (fun r l => bound ≤ t → (siftDown bound r l)[t]? = l[t]?)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ hge
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih hge
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
    have hne1 : r * 2 + 1 + 1 ≠ t := by omega
    have hne2 : r ≠ t := by omega
    rw [ih hge, List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab hge
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih hge
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
    have hne1 : r * 2 + 1 ≠ t := by omega
    have hne2 : r ≠ t := by omega
    rw [ih hge, List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab hge
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob wo hwo hro hge
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, hro, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob hwo hge
    unfold siftDown
    simp only [hcb, hwc, hob, hwo, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob a hro hab ih hge
    unfold siftDown
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
      Bool.false_eq_true]
    have hne1 : r * 2 + 1 ≠ t := by omega
    have hne2 : r ≠ t := by omega
    rw [ih hge, List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
  · intro r l hcb wc hwc hob a hro hab hge
    unfold siftDown
    simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb wc hwc hob hro hge
    unfold siftDown
    simp only [hcb, hwc, hob, hro, dite_true, dite_false,
      Bool.false_eq_true]
  · intro r l hcb hwc hge
    unfold siftDown
    simp only [hcb, hwc, dite_true, dite_false, Bool.false_eq_true]
  · intro r l hcb hge
    unfold siftDown
    simp only [hcb, dite_true, dite_false, Bool.false_eq_true]

/-- Heapify establishes the heap: counting down from `i`, each
    `siftDown` preserves heap-above, so position `0` ends ordered.
    (Plain `Nat` induction; lengths survive via `siftDown_perm`.) -/
theorem heapifyDown_heap (bound : Nat) : ∀ (i : Nat) (v : List (BitVec 32)),
    bound ≤ v.length → HeapAbove bound i v →
    HeapAbove bound 0 (heapifyDown bound i v) := by
  intro i
  induction i with
  | zero => intro v hlen h; simpa [heapifyDown] using h
  | succ n ih =>
    intro v hlen h
    simp only [heapifyDown]
    have hlen' : bound ≤ (siftDown bound n v).length := by
      have hpl := (siftDown_perm bound n v).length_eq
      omega
    have hs := sift_step bound n v hlen h
    exact ih (siftDown bound n v) hlen' hs

/-- Heapify from the top establishes `IsHeap` (the `i = length`
    premise is vacuous: no `j ≥ length` sits below `bound`). -/
theorem heapifyDown_isHeap (v : List (BitVec 32)) :
    IsHeap v.length (heapifyDown v.length v.length v) := by
  apply heapifyDown_heap
  · exact Nat.le_refl _
  · intro j hj1 hj2
    omega

/-- `(root * 2 + 1).toNat` is exact below `2^63`. -/
theorem bv64_child_toNat (root : BitVec 64) (rn : Nat)
    (h : root.toNat = rn) (hlt : rn < 2 ^ 63) :
    (root * 2 + 1).toNat = rn * 2 + 1 := by
  have h2 : (2 : BitVec 64).toNat = 2 := by decide
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_mul, h, h2, h1,
    Nat.mod_eq_of_lt (by omega : rn * 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : rn * 2 + 1 < 2 ^ 64)]

/-- `(child + 1).toNat` is exact when it fits in 64 bits. -/
theorem bv64_other_toNat (child : BitVec 64) (cn : Nat)
    (h : child.toNat = cn) (hlt : cn + 1 < 2 ^ 64) :
    (child + 1).toNat = cn + 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  rw [BitVec.toNat_add, h, h1, Nat.mod_eq_of_lt hlt]

/-- `(i - 1).toNat` for a positive cursor. -/
theorem bv64_sub1_toNat (i : BitVec 64) (inn : Nat)
    (h : i.toNat = inn) (hpos : 0 < inn) :
    (i - 1).toNat = inn - 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  have hlt : inn < 2 ^ 64 := by
    have hi := i.isLt
    omega
  rw [BitVec.toNat_sub, h, h1]
  omega

/-- `ult` reflects `toNat` order (via `ult_eq_decide`). -/
theorem bv64_ult_true {a b : BitVec 64} (h : a.toNat < b.toNat) :
    a.ult b = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  exact h

theorem bv64_ult_false {a b : BitVec 64} (h : ¬ a.toNat < b.toNat) :
    a.ult b = false := by
  rw [BitVec.ult_eq_decide]
  simpa using h

/-- A zero cursor tests false against `!= 0`. -/
theorem bv64_ne_zero_false {i : BitVec 64} (h : i.toNat = 0) :
    (i != 0) = false := by
  have h0 : (0 : BitVec 64).toNat = 0 := by decide
  have hi : i = 0 := BitVec.toNat_inj.mp (h.trans h0.symm)
  rw [hi]
  decide

/-- A nonzero cursor tests true against `!= 0`. -/
theorem bv64_ne_zero_true {i : BitVec 64} (h : i.toNat ≠ 0) :
    (i != 0) = true := by
  rw [bne_iff_ne]
  intro heq
  rw [heq] at h
  exact h (by decide : (0 : BitVec 64).toNat = 0)

/-- A missed read contradicts the length bound. -/
theorem len_le_of_getElem?_eq_none {l : List (BitVec 32)} {i : Nat}
    (h : l[i]? = none) : l.length ≤ i := by
  by_cases hc : i < l.length
  · obtain ⟨x, hx⟩ := getElem?_some_of_lt_length hc
    rw [hx] at h
    simp at h
  · omega

/-- The fuel-threaded sift computes the pure sift: some fuel always
    suffices (mirror induction; missed reads are impossible under
    `bn ≤ length`, and `2^63` keeps every cursor exact). -/
theorem siftFwd_exists (bn rn : Nat) (v : List (BitVec 32))
    (bound root : BitVec 64) (hbn : bound.toNat = bn)
    (hrn : root.toNat = rn) (hlt : rn < bn) (hbig : bn ≤ 2 ^ 63)
    (hlen : bn ≤ v.length) :
    ∃ F, ∀ F', F ≤ F' →
      siftFwd F' v bound root = .ok (siftDown bn rn v) := by
  refine siftDown.induct bn
    (fun rn v => ∀ (root : BitVec 64), root.toNat = rn → rn < bn →
      bn ≤ 2 ^ 63 → bn ≤ v.length →
      ∃ F, ∀ F', F ≤ F' →
      siftFwd F' v bound root = .ok (siftDown bn rn v))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rn v root hrn hlt hbig hlen
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih
      root hrn hlt hbig hlen
    have hchild : (root * 2 + 1).toNat = r * 2 + 1 :=
      bv64_child_toNat root r hrn (by omega)
    have hother : (root * 2 + 1 + 1).toNat = r * 2 + 1 + 1 :=
      bv64_other_toNat (root * 2 + 1) (r * 2 + 1) hchild (by omega)
    have hcu : (root * 2 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1).toNat < bound.toNat := by
        rw [hchild, hbn]; exact hcb
      exact bv64_ult_true hlt'
    have hou : (root * 2 + 1 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1 + 1).toNat < bound.toNat := by
        rw [hother, hbn]; exact hob
      exact bv64_ult_true hlt'
    have hmir : siftDown bn r l =
        siftDown bn (r * 2 + 1 + 1) ((l.set r wo).set (r * 2 + 1 + 1) a) := by
      conv => lhs; unfold siftDown
      simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
        Bool.false_eq_true]
    obtain ⟨F0, hF0⟩ := ih (root * 2 + 1 + 1) hother hob hbig
      (by rwa [List.length_set, List.length_set])
    refine ⟨F0.succ, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    have hrec := hF0 F'' (by omega)
    rw [hmir]
    unfold siftFwd
    simp only [hcu, hou, hchild, hother, hwc, hwo, hrn, hcand, hro, hab, hrec, if_true, if_false, Bool.false_eq_true]
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab
      root hrn hlt hbig hlen
    have hchild : (root * 2 + 1).toNat = r * 2 + 1 :=
      bv64_child_toNat root r hrn (by omega)
    have hother : (root * 2 + 1 + 1).toNat = r * 2 + 1 + 1 :=
      bv64_other_toNat (root * 2 + 1) (r * 2 + 1) hchild (by omega)
    have hcu : (root * 2 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1).toNat < bound.toNat := by
        rw [hchild, hbn]; exact hcb
      exact bv64_ult_true hlt'
    have hou : (root * 2 + 1 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1 + 1).toNat < bound.toNat := by
        rw [hother, hbn]; exact hob
      exact bv64_ult_true hlt'
    have hmir : siftDown bn r l = l := by
      conv => lhs; unfold siftDown
      simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
        Bool.false_eq_true]
    refine ⟨Nat.succ Nat.zero, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    rw [hmir]
    unfold siftFwd
    simp only [hcu, hou, hchild, hother, hwc, hwo, hrn, hcand, hro, hab, if_true, if_false, Bool.false_eq_true]
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab ih
      root hrn hlt hbig hlen
    have hchild : (root * 2 + 1).toNat = r * 2 + 1 :=
      bv64_child_toNat root r hrn (by omega)
    have hother : (root * 2 + 1 + 1).toNat = r * 2 + 1 + 1 :=
      bv64_other_toNat (root * 2 + 1) (r * 2 + 1) hchild (by omega)
    have hcu : (root * 2 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1).toNat < bound.toNat := by
        rw [hchild, hbn]; exact hcb
      exact bv64_ult_true hlt'
    have hou : (root * 2 + 1 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1 + 1).toNat < bound.toNat := by
        rw [hother, hbn]; exact hob
      exact bv64_ult_true hlt'
    have hmir : siftDown bn r l =
        siftDown bn (r * 2 + 1) ((l.set r wc).set (r * 2 + 1) a) := by
      conv => lhs; unfold siftDown
      simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
        Bool.false_eq_true]
    obtain ⟨F0, hF0⟩ := ih (root * 2 + 1) hchild hcb hbig
      (by rwa [List.length_set, List.length_set])
    refine ⟨F0.succ, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    have hrec := hF0 F'' (by omega)
    rw [hmir]
    unfold siftFwd
    simp only [hcu, hou, hchild, hother, hwc, hwo, hrn, hcand, hro, hab, hrec, if_true, if_false, Bool.false_eq_true]
  · intro r l hcb wc hwc hob wo hwo a hro hcand hab
      root hrn hlt hbig hlen
    have hchild : (root * 2 + 1).toNat = r * 2 + 1 :=
      bv64_child_toNat root r hrn (by omega)
    have hother : (root * 2 + 1 + 1).toNat = r * 2 + 1 + 1 :=
      bv64_other_toNat (root * 2 + 1) (r * 2 + 1) hchild (by omega)
    have hcu : (root * 2 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1).toNat < bound.toNat := by
        rw [hchild, hbn]; exact hcb
      exact bv64_ult_true hlt'
    have hou : (root * 2 + 1 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1 + 1).toNat < bound.toNat := by
        rw [hother, hbn]; exact hob
      exact bv64_ult_true hlt'
    have hmir : siftDown bn r l = l := by
      conv => lhs; unfold siftDown
      simp only [hcb, hwc, hob, hwo, hro, hcand, hab, dite_true, dite_false,
        Bool.false_eq_true]
    refine ⟨Nat.succ Nat.zero, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    rw [hmir]
    unfold siftFwd
    simp only [hcu, hou, hchild, hother, hwc, hwo, hrn, hcand, hro, hab, if_true, if_false, Bool.false_eq_true]
  · intro r l hcb wc hwc hob wo hwo hro
      root hrn hlt hbig hlen
    have hc := len_le_of_getElem?_eq_none hro
    omega
  · intro r l hcb wc hwc hob hwo
      root hrn hlt hbig hlen
    have hc := len_le_of_getElem?_eq_none hwo
    omega
  · intro r l hcb wc hwc hob a hro hab ih
      root hrn hlt hbig hlen
    have hchild : (root * 2 + 1).toNat = r * 2 + 1 :=
      bv64_child_toNat root r hrn (by omega)
    have hother : (root * 2 + 1 + 1).toNat = r * 2 + 1 + 1 :=
      bv64_other_toNat (root * 2 + 1) (r * 2 + 1) hchild (by omega)
    have hcu : (root * 2 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1).toNat < bound.toNat := by
        rw [hchild, hbn]; exact hcb
      exact bv64_ult_true hlt'
    have hou : (root * 2 + 1 + 1).ult bound = false := by
      have hlt' : ¬ (root * 2 + 1 + 1).toNat < bound.toNat := by
        rw [hother, hbn]; exact hob
      exact bv64_ult_false hlt'
    have hmir : siftDown bn r l =
        siftDown bn (r * 2 + 1) ((l.set r wc).set (r * 2 + 1) a) := by
      conv => lhs; unfold siftDown
      simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
        Bool.false_eq_true]
    obtain ⟨F0, hF0⟩ := ih (root * 2 + 1) hchild hcb hbig
      (by rwa [List.length_set, List.length_set])
    refine ⟨F0.succ, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    have hrec := hF0 F'' (by omega)
    rw [hmir]
    unfold siftFwd
    simp only [hcu, hou, hchild, hwc, hrn, hro, hab, hrec, if_true, if_false, Bool.false_eq_true]
  · intro r l hcb wc hwc hob a hro hab
      root hrn hlt hbig hlen
    have hchild : (root * 2 + 1).toNat = r * 2 + 1 :=
      bv64_child_toNat root r hrn (by omega)
    have hother : (root * 2 + 1 + 1).toNat = r * 2 + 1 + 1 :=
      bv64_other_toNat (root * 2 + 1) (r * 2 + 1) hchild (by omega)
    have hcu : (root * 2 + 1).ult bound = true := by
      have hlt' : (root * 2 + 1).toNat < bound.toNat := by
        rw [hchild, hbn]; exact hcb
      exact bv64_ult_true hlt'
    have hou : (root * 2 + 1 + 1).ult bound = false := by
      have hlt' : ¬ (root * 2 + 1 + 1).toNat < bound.toNat := by
        rw [hother, hbn]; exact hob
      exact bv64_ult_false hlt'
    have hmir : siftDown bn r l = l := by
      conv => lhs; unfold siftDown
      simp only [hcb, hwc, hob, hro, hab, dite_true, dite_false,
        Bool.false_eq_true]
    refine ⟨Nat.succ Nat.zero, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    rw [hmir]
    unfold siftFwd
    simp only [hcu, hou, hchild, hwc, hrn, hro, hab, if_true, if_false, Bool.false_eq_true]
  · intro r l hcb wc hwc hob hro
      root hrn hlt hbig hlen
    have hc := len_le_of_getElem?_eq_none hro
    omega
  · intro r l hcb hwc
      root hrn hlt hbig hlen
    have hc := len_le_of_getElem?_eq_none hwc
    omega
  · intro r l hcb
      root hrn hlt hbig hlen
    have hchild : (root * 2 + 1).toNat = r * 2 + 1 :=
      bv64_child_toNat root r hrn (by omega)
    have hcu : (root * 2 + 1).ult bound = false := by
      have hlt' : ¬ (root * 2 + 1).toNat < bound.toNat := by
        rw [hchild, hbn]; exact hcb
      exact bv64_ult_false hlt'
    have hmir : siftDown bn r l = l := by
      conv => lhs; unfold siftDown
      simp only [hcb, dite_true, dite_false, Bool.false_eq_true]
    refine ⟨Nat.succ Nat.zero, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    rw [hmir]
    unfold siftFwd
    simp only [hcu, if_true, if_false, Bool.false_eq_true]

/-- The fuel-threaded heapify computes the pure heapify: some fuel
    always suffices (plain induction on `i`; the sift at each level
    takes the uniform-fuel simulation). -/
theorem heapifyFwd_exists (bn : Nat) : ∀ (i : Nat) (v : List (BitVec 32))
    (n ni : BitVec 64), n.toNat = bn → ni.toNat = i → i ≤ bn →
    bn ≤ v.length → v.length ≤ 2 ^ 63 →
    ∃ F, ∀ F', F ≤ F' → heapifyFwd F' v n ni = .ok (heapifyDown bn i v) := by
  intro i
  induction i with
  | zero =>
    intro v n ni hbn hni hle hlen hbig
    have hmir : heapifyDown bn 0 v = v := by simp only [heapifyDown]
    have hni0 : (ni != 0) = false := bv64_ne_zero_false hni
    refine ⟨Nat.succ Nat.zero, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    rw [hmir]
    unfold heapifyFwd
    simp only [hni0, if_true, if_false, Bool.false_eq_true]
  | succ i ih =>
    intro v n ni hbn hni hle hlen hbig
    have hsub : (ni - 1).toNat = i := by
      have h1 := bv64_sub1_toNat ni (i + 1) hni (by omega)
      omega
    obtain ⟨Fs, hFs⟩ := siftFwd_exists bn i v n (ni - 1) hbn hsub
      (by omega) (by omega) hlen
    have hlen' : bn ≤ (siftDown bn i v).length := by
      have hpl := (siftDown_perm bn i v).length_eq
      omega
    have hbig' : (siftDown bn i v).length ≤ 2 ^ 63 := by
      have hpl := (siftDown_perm bn i v).length_eq
      omega
    obtain ⟨Fr, hFr⟩ := ih (siftDown bn i v) n (ni - 1) hbn hsub
      (by omega) hlen' hbig'
    have hmir : heapifyDown bn (i + 1) v =
        heapifyDown bn i (siftDown bn i v) := by
      simp only [heapifyDown]
    refine ⟨Fs + Fr + 1, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    have hsift := hFs F'' (by omega)
    have hrest := hFr F'' (by omega)
    have hni1 : (ni != 0) = true := bv64_ne_zero_true (by omega)
    rw [hmir]
    unfold heapifyFwd
    simp only [hni1, hsift, hrest, if_true, if_false, Bool.false_eq_true]

/-- Index-wise ascending implies `List.Pairwise` ascending. -/
theorem pairwise_of_indexed : ∀ (w : List (BitVec 32)),
    (∀ k1 k2 z1 z2, k1 < k2 → k2 < w.length →
      w[k1]? = some z1 → w[k2]? = some z2 → z2.slt z1 = false) →
    List.Pairwise (fun a b => b.slt a = false) w := by
  intro w
  induction w with
  | nil => intro; exact List.Pairwise.nil
  | cons hd tl ih =>
    intro hall
    apply List.Pairwise.cons
    · intro y hy
      obtain ⟨n, hnlt, heq⟩ := List.mem_iff_getElem.mp hy
      have hn : tl[n]? = some y := by
        rw [List.getElem?_eq_getElem hnlt, heq]
      exact hall 0 (n + 1) hd y (by omega)
        (by have h := hnlt; simpa using Nat.succ_lt_succ h)
        rfl (by simpa using hn)
    · apply ih
      intro k1 k2 z1 z2 h12 hlen h1 h2
      exact hall (k1 + 1) (k2 + 1) z1 z2 (by omega)
        (by simpa using hlen) (by simpa using h1) (by simpa using h2)

/-- Extract invariant: heap on `[0, l)`, every heap value below the
    sorted suffix `[l, len)`, suffix pairwise ascending (all in the
    `¬(later < earlier)` GE-shape matching `HeapAt`). -/
def ExtractInv (l : Nat) (w : List (BitVec 32)) : Prop :=
  l ≤ w.length ∧
  HeapAbove l 0 w ∧
  (∀ i y, i < l → w[i]? = some y →
    ∀ k z, l ≤ k → k < w.length → w[k]? = some z → z.slt y = false) ∧
  (∀ k1 k2 z1 z2, l ≤ k1 → k1 < k2 → k2 < w.length →
    w[k1]? = some z1 → w[k2]? = some z2 → z2.slt z1 = false)

/-- One extract step preserves the invariant: swapping the root
    max into place and re-sifting the shrunk heap. Shared by the
    pure sortedness proof and the fuel-threaded bridge. -/
theorem extractDown_step_inv (F : Nat) (v : List (BitVec 32))
    (a b : BitVec 32) (hbl : v[F]? = some b) (ha0 : v[0]? = some a)
    (hinv : ExtractInv (F + 1) v) :
    ExtractInv F (siftDown F 0 ((v.set 0 b).set F a)) := by
  obtain ⟨hlen, hheap, hle, hsorted⟩ := hinv
  have hwslen : ((v.set 0 b).set F a).length = v.length := by
    rw [List.length_set, List.length_set]
  have hlen_eq :
      (siftDown F 0 ((v.set 0 b).set F a)).length = v.length := by
    have hpl := (siftDown_perm F 0 ((v.set 0 b).set F a)).length_eq
    omega
  have hswap1 : HeapAbove F 1 ((v.set 0 b).set F a) := by
    intro j hj1 hjF
    have hbase : HeapAt (F + 1) j v := hheap j (by omega) (by omega)
    intro s t x y hs ht htb hsx hsy
    have hsge := hs.ge
    have ht2 := ht
    have hFs : s ≠ F := by
      intro e; subst e
      rcases ht2 with ht2 | ht2 <;> omega
    have hs0 : s ≠ 0 := by omega
    have ht0 : t ≠ 0 := by rcases ht2 with ht2 | ht2 <;> omega
    have htF : t ≠ F := by omega
    rw [List.getElem?_set_ne (Ne.symm hFs),
      List.getElem?_set_ne (Ne.symm hs0)] at hsx
    rw [List.getElem?_set_ne (Ne.symm htF),
      List.getElem?_set_ne (Ne.symm ht0)] at hsy
    exact hbase s t x y hs ht (by omega) hsx hsy
  have hheap1 : HeapAbove F 0
      (siftDown F 0 ((v.set 0 b).set F a)) :=
    sift_step F 0 ((v.set 0 b).set F a) (by omega) hswap1
  have hmax : ∀ jj xx, jj < F + 1 → v[jj]? = some xx → a.slt xx = false := by
    intro jj xx hjb hx
    exact HeapAt_all (hheap 0 (Nat.le_refl 0) (by omega)) ha0
      (mem_subtree_zero jj) hjb hx
  have hws_self : ((v.set 0 b).set F a)[F]? = some a :=
    List.getElem?_set_self (by rw [List.length_set]; omega)
  have hws_gt : ∀ k z, F < k → k < v.length →
      ((v.set 0 b).set F a)[k]? = some z → v[k]? = some z := by
    intro k z hkF hkv hkz
    have h1 : k ≠ F := by omega
    have h2 : k ≠ 0 := by omega
    rw [List.getElem?_set_ne (Ne.symm h1),
      List.getElem?_set_ne (Ne.symm h2)] at hkz
    exact hkz
  have hprov : ∀ i y, i < F →
      (siftDown F 0 ((v.set 0 b).set F a))[i]? = some y →
      y = b ∨ (∃ t', t' ≠ 0 ∧ t' < F + 1 ∧ v[t']? = some y) := by
    intro i y hiF hy
    obtain ⟨t', ht', htb', hsw⟩ :=
      siftDown_mem_region F 0 ((v.set 0 b).set F a) i y
        (mem_subtree_zero i) hiF hy
    by_cases ht0 : t' = 0
    · left
      subst ht0
      have hF0 : F ≠ (0 : Nat) := by omega
      have hb0 : ((v.set 0 b).set F a)[0]? = some b := by
        rw [List.getElem?_set_ne hF0,
          List.getElem?_set_self (by omega)]
      exact Option.some.inj (hsw.symm.trans hb0)
    · right
      have h1 : t' ≠ F := by omega
      have h2 : v[t']? = some y := by
        rw [List.getElem?_set_ne (Ne.symm h1),
          List.getElem?_set_ne (Ne.symm ht0)] at hsw
        exact hsw
      exact ⟨t', ht0, by omega, h2⟩
  have hle1 : ∀ i y, i < F →
      (siftDown F 0 ((v.set 0 b).set F a))[i]? = some y →
      ∀ k z, F ≤ k →
      k < (siftDown F 0 ((v.set 0 b).set F a)).length →
      (siftDown F 0 ((v.set 0 b).set F a))[k]? = some z →
      z.slt y = false := by
    intro i y hiF hy k z hkF hkw hkz
    rw [siftDown_get_ge F 0 _ k hkF] at hkz
    have hkv : k < v.length := by omega
    rcases hprov i y hiF hy with hyb | ⟨t', ht0, htb1, hvy⟩
    · rw [hyb]
      by_cases hkFe : k = F
      · rw [hkFe] at hkz
        have hza : z = a := Option.some.inj (hkz.symm.trans hws_self)
        rw [hza]
        exact hmax F b (by omega) hbl
      · have hkvz : v[k]? = some z := hws_gt k z (by omega) hkv hkz
        exact hle F b (by omega) hbl k z (by omega) hkv hkvz
    · by_cases hkFe : k = F
      · rw [hkFe] at hkz
        have hza : z = a := Option.some.inj (hkz.symm.trans hws_self)
        rw [hza]
        exact hmax t' y htb1 hvy
      · have hkvz : v[k]? = some z := hws_gt k z (by omega) hkv hkz
        exact hle t' y (by omega) hvy k z (by omega) hkv hkvz
  have hsorted1 : ∀ k1 k2 z1 z2, F ≤ k1 → k1 < k2 →
      k2 < (siftDown F 0 ((v.set 0 b).set F a)).length →
      (siftDown F 0 ((v.set 0 b).set F a))[k1]? = some z1 →
      (siftDown F 0 ((v.set 0 b).set F a))[k2]? = some z2 →
      z2.slt z1 = false := by
    intro k1 k2 z1 z2 hk1 h12 hkw2 hk1z hk2z
    rw [siftDown_get_ge F 0 _ k1 hk1] at hk1z
    rw [siftDown_get_ge F 0 _ k2 (by omega : F ≤ k2)] at hk2z
    have hk1v : k1 < v.length := by omega
    have hk2v : k2 < v.length := by omega
    by_cases hk1F : k1 = F
    · rw [hk1F] at hk1z
      have hz1 : z1 = a := Option.some.inj (hk1z.symm.trans hws_self)
      rw [hz1]
      have hkv2 : v[k2]? = some z2 :=
        hws_gt k2 z2 (by omega) hk2v hk2z
      exact hle 0 a (by omega) ha0 k2 z2 (by omega) hk2v hkv2
    · have hkv1 : v[k1]? = some z1 :=
        hws_gt k1 z1 (by omega) hk1v hk1z
      have hkv2 : v[k2]? = some z2 :=
        hws_gt k2 z2 (by omega) hk2v hk2z
      exact hsorted k1 k2 z1 z2 (by omega) h12 hk2v hkv1 hkv2
  exact ⟨by omega, hheap1, hle1, hsorted1⟩

/-- The extract drain preserves the invariant, hence the final list
    (`last = 0`) is pairwise sorted. Functional induction on
    `extractDown`: the stopped case is discharged by `l ≤ length`
    (the reads cannot miss), the swap case re-establishes heap-above
    via `sift_step` and pushes the old root onto the suffix. -/
theorem extractDown_sorted (bound : Nat) (last : Nat) (v : List (BitVec 32))
    (hinv : ExtractInv last v) :
    ExtractInv 0 (extractDown bound last v) := by
  refine extractDown.induct
    (fun last v => ExtractInv last v → ExtractInv 0 (extractDown bound last v))
    ?_ ?_ ?_ last v hinv
  · intro v hinv
    exact hinv
  · intro v F a b hbl ha0 ih hinv
    have hinv' : ExtractInv (F + 1) v := hinv
    have hred : extractDown bound F.succ v =
        extractDown bound F (siftDown F 0 ((v.set 0 b).set F a)) := by
      conv => lhs; unfold extractDown
      simp only [ha0, hbl]
    rw [hred]
    exact ih (extractDown_step_inv F v a b hbl ha0 hinv')
  · intro v F hdead hinv
    obtain ⟨hlen, _, _, _⟩ := hinv
    obtain ⟨a, ha0⟩ := getElem?_some_of_lt_length (l := v) (k := 0) (by omega)
    obtain ⟨b, hbl⟩ := getElem?_some_of_lt_length (l := v) (k := F) (by omega)
    exact False.elim (hdead a b ha0 hbl)

/-- Heapsort output is ascending. -/
theorem heapSortList_sorted (v : List (BitVec 32)) :
    (heapSortList v).Pairwise (fun a b => b.slt a = false) := by
  unfold heapSortList
  have hpl := (heapifyDown_perm v.length v.length v).length_eq
  have hinv : ExtractInv v.length (heapifyDown v.length v.length v) := by
    refine ⟨by omega, heapifyDown_isHeap v, ?_, ?_⟩
    · intro i y hiF hy k z hkF hkw hkz
      omega
    · intro k1 k2 z1 z2 hk1 h12 hkw2 hk1z hk2z
      omega
  have hfin := extractDown_sorted v.length v.length _ hinv
  obtain ⟨_, _, _, hsorted⟩ := hfin
  exact pairwise_of_indexed _
    (fun k1 k2 z1 z2 h12 hlen h1 h2 =>
      hsorted k1 k2 z1 z2 (by omega) h12 hlen h1 h2)





/-- A sift whose root is already at/below the bound is a no-op (some
    fuel always suffices). Covers the extract's final singleton sift
    where the general simulation's `0 < F` premise fails. -/
theorem siftFwd_nop (bn rn : Nat) (v : List (BitVec 32))
    (bound root : BitVec 64) (hbn : bound.toNat = bn)
    (hrn : root.toNat = rn) (hle : bn ≤ rn * 2 + 1) (hrn63 : rn < 2 ^ 63)
    (hmir : siftDown bn rn v = v) :
    ∃ F, ∀ F', F ≤ F' → siftFwd F' v bound root = .ok (siftDown bn rn v) := by
  refine ⟨Nat.succ Nat.zero, ?_⟩
  intro F' hF'
  obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
  subst hF''
  rw [hmir]
  have hchild : (root * 2 + 1).toNat = rn * 2 + 1 :=
    bv64_child_toNat root rn hrn hrn63
  have hcu : (root * 2 + 1).ult bound = false := by
    have hlt' : ¬ (root * 2 + 1).toNat < bound.toNat := by
      rw [hchild, hbn]; omega
    exact bv64_ult_false hlt'
  unfold siftFwd
  simp only [hcu, if_true, if_false, Bool.false_eq_true]

/-- The fuel-threaded extract drain computes the pure extract drain:
    some fuel always suffices (mirror induction; the swap case
    reuses the invariant step, the singleton sift uses the no-op). -/
theorem extractFwd_exists (last : Nat) (v : List (BitVec 32))
    (n llast : BitVec 64) (hll : llast.toNat = last)
    (hlen : last ≤ v.length) (hbig : v.length ≤ 2 ^ 63)
    (hinv : ExtractInv last v) :
    ∃ F, ∀ F', F ≤ F' →
      extractFwd F' v n llast = .ok (extractDown n.toNat last v) := by
  refine extractDown.induct
    (fun last v => ExtractInv last v → ∀ (n llast : BitVec 64),
      llast.toNat = last → last ≤ v.length → v.length ≤ 2 ^ 63 →
      ∃ F, ∀ F', F ≤ F' →
        extractFwd F' v n llast = .ok (extractDown n.toNat last v))
    ?_ ?_ ?_ last v hinv n llast hll hlen hbig
  · intro v hinv n llast hll hlen hbig
    have hmir : extractDown n.toNat 0 v = v := by simp only [extractDown]
    have hll0 : (llast != 0) = false := bv64_ne_zero_false hll
    refine ⟨Nat.succ Nat.zero, ?_⟩
    intro F' hF'
    obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
    subst hF''
    rw [hmir]
    unfold extractFwd
    simp only [hll0, if_true, if_false, Bool.false_eq_true]
  · intro v F a b hbl ha0 ih hinv n llast hll hlen hbig
    have hinv' : ExtractInv (F + 1) v := hinv
    have hlast' : (llast - 1).toNat = F := by
      have h1 := bv64_sub1_toNat llast (F + 1) hll (by omega)
      omega
    have hll0 : (llast != 0) = true := bv64_ne_zero_true (by omega)
    by_cases hF0 : F = 0
    · subst hF0
      have hab0 : a = b := Option.some.inj (ha0.symm.trans hbl)
      subst hab0
      have hmir0 : siftDown 0 0 ((v.set 0 a).set 0 a) =
          (v.set 0 a).set 0 a := by
        unfold siftDown
        simp only [show ¬ 0 * 2 + 1 < 0 from by omega, dite_true, dite_false,
          Bool.false_eq_true]
      obtain ⟨Fs, hFs⟩ := siftFwd_nop 0 0 ((v.set 0 a).set 0 a) (llast - 1) 0
        hlast' (by decide) (by omega) (by omega) hmir0
      have hinv1 := extractDown_step_inv 0 v a a hbl ha0 hinv'
      have hlen1 : (0 : Nat) ≤
          (siftDown 0 0 ((v.set 0 a).set 0 a)).length := by
        rw [hmir0]; omega
      have hbig1 : (siftDown 0 0 ((v.set 0 a).set 0 a)).length ≤ 2 ^ 63 := by
        rw [hmir0, List.length_set, List.length_set]; omega
      obtain ⟨Fe, hFe⟩ := ih hinv1 n (llast - 1) hlast' hlen1 hbig1
      refine ⟨Fs + Fe + 1, ?_⟩
      intro F' hF'
      obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
      subst hF''
      have hsift := hFs F'' (by omega)
      have hrest := hFe F'' (by omega)
      have hmir : extractDown n.toNat (0 + 1) v =
          extractDown n.toNat 0 (siftDown 0 0 ((v.set 0 a).set 0 a)) := by
        conv => lhs; unfold extractDown
        simp only [ha0]
      rw [hmir]
      unfold extractFwd
      simp only [hll0, hlast', ha0, hsift, hrest, if_true, if_false,
        Bool.false_eq_true]
    · have hwslen : ((v.set 0 b).set F a).length = v.length := by
        rw [List.length_set, List.length_set]
      obtain ⟨Fs, hFs⟩ := siftFwd_exists F 0 ((v.set 0 b).set F a)
        (llast - 1) 0
        hlast' (by decide) (by omega) (by omega) (by omega)
      have hinv1 := extractDown_step_inv F v a b hbl ha0 hinv'
      have hlen1 : F ≤ (siftDown F 0 ((v.set 0 b).set F a)).length := by
        have hpl := (siftDown_perm F 0 ((v.set 0 b).set F a)).length_eq
        omega
      have hbig1 : (siftDown F 0 ((v.set 0 b).set F a)).length ≤ 2 ^ 63 := by
        have hpl := (siftDown_perm F 0 ((v.set 0 b).set F a)).length_eq
        omega
      obtain ⟨Fe, hFe⟩ := ih hinv1 n (llast - 1) hlast' hlen1 hbig1
      refine ⟨Fs + Fe + 1, ?_⟩
      intro F' hF'
      obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
      subst hF''
      have hsift := hFs F'' (by omega)
      have hrest := hFe F'' (by omega)
      have hmir : extractDown n.toNat (F + 1) v =
          extractDown n.toNat F (siftDown F 0 ((v.set 0 b).set F a)) := by
        conv => lhs; unfold extractDown
        simp only [ha0, hbl]
      rw [hmir]
      unfold extractFwd
      simp only [hll0, hlast', ha0, hbl, hsift, hrest, if_true, if_false,
        Bool.false_eq_true]
  · intro v F hdead hinv n llast hll hlen hbig
    obtain ⟨a, ha0⟩ := getElem?_some_of_lt_length (l := v) (k := 0) (by omega)
    obtain ⟨b, hbl⟩ := getElem?_some_of_lt_length (l := v) (k := F) (by omega)
    exact False.elim (hdead a b ha0 hbl)


/-- The entry mirror computes heapsort: some fuel always suffices
    (heapify then extract at uniform fuel). -/
theorem heapSortFwd_exists (v : List (BitVec 32)) (n : BitVec 64)
    (hn : n.toNat = v.length) (hlen : v.length ≤ 2 ^ 63) :
    ∃ F, ∀ F', F ≤ F' →
      heapSortFwd F' v n = .ok (.stdVecVal (heapSortList v)) := by
  obtain ⟨Fh, hFh⟩ := heapifyFwd_exists v.length v.length v n n hn hn
    (Nat.le_refl _) (Nat.le_refl _) hlen
  have hpl : (heapifyDown v.length v.length v).length = v.length :=
    (heapifyDown_perm v.length v.length v).length_eq
  have hinv : ExtractInv v.length (heapifyDown v.length v.length v) := by
    refine ⟨by omega, heapifyDown_isHeap v, ?_, ?_⟩
    · intro i y hiF hy k z hkF hkw hkz
      omega
    · intro k1 k2 z1 z2 hk1 h12 hkw2 hk1z hk2z
      omega
  obtain ⟨Fe, hFe⟩ := extractFwd_exists v.length
    (heapifyDown v.length v.length v) n n hn (by omega) (by omega) hinv
  refine ⟨Fh + Fe + 1, ?_⟩
  intro F' hF'
  obtain ⟨F'', hF''⟩ := Nat.exists_eq_succ_of_ne_zero (show F' ≠ 0 by omega)
  subst hF''
  have hH := hFh (F''.succ) (by omega)
  have hE := hFe (F''.succ) (by omega)
  unfold heapSortFwd
  simp only [hH, hE, hn, heapSortList, if_true, if_false, Bool.false_eq_true]

/-- The entry point sorts: some fuel computes an ascending permutation
    of the input. The firewall between the fuel-threaded forward and
    the pure contract (`heapSortList_sorted`/`perm`). -/
theorem heapSortFwd_sorted (v : List (BitVec 32)) (n : BitVec 64)
    (hn : n.toNat = v.length) (hlen : v.length ≤ 2 ^ 63) :
    ∃ F w, heapSortFwd F v n = .ok (.stdVecVal w) ∧
      w.Pairwise (fun a b => b.slt a = false) ∧ List.Perm w v := by
  obtain ⟨F, hF⟩ := heapSortFwd_exists v n hn hlen
  exact ⟨F, _, hF F (Nat.le_refl _), heapSortList_sorted v,
    heapSortList_perm v⟩

/-- The emitted entry sorts: for some fuel the `heap_sort` body
    returns an ascending permutation of the input vector. Feeds the
    fuel-threaded drain equations into `heapSort_body_ok`, then the
    pure contract. -/
theorem heapSortFunc_sorted (vL : List (BitVec 32)) (N : BitVec 64)
    (hn : N.toNat = vL.length) (hlen : vL.length ≤ 2 ^ 63) :
    ∃ F ρ' w, evalStmtFuel F heapSortFunc.body
      [("v", .stdVecVal vL), ("n", .u64 N)] =
      .ok (ρ', .returned (.stdVecVal w)) ∧
      w.Pairwise (fun a b => b.slt a = false) ∧ List.Perm w vL := by
  obtain ⟨Fh, hFh⟩ := heapifyFwd_exists vL.length vL.length vL N N hn hn
    (Nat.le_refl _) (Nat.le_refl _) hlen
  have hpl : (heapifyDown vL.length vL.length vL).length = vL.length :=
    (heapifyDown_perm vL.length vL.length vL).length_eq
  have hinv : ExtractInv vL.length (heapifyDown vL.length vL.length vL) := by
    refine ⟨by omega, heapifyDown_isHeap vL, ?_, ?_⟩
    · intro i y hiF hy k z hkF hkw hkz
      omega
    · intro k1 k2 z1 z2 hk1 h12 hkw2 hk1z hk2z
      omega
  obtain ⟨Fe, hFe⟩ := extractFwd_exists vL.length
    (heapifyDown vL.length vL.length vL) N N hn (by omega) (by omega) hinv
  have hH := hFh (Fh + Fe + 1) (by omega)
  have hE := hFe (Fh + Fe + 1) (by omega)
  obtain ⟨ρ', hbody⟩ := heapSort_body_ok (Fh + Fe + 1) vL N _ _ hH hE
  refine ⟨Fh + Fe + 1, ρ', _, hbody, ?_, ?_⟩
  · obtain ⟨_, _, _, hsorted⟩ := extractDown_sorted N.toNat vL.length _ hinv
    exact pairwise_of_indexed _
      (fun k1 k2 z1 z2 h12 hlen h1 h2 =>
        hsorted k1 k2 z1 z2 (by omega) h12 hlen h1 h2)
  · have hweq : extractDown N.toNat vL.length
        (heapifyDown vL.length vL.length vL) = heapSortList vL := by
      unfold heapSortList
      rw [hn]
    rw [hweq]
    exact heapSortList_perm vL

