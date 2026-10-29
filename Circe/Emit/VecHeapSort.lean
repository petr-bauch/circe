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
