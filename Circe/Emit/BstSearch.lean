/-
Pillar-1 tree-kit goal: iterative BST membership query
(`bst_search`): `int bst_search(Node *root, int key)` descends
with a single cursor comparing against each node's key, and
returns `1` on the first match, `0` on miss. Read-only by
design: no stores, no `malloc`, the loop guard covers misses;
faults are loud.
-/
import Circe.Emit.LinkedReverse
import Circe.Mem.BinaryTree

/-- C name (unmangled: pure-C corpus entry). -/
def bstSearchName : String :=
  "bst_search"

/-- Loop body: hit returns `1` early; miss on `==` descends —
    left while `key < cur->key` (signed), right otherwise. -/
def bstSearchLoopBody : CStmt :=
  (.if_ (.ueq (.pgetVal (.var "cur")) (.var "key"))
    (.return_ (.lit (.i32 1)))
    (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
      (.assign "cur" (.pgetNext (.var "cur")))
      (.assign "cur" (.pgetRight (.var "cur")))))

/-- Loop `while (cur != nullptr) body`. -/
def bstSearchLoop : CStmt :=
  (.while_ (.une (.var "cur") (.lit .nullptr)) bstSearchLoopBody)

/-- Whole function: seed the cursor at the root, chase, return
    `0` on exhaustion. -/
def bstSearchBody : CStmt :=
  (.seq (.let_ "cur" nodeTy (.var "root"))
    (.seq bstSearchLoop (.return_ (.lit (.i32 0)))))

/-- The search entry: `Node*` root + `i32` key in, `i32`
    found-flag out. -/
def bstSearchFunc : Func :=
  ⟨bstSearchName,
   [{ name := "root", ty := nodeTy, role := .owned },
    { name := "key", ty := (.i 32), role := .owned }],
   (.i 32),
   bstSearchBody⟩

/-- Search environment: root/key slots, then the cursor slot
    (the entry binds `root` and `key` first, then the let
    conses `cur` on the front). -/
def mkBstSearchEnv (root : Option Addr) (key : BitVec 32)
    (cur : Option Addr) : Env :=
  [("cur", .ptrVal cur), ("root", .ptrVal root),
    ("key", .i32 key)]

theorem mkBstSearchEnv_cur (root : Option Addr)
    (key : BitVec 32) (cur : Option Addr) :
    envLookup (mkBstSearchEnv root key cur) "cur" =
      some (.ptrVal cur) := by
  simp [mkBstSearchEnv, envLookup]

theorem mkBstSearchEnv_root (root : Option Addr)
    (key : BitVec 32) (cur : Option Addr) :
    envLookup (mkBstSearchEnv root key cur) "root" =
      some (.ptrVal root) := by
  simp [mkBstSearchEnv, envLookup]

theorem mkBstSearchEnv_key (root : Option Addr)
    (key : BitVec 32) (cur : Option Addr) :
    envLookup (mkBstSearchEnv root key cur) "key" =
      some (.i32 key) := by
  simp [mkBstSearchEnv, envLookup]

/-! ## Forward mirror (read-only descent, hit node or miss) -/

/-- Descent for the first key match: read-only (each step reads
    the key at `[0]` and one link), returning the match (`none`
    on exhaustion). Misses, dangling links, and short blocks
    abort loudly at any fuel; each visit consumes fuel (like the
    evaluator's loop iteration — a hit needs fuel too). -/
def bstSearchChase (F : Nat) (m : Mem) (cur : Option Addr)
    (key : BitVec 32) : Result (Option Addr) :=
  match cur with
  | none => .ok none
  | some a =>
    match F with
    | 0 => .error .AssertFail
    | F + 1 =>
      match memFind m a with
      | none => .error .AssertFail
      | some b =>
        match memLoad m a b.tag 0 with
        | .error e => .error e
        | .ok w =>
          if w == key then .ok (some a)
          else if key.slt w then
            match memLoad m a b.tag 1 with
            | .error e => .error e
            | .ok w' => bstSearchChase F m (addrOfWord w') key
          else
            match memLoad m a b.tag 2 with
            | .error e => .error e
            | .ok w' => bstSearchChase F m (addrOfWord w') key

/-- Entry mirror: chase, then `1` on hit, `0` on miss. -/
def bstSearchFwd (F : Nat) (m : Mem) (root : Option Addr)
    (key : BitVec 32) : Result Nat :=
  match bstSearchChase F m root key with
  | .error e => .error e
  | .ok (some _) => .ok 1
  | .ok none => .ok 0

/-- The chase succeeds on a fueled segment (faults ruled out by
    the segment hypotheses; exhaustion by node-count fuel). -/
theorem bstSearchChase_ok (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (key : BitVec 32) (cur : Option Addr)
      (t : BTree) (hseg : TreeSeg m cur t)
      (hlen : t.bsize ≤ F),
    ∃ r, bstSearchChase F m cur key = .ok r := by
  induction F with
  | zero =>
    intro m hex key cur t hseg hlen
    cases hseg with
    | nil => exact ⟨none, by simp [bstSearchChase]⟩
    | cons hnode _ _ =>
      simp only [BTree.bsize] at hlen
      omega
  | succ F ih =>
    intro m hex key cur t hseg hlen
    cases hseg with
    | nil => exact ⟨none, by simp [bstSearchChase]⟩
    | @cons a tg k l r tl tr hnode hl hr =>
      have hfb : memFind m a = some _ := hnode
      have hmem0 : memLoad m a tg 0 = .ok k := nodeLoadKey hnode
      have hmem1 : memLoad m a tg 1 = .ok (linkWord l) :=
        nodeLoadLeft hnode
      have hmem2 : memLoad m a tg 2 = .ok (linkWord r) :=
        nodeLoadRight hnode
      have hlenL : tl.bsize ≤ F := by
        simp only [BTree.bsize] at hlen
        omega
      have hlenR : tr.bsize ≤ F := by
        simp only [BTree.bsize] at hlen
        omega
      by_cases heq : (k == key) = true
      · exact ⟨some a, by
          unfold bstSearchChase
          simp only [hfb, hmem0, ite_eq_left heq]⟩
      · have hallocL : ∀ c', l = some c' →
            (memFind m c').isSome = true := by
          intro c' hc'
          cases hnxt : l with
          | none => rw [hnxt] at hc'; cases hc'
          | some c'' =>
            cases hc'
            exact TreeSeg_head_alloc hl
        have hdecL := nodeAt3_link_roundtrip hex hallocL
        have hl' : TreeSeg m (addrOfWord (linkWord l)) tl := by
          rw [hdecL]; exact hl
        have hallocR : ∀ c', r = some c' →
            (memFind m c').isSome = true := by
          intro c' hc'
          cases hnxt : r with
          | none => rw [hnxt] at hc'; cases hc'
          | some c'' =>
            cases hc'
            exact TreeSeg_head_alloc hr
        have hdecR := nodeAt3_link_roundtrip hex hallocR
        have hr' : TreeSeg m (addrOfWord (linkWord r)) tr := by
          rw [hdecR]; exact hr
        by_cases hslt : (key.slt k) = true
        · obtain ⟨rL, hC'⟩ :=
            ih m hex key (addrOfWord (linkWord l)) tl hl' hlenL
          exact ⟨rL, by
            unfold bstSearchChase
            simp only [hfb, hmem0, hmem1, ite_eq_right heq,
              ite_eq_left hslt, hC']⟩
        · obtain ⟨rR, hC'⟩ :=
            ih m hex key (addrOfWord (linkWord r)) tr hr' hlenR
          have hnslt : ¬((key.slt k) = true) := hslt
          exact ⟨rR, by
            unfold bstSearchChase
            simp only [hfb, hmem0, hmem2, ite_eq_right heq,
              ite_eq_right hnslt, hC']⟩

/-- The chase is correct: a hit returns a node holding the key,
    a miss means the key is absent (needs the BST invariant —
    descent without bounds can miss present keys). Direct
    induction on fuel (the chase is read-only and the result is
    the chase result). Bounds-threaded so the induction
    hypothesis applies in both subtrees. -/
theorem bstSearchFwd_correct (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (root : Option Addr) (key : BitVec 32) (t : BTree)
    (r : Option Addr) (lo hi : Option (BitVec 32))
    (hbst : Bst lo hi t) (hseg : TreeSeg m root t)
    (hlen : t.bsize ≤ F)
    (hfwd : bstSearchChase F m root key = .ok r) :
    (∀ c, r = some c → key ∈ t.flatten) ∧
      (r = none → key ∉ t.flatten) := by
  induction F generalizing root t lo hi hbst hseg with
  | zero =>
    cases hseg with
    | nil =>
      simp only [bstSearchChase] at hfwd
      simp only [Except.ok.injEq] at hfwd
      subst r
      refine ⟨?_, ?_⟩
      · intro c hcon
        cases hcon
      · intro _ hmem
        simp only [BTree.flatten] at hmem
        exact List.not_mem_nil hmem
    | cons _ _ _ =>
      simp only [BTree.bsize] at hlen
      omega
  | succ F ih =>
    cases hseg with
    | nil =>
      simp only [bstSearchChase] at hfwd
      simp only [Except.ok.injEq] at hfwd
      subst r
      refine ⟨?_, ?_⟩
      · intro c hcon
        cases hcon
      · intro _ hmem
        simp only [BTree.flatten] at hmem
        exact List.not_mem_nil hmem
    | @cons a tg k l r' tl tr hnode hl hr =>
      cases hbst with
      | node hloB hhiB hlB hrB =>
        have hfb : memFind m a = some _ := hnode
        have hmem0 : memLoad m a tg 0 = .ok k := nodeLoadKey hnode
        have hmem1 : memLoad m a tg 1 = .ok (linkWord l) :=
          nodeLoadLeft hnode
        have hmem2 : memLoad m a tg 2 = .ok (linkWord r') :=
          nodeLoadRight hnode
        have hlenL : tl.bsize ≤ F := by
          simp only [BTree.bsize] at hlen
          omega
        have hlenR : tr.bsize ≤ F := by
          simp only [BTree.bsize] at hlen
          omega
        by_cases heq : (k == key) = true
        · have hxk : key = k := (beq_iff_eq.mp heq).symm
          simp only [bstSearchChase, hfb, hmem0, ite_eq_left heq]
            at hfwd
          simp only [Except.ok.injEq] at hfwd
          subst r
          refine ⟨?_, ?_⟩
          · intro c hcon
            cases hcon
            rw [BTree.flatten, List.mem_append, List.mem_append,
              List.mem_singleton]
            exact Or.inl (Or.inr hxk)
          · intro hcon
            cases hcon
        · have hallocL : ∀ c', l = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : l with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hl
          have hdecL := nodeAt3_link_roundtrip hex hallocL
          have hl' : TreeSeg m (addrOfWord (linkWord l)) tl := by
            rw [hdecL]; exact hl
          have hallocR : ∀ c', r' = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : r' with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hr
          have hdecR := nodeAt3_link_roundtrip hex hallocR
          have hr' : TreeSeg m (addrOfWord (linkWord r')) tr := by
            rw [hdecR]; exact hr
          by_cases hslt : (key.slt k) = true
          · simp only [bstSearchChase, hfb, hmem0, hmem1,
              ite_eq_right heq, ite_eq_left hslt] at hfwd
            have hIH := ih (root := addrOfWord (linkWord l))
              (t := tl) (lo := lo) (hi := some k) (hbst := hlB)
              (hseg := hl') (hlen := hlenL) (hfwd := hfwd)
            refine ⟨fun c hcon => ?_, fun hcon hmem => ?_⟩
            · have hL := hIH.1 c hcon
              rw [BTree.flatten, List.mem_append,
                List.mem_append, List.mem_singleton]
              exact Or.inl (Or.inl hL)
            · rw [BTree.flatten, List.mem_append,
                List.mem_append, List.mem_singleton] at hmem
              rcases hmem with (hmem | hbad) | hmem
              · exact absurd (hIH.2 hcon hmem) (by simp)
              · have hkk : (k == key) = true := by
                  rw [hbad]; simp
                exact absurd hkk heq
              · obtain ⟨hlo', -⟩ :=
                  BTree.mem_flatten_bounds hmem hrB
                simp only [boundLo] at hlo'
                have hcon : (k.slt key) = false :=
                  bst_slt_asymm hslt
                rw [hcon] at hlo'
                exact absurd hlo' (by simp)
          · simp only [bstSearchChase, hfb, hmem0, hmem2,
              ite_eq_right heq, ite_eq_right hslt]
              at hfwd
            have hIH := ih (root := addrOfWord (linkWord r'))
              (t := tr) (lo := some k) (hi := hi) (hbst := hrB)
              (hseg := hr') (hlen := hlenR) (hfwd := hfwd)
            refine ⟨fun c hcon => ?_, fun hcon hmem => ?_⟩
            · have hR := hIH.1 c hcon
              rw [BTree.flatten, List.mem_append,
                List.mem_append, List.mem_singleton]
              exact Or.inr hR
            · rw [BTree.flatten, List.mem_append,
                List.mem_append, List.mem_singleton] at hmem
              rcases hmem with (hmem | hbad) | hmem
              · obtain ⟨-, hhi'⟩ :=
                  BTree.mem_flatten_bounds hmem hlB
                simp only [boundHi] at hhi'
                rw [hhi'] at hslt
                exact absurd hslt (by simp)
              · have hkk : (k == key) = true := by
                  rw [hbad]; simp
                exact absurd hkk heq
              · exact absurd (hIH.2 hcon hmem) (by simp)

/-- Loop/evaluator agreement: the search loop evaluates exactly
    as the read-only chase directs — miss falls through with
    the cursor at null, hit returns `1` early. No equations
    beyond the chase (the entry mirror is the chase itself, so
    the forward identification is direct). Induction on fuel,
    reusing the chase-ok skeleton (segment hypotheses rule out
    faults; fuel rules out exhaustion). -/
theorem bstSearchLoop_agree (F : Nat) :
    ∀ (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (root : Option Addr) (key : BitVec 32)
      (cur : Option Addr)
      (t : BTree) (hseg : TreeSeg m cur t)
      (hlen : t.bsize ≤ F)
      (r : Option Addr)
      (hC : bstSearchChase F m cur key = .ok r),
    (r = none →
      memEvalStmtFuel F bstSearchLoop (mkBstSearchEnv root key cur)
        m π =
        .ok ((mkBstSearchEnv root key none, m, π), .fellThrough)) ∧
    (∀ c, r = some c →
      memEvalStmtFuel F bstSearchLoop (mkBstSearchEnv root key cur)
        m π =
        .ok ((mkBstSearchEnv root key (some c), m, π),
          .returned (.i32 1))) := by
  induction F with
  | zero =>
    intro m π hex root key cur t hseg hlen r hC
    cases hseg with
    | nil =>
      have hC' : bstSearchChase 0 m none key = .ok none := by
        simp [bstSearchChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq] at hC
      subst r
      refine ⟨?_, ?_⟩
      · intro _
        have hcurE : memEvalExpr (.var "cur")
            (mkBstSearchEnv root key none) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkBstSearchEnv_cur _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr)
            (mkBstSearchEnv root key none) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkBstSearchEnv root key none) m π =
            .ok (.b false) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
            hcurE hnullE
          have hbe : ((none : Option Addr) != none) = false := by
            simp
          rw [hbe] at hg
          exact hg
        have hw : memEvalStmtFuel 0 bstSearchLoop
            (mkBstSearchEnv root key none) m π =
            .ok ((mkBstSearchEnv root key none, m, π), .fellThrough) :=
          memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
        exact hw
      · intro c hcon
        cases hcon
    | cons _ _ _ =>
      simp only [BTree.bsize] at hlen
      omega
  | succ F ih =>
    intro m π hex root key cur t hseg hlen r hC
    cases hseg with
    | nil =>
      have hC' : bstSearchChase (F + 1) m none key = .ok none := by
        simp [bstSearchChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq] at hC
      subst r
      refine ⟨?_, ?_⟩
      · intro _
        have hcurE : memEvalExpr (.var "cur")
            (mkBstSearchEnv root key none) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkBstSearchEnv_cur _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr)
            (mkBstSearchEnv root key none) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkBstSearchEnv root key none) m π =
            .ok (.b false) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
            hcurE hnullE
          have hbe : ((none : Option Addr) != none) = false := by
            simp
          rw [hbe] at hg
          exact hg
        have hw : memEvalStmtFuel (F + 1) bstSearchLoop
            (mkBstSearchEnv root key none) m π =
            .ok ((mkBstSearchEnv root key none, m, π), .fellThrough) :=
          memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
        exact hw
      · intro c hcon
        cases hcon
    | @cons a tg k l r' tl tr hnode hl hr =>
      have hfb : memFind m a = some _ := hnode
      have hmem0 : memLoad m a tg 0 = .ok k := nodeLoadKey hnode
      have hmem1 : memLoad m a tg 1 = .ok (linkWord l) :=
        nodeLoadLeft hnode
      have hmem2 : memLoad m a tg 2 = .ok (linkWord r') :=
        nodeLoadRight hnode
      have hlenL : tl.bsize ≤ F := by
        simp only [BTree.bsize] at hlen
        omega
      have hlenR : tr.bsize ≤ F := by
        simp only [BTree.bsize] at hlen
        omega
      have hcurE : memEvalExpr (.var "cur")
          (mkBstSearchEnv root key (some a)) m π =
          .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkBstSearchEnv_cur _ _ _)
      have hnullE : memEvalExpr (.lit .nullptr)
          (mkBstSearchEnv root key (some a)) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkBstSearchEnv root key (some a)) m π = .ok (.b true) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none
          hcurE hnullE
        have hbe : ((some a) != none) = true := by simp
        rw [hbe] at hg
        exact hg
      have hpget : memEvalExpr (.pgetVal (.var "cur"))
          (mkBstSearchEnv root key (some a)) m π = .ok (.i32 k) :=
        memEvalExpr_pgetVal_hit _ _ _ _ _ _ _ hcurE hfb hmem0
      have hkeyE : memEvalExpr (.var "key")
          (mkBstSearchEnv root key (some a)) m π = .ok (.i32 key) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkBstSearchEnv_key _ _ _)
      have hueq : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "key"))
          (mkBstSearchEnv root key (some a)) m π =
          .ok (.b (k == key)) := by
        unfold memEvalExpr
        simp only [hpget, hkeyE]
      by_cases heq : (k == key) = true
      · have hC' : bstSearchChase (F + 1) m (some a) key =
          .ok (some a) := by
          unfold bstSearchChase
          simp only [hfb, hmem0, ite_eq_left heq]
        rw [hC'] at hC
        simp only [Except.ok.injEq] at hC
        subst r
        refine ⟨?_, ?_⟩
        · intro hcon
          cases hcon
        · intro c hcon
          cases hcon
          have hueqT : memEvalExpr
              (.ueq (.pgetVal (.var "cur")) (.var "key"))
              (mkBstSearchEnv root key (some a)) m π =
              .ok (.b true) := by
            rw [heq] at hueq
            exact hueq
          have hevR : memEvalExpr (.lit (.i32 1))
              (mkBstSearchEnv root key (some a)) m π =
              evalExpr (.lit (.i32 1))
                (mkBstSearchEnv root key (some a)) :=
            memEvalExpr_lit _ _ _ _
          have hevRV : evalExpr (.lit (.i32 1))
              (mkBstSearchEnv root key (some a)) =
              .ok (.i32 1) := by simp [evalExpr, litVal]
          have hret := memEvalStmtFuel_return F (.lit (.i32 1))
            (mkBstSearchEnv root key (some a)) m π _ hevR hevRV
          have hbodyEv : memEvalStmtFuel F bstSearchLoopBody
              (mkBstSearchEnv root key (some a)) m π =
              .ok ((mkBstSearchEnv root key (some a), m, π),
                .returned (.i32 1)) := by
            have hif : memEvalStmtFuel F bstSearchLoopBody
                (mkBstSearchEnv root key (some a)) m π =
                memEvalStmtFuel F (.return_ (.lit (.i32 1)))
                (mkBstSearchEnv root key (some a)) m π :=
              memEvalStmtFuel_if_true F _ _ _ _ _ _ hueqT
            exact hif.trans hret
          have hW : memEvalStmtFuel (F + 1) bstSearchLoop
              (mkBstSearchEnv root key (some a)) m π =
              .ok ((mkBstSearchEnv root key (some a), m, π),
                .returned (.i32 1)) := by
            have h := memEvalStmtFuel_while_true F _
              bstSearchLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          exact hW
      · have heqF : (k == key) = false := by
          cases h : (k == key) with
          | true => exact absurd h heq
          | false => rfl
        have hueqF : memEvalExpr
            (.ueq (.pgetVal (.var "cur")) (.var "key"))
            (mkBstSearchEnv root key (some a)) m π =
            .ok (.b false) := by
          rw [heqF] at hueq
          exact hueq
        have hsltM : memEvalExpr
            (.slt (.var "key") (.pgetVal (.var "cur")))
            (mkBstSearchEnv root key (some a)) m π =
            .ok (.b (key.slt k)) := by
          unfold memEvalExpr
          simp only [hkeyE, hpget]
        by_cases hslt : (key.slt k) = true
        · have hallocL : ∀ c', l = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : l with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hl
          have hdecL := nodeAt3_link_roundtrip hex hallocL
          have hl' : TreeSeg m (addrOfWord (linkWord l)) tl := by
            rw [hdecL]; exact hl
          have hsltT : memEvalExpr
              (.slt (.var "key") (.pgetVal (.var "cur")))
              (mkBstSearchEnv root key (some a)) m π =
              .ok (.b true) := by
            rw [hslt] at hsltM
            exact hsltM
          have hlinkL : memEvalExpr (.pgetNext (.var "cur"))
              (mkBstSearchEnv root key (some a)) m π =
              .ok (.ptrVal (addrOfWord (linkWord l))) :=
            memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE hfb hmem1
          have hstep : memEvalStmtFuel F
              (.assign "cur" (.pgetNext (.var "cur")))
              (mkBstSearchEnv root key (some a)) m π =
              .ok (((mkBstSearchEnv root key
                (addrOfWord (linkWord l))), m, π), .fellThrough) :=
            memEvalStmtFuel_assign_mem F "cur" (.pgetNext (.var "cur"))
              (mkBstSearchEnv root key (some a)) m π _ _
              hlinkL (by simp [mkBstSearchEnv, envUpdate])
          have hbodyEv : memEvalStmtFuel F bstSearchLoopBody
              (mkBstSearchEnv root key (some a)) m π =
              .ok (((mkBstSearchEnv root key
                (addrOfWord (linkWord l))), m, π), .fellThrough) := by
            have hifF : memEvalStmtFuel F bstSearchLoopBody
                (mkBstSearchEnv root key (some a)) m π =
                memEvalStmtFuel F
                  (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
                    (.assign "cur" (.pgetNext (.var "cur")))
                    (.assign "cur" (.pgetRight (.var "cur"))))
                  (mkBstSearchEnv root key (some a)) m π :=
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hueqF
            have hifT : memEvalStmtFuel F
                (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
                  (.assign "cur" (.pgetNext (.var "cur")))
                  (.assign "cur" (.pgetRight (.var "cur"))))
                (mkBstSearchEnv root key (some a)) m π =
                memEvalStmtFuel F
                  (.assign "cur" (.pgetNext (.var "cur")))
                  (mkBstSearchEnv root key (some a)) m π :=
              memEvalStmtFuel_if_true F _ _ _ _ _ _ hsltT
            exact hifF.trans (hifT.trans hstep)
          have hC'' : bstSearchChase F m (addrOfWord (linkWord l))
              key = .ok r := by
            have hch := hC
            unfold bstSearchChase at hch
            simp only [hfb, hmem0, hmem1] at hch
            rw [ite_eq_right heq, ite_eq_left hslt] at hch
            exact hch
          have hIH := ih m π hex root key
            (addrOfWord (linkWord l)) tl hl' hlenL r hC''
          have hWh : memEvalStmtFuel (F + 1) bstSearchLoop
              (mkBstSearchEnv root key (some a)) m π =
              memEvalStmtFuel F bstSearchLoop
                (mkBstSearchEnv root key (addrOfWord (linkWord l)))
                m π := by
            have h := memEvalStmtFuel_while_true F _
              bstSearchLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          refine ⟨fun hcon => ?_, fun c hcon => ?_⟩
          · have hstep := hIH.1 hcon
            rw [hWh]
            exact hstep
          · have hev := hIH.2 c hcon
            rw [hWh]
            exact hev
        · have hnslt : ¬((key.slt k) = true) := hslt
          have hallocR : ∀ c', r' = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : r' with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hr
          have hdecR := nodeAt3_link_roundtrip hex hallocR
          have hr' : TreeSeg m (addrOfWord (linkWord r')) tr := by
            rw [hdecR]; exact hr
          have hsltF' : (key.slt k) = false := by
            cases h : (key.slt k) with
            | true => exact absurd h hslt
            | false => rfl
          have hsltF : memEvalExpr
              (.slt (.var "key") (.pgetVal (.var "cur")))
              (mkBstSearchEnv root key (some a)) m π =
              .ok (.b false) := by
            rw [hsltF'] at hsltM
            exact hsltM
          have hlinkR : memEvalExpr (.pgetRight (.var "cur"))
              (mkBstSearchEnv root key (some a)) m π =
              .ok (.ptrVal (addrOfWord (linkWord r'))) :=
            memEvalExpr_pgetRight_hit _ _ _ _ _ _ _ hcurE hfb hmem2
          have hstep : memEvalStmtFuel F
              (.assign "cur" (.pgetRight (.var "cur")))
              (mkBstSearchEnv root key (some a)) m π =
              .ok (((mkBstSearchEnv root key
                (addrOfWord (linkWord r'))), m, π), .fellThrough) :=
            memEvalStmtFuel_assign_mem F "cur" (.pgetRight (.var "cur"))
              (mkBstSearchEnv root key (some a)) m π _ _
              hlinkR (by simp [mkBstSearchEnv, envUpdate])
          have hbodyEv : memEvalStmtFuel F bstSearchLoopBody
              (mkBstSearchEnv root key (some a)) m π =
              .ok (((mkBstSearchEnv root key
                (addrOfWord (linkWord r'))), m, π), .fellThrough) := by
            have hifF : memEvalStmtFuel F bstSearchLoopBody
                (mkBstSearchEnv root key (some a)) m π =
                memEvalStmtFuel F
                  (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
                    (.assign "cur" (.pgetNext (.var "cur")))
                    (.assign "cur" (.pgetRight (.var "cur"))))
                  (mkBstSearchEnv root key (some a)) m π :=
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hueqF
            have hifF2 : memEvalStmtFuel F
                (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
                  (.assign "cur" (.pgetNext (.var "cur")))
                  (.assign "cur" (.pgetRight (.var "cur"))))
                (mkBstSearchEnv root key (some a)) m π =
                memEvalStmtFuel F
                  (.assign "cur" (.pgetRight (.var "cur")))
                  (mkBstSearchEnv root key (some a)) m π :=
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hsltF
            exact hifF.trans (hifF2.trans hstep)
          have hC'' : bstSearchChase F m (addrOfWord (linkWord r'))
              key = .ok r := by
            have hch := hC
            unfold bstSearchChase at hch
            simp only [hfb, hmem0, hmem2, ite_eq_right heq,
              ite_eq_right hnslt] at hch
            exact hch
          have hIH := ih m π hex root key (addrOfWord (linkWord r'))
            tr hr' hlenR r hC''
          have hWh : memEvalStmtFuel (F + 1) bstSearchLoop
              (mkBstSearchEnv root key (some a)) m π =
              memEvalStmtFuel F bstSearchLoop
                (mkBstSearchEnv root key (addrOfWord (linkWord r')))
                m π := by
            have h := memEvalStmtFuel_while_true F _
              bstSearchLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          refine ⟨fun hcon => ?_, fun c hcon => ?_⟩
          · have hstep := hIH.1 hcon
            rw [hWh]
            exact hstep
          · have hev := hIH.2 c hcon
            rw [hWh]
            exact hev

/-- The search entry evaluates as the mirror and returns the
    found flag: seed let builds the chase environment, the
    loop agree fires the chase result (miss falls through to
    the tail `0`, hit returns `1` early), and the forward
    contract supplies the membership fact. -/
theorem bstSearchFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (root : Option Addr) (key : BitVec 32) (t : BTree)
    (hbst : Bst none none t) (hseg : TreeSeg m root t)
    (hlen : t.bsize ≤ F) :
    ∃ (ρ' : Env) (w : BitVec 32),
      memEvalStmtFuel F bstSearchFunc.body
        [("root", .ptrVal root), ("key", .i32 key)] m π =
        .ok ((ρ', m, π), .returned (.i32 w)) ∧
      (w = 1 → key ∈ t.flatten) ∧
      (w = 0 → key ∉ t.flatten) := by
  obtain ⟨cur', hC⟩ :=
    bstSearchChase_ok F m hex key root t hseg hlen
  have hloop := bstSearchLoop_agree F m π hex root key root t hseg
    hlen cur' hC
  have hF := bstSearchFwd_correct F m hex root key t cur'
    none none hbst hseg hlen hC
  have eC : memEvalExpr (.var "root")
      [("root", .ptrVal root), ("key", .i32 key)] m π =
      evalExpr (.var "root")
        [("root", .ptrVal root), ("key", .i32 key)] :=
    memEvalExpr_var _ _ _ _
  have vC : evalExpr (.var "root")
      [("root", .ptrVal root), ("key", .i32 key)] =
      .ok (.ptrVal root) :=
    evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hA := memEvalStmtFuel_let_pure F "cur" nodeTy (.var "root")
    _ _ _ (.ptrVal root)
    (by simp) (by simp) (by simp) (by simp) eC vC
  have hbody : bstSearchFunc.body = bstSearchBody := rfl
  rw [hbody]
  -- Dispatch on the chase result: none misses (tail `0`), some hits (early `1`).
  cases cur' with
  | none =>
    have hmiss := hloop.1 rfl
    have hretE : memEvalExpr (.lit (.i32 0))
        (mkBstSearchEnv root key none) m π =
        evalExpr (.lit (.i32 0)) (mkBstSearchEnv root key none) :=
      memEvalExpr_lit _ _ _ _
    have hretV : evalExpr (.lit (.i32 0))
        (mkBstSearchEnv root key none) =
        .ok (.i32 0) := by simp [evalExpr, litVal]
    have hret := memEvalStmtFuel_return F (.lit (.i32 0))
      (mkBstSearchEnv root key none) m π _ hretE hretV
    have hRest := memEvalStmtFuel_seq_fallthrough_trans F
      bstSearchLoop (.return_ (.lit (.i32 0)))
      (mkBstSearchEnv root key root) m π
      (mkBstSearchEnv root key none) m π _
      hmiss hret
    have hTop := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "cur" nodeTy (.var "root"))
      (.seq bstSearchLoop (.return_ (.lit (.i32 0))))
      ([("root", .ptrVal root), ("key", .i32 key)]) m π
      (mkBstSearchEnv root key root) m π _
      hA hRest
    refine ⟨_, 0, hTop, ?_, ?_⟩
    · intro hcon
      exact absurd hcon (by decide)
    · intro _
      exact hF.2 rfl
  | some c =>
    have hev := hloop.2 c rfl
    have hRest := memEvalStmtFuel_seq_return F
      bstSearchLoop (.return_ (.lit (.i32 0)))
      (mkBstSearchEnv root key root) m π
      (mkBstSearchEnv root key (some c)) m π _ hev
    have hTop := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "cur" nodeTy (.var "root"))
      (.seq bstSearchLoop (.return_ (.lit (.i32 0))))
      ([("root", .ptrVal root), ("key", .i32 key)]) m π
      (mkBstSearchEnv root key root) m π _
      hA hRest
    refine ⟨_, 1, hTop, ?_, ?_⟩
    · intro _
      exact hF.1 c rfl
    · intro hcon
      exact absurd hcon (by decide)
