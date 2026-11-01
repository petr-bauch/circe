/-
Circe.Emit.ListClear — pillar-1 proposed goal #1: whole-chain
free (`list_clear`) with per-node `free` in the traversal.

The corpus (`tests/cpp/list_clear.cpp`, entry
`Node *list_clear(Node *head)`) chases with a single cursor,
saving the link before each `free(cur)`, freeing every node
exactly once, and returning the (now empty) head `nullptr`.
The payload is never read and the freed cells are never chased.
Faults are loud: freeing a null, missing, or already-freed cell
aborts (`memFree` miss/tag/liveness checks), exactly the L-ptr
miss discipline; dangling links abort (`memLoad` miss). There
are no stores at all — the mirror walks with `.pgetNext` and
frees with `.nfree`.

The contract: every node of the input chain is dead on exit
(live flag cleared, contents kept but unusable), and every
other cell is untouched (`memFind` equal) or was freed by the
run with contents preserved. The invariant tracks the freed
prefix's addresses plus a reachability triage of the entry
chain (freed / still-current / other).
-/
import Circe.Emit.LinkedReverse
import Circe.Emit.ListCopy

/-- Mangled name of the clear entry. -/
def listClearName : String :=
  "_Z10list_clearP4Node"

/-- The clear loop body: save the link, free the cursor,
    advance. -/
def listClearLoopBody : CStmt :=
  (.seq (.assign "next" (.pgetNext (.var "cur")))
    (.seq (.nfree (.var "cur")) (.assign "cur" (.var "next"))))

/-- The clear loop (isolated for the loop/evaluator agreement). -/
def listClearLoop : CStmt :=
  (.while_ (.une (.var "cur") (.lit .nullptr)) listClearLoopBody)

/-- Canonical CoreIR for `list_clear`: seed the cursor and
    the link spare, chase and free, return the (now empty)
    head. -/
def listClearBody : CStmt :=
  (.seq (.let_ "cur" nodeTy (.var "head"))
    (.seq (.let_ "next" nodeTy (.lit .nullptr))
      (.seq listClearLoop (.return_ (.lit .nullptr)))))

/-- The clear entry: a single `Node*` in, a `Node*` out (always
    null, the now-empty head). -/
def listClearFunc : Func :=
  ⟨listClearName,
   [{ name := "head", ty := nodeTy, role := .owned }],
   nodeTy,
   listClearBody⟩

/-- Clear environment: link spare, cursor, entry head (the
    entry binds `head`, then the lets cons `cur` and `next` on
    the front; assigns rewrite slots in place). -/
def mkListClearEnv (head cur nxt : Option Addr) : Env :=
  [("next", .ptrVal nxt), ("cur", .ptrVal cur),
    ("head", .ptrVal head)]

/-- Chase mirror: load the link, free the node, advance (fuel
    from the segment length; a null, missing, or already-freed
    cell is loud, dangling links abort). -/
def listClearChase (F : Nat) (m : Mem) (cur : Option Addr) :
    Result Mem :=
  match cur with
  | none => .ok m
  | some a =>
    match F with
    | 0 => .error .AssertFail
    | F + 1 =>
      match memFind m a with
      | none => .error .AssertFail
      | some b =>
        match memLoad m a b.tag 1 with
        | .error e => .error e
        | .ok w' =>
          match memFree m a b.tag with
          | .error e => .error e
          | .ok m' => listClearChase F m' (addrOfWord w')

/-- Entry mirror: chase the head (the input chain is freed in
    full; the empty head comes back). -/
def listClearFwd (F : Nat) (m : Mem) (head : Option Addr) :
    Result (Mem × Option Addr) :=
  match listClearChase F m head with
  | .error e => .error e
  | .ok m' => .ok (m', none)

/-- The cursor slot resolves. -/
theorem mkListClearEnv_cur (head cur nxt : Option Addr) :
    envLookup (mkListClearEnv head cur nxt) "cur" =
      some (.ptrVal cur) := by
  simp [mkListClearEnv, envLookup]

/-- The head slot resolves. -/
theorem mkListClearEnv_head (head cur nxt : Option Addr) :
    envLookup (mkListClearEnv head cur nxt) "head" =
      some (.ptrVal head) := by
  simp [mkListClearEnv, envLookup]

/-- The link spare resolves. -/
theorem mkListClearEnv_next (head cur nxt : Option Addr) :
    envLookup (mkListClearEnv head cur nxt) "next" =
      some (.ptrVal nxt) := by
  simp [mkListClearEnv, envLookup]

/-- The whole-chain-free invariant: the suffix is still a live
    segment; every freed address keeps its contents dead; every
    other cell is untouched; and every entry-chain address is
    either freed or still reachable from the cursor. -/
structure ClearInv (vs₀ : List (BitVec 32)) (F : Nat) (m₀ : Mem)
    (head : Option Addr) (m : Mem) (cur : Option Addr)
    (pref : List Addr) (suf : List (BitVec 32)) : Prop where
  hseg : ListSeg m cur suf
  hcont : ∀ a, a ∈ pref →
    ∃ t v n, memFind m₀ a = some ⟨t, true, [v, linkWord n]⟩ ∧
      memFind m a = some ⟨t, false, [v, linkWord n]⟩
  hrest : ∀ a, a ∉ pref → memFind m a = memFind m₀ a
  hsplit : ∀ a, SegMem (m := m₀) head a →
    a ∈ pref ∨ SegMem (m := m) cur a
  hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32
  hlen : suf.length ≤ F

/-- One clear iteration: load the link, free the cursor, and
    the freed prefix grows by its address. -/
theorem clear_step {vs₀ : List (BitVec 32)} {F : Nat} {m₀ : Mem}
    {head : Option Addr} {m : Mem} {a : Addr} {w : BitVec 32}
    {ws : List (BitVec 32)} {pref : List Addr}
    (hinv : ClearInv vs₀ (F + 1) m₀ head m (some a) pref
      (w :: ws)) :
    ∃ (m' : Mem) (t : Nat) (lw : BitVec 32),
      memLoad m a t 1 = .ok lw ∧
      memFree m a t = .ok m' ∧
      ClearInv vs₀ F m₀ head m' (addrOfWord lw) (a :: pref) ws := by
  cases hinv.hseg with
  | @cons a₀ t₀ v₀ nL vs₀ hnode t2 =>
      have hcell : cellsAt m a t₀ [w, linkWord nL] := hnode
      have hfindA : memFind m a = some ⟨t₀, true, [w, linkWord nL]⟩ :=
        hnode
      have hL1 : memLoad m a t₀ 1 = .ok (linkWord nL) :=
        memLoad_cellsAt m a t₀ 1 [w, linkWord nL] (linkWord nL)
          hcell (by simp)
      have hdec : addrOfWord (linkWord nL) = nL :=
        nodeAt_link_roundtrip hnode hinv.hex
          (ListSeg_start_alloc t2)
      have hfree : ∃ m', memFree m a t₀ = .ok m' :=
        ⟨⟨m.next, (a, (⟨t₀, false, [w, linkWord nL]⟩ : Block)) ::
          m.blocks, m.blocks64⟩, by simp [memFree, hfindA]⟩
      obtain ⟨m', hF⟩ := hfree
      have hseg' : ListSeg m' nL ws :=
        ListSeg.free_other t2 hF
          (ListSeg_head_notin_tail hnode t2 hinv.hex)
      have hdeadA : memFind m' a =
          some ⟨t₀, false, [w, linkWord nL]⟩ :=
        memFind_memFree_dead hnode hF
      have hanp : a ∉ pref := by
        intro hmem
        obtain ⟨t1, v1, n1, _, hdead⟩ := hinv.hcont a hmem
        rw [hfindA] at hdead
        simp at hdead
      have hcont' : ∀ x, x ∈ (a :: pref) →
          ∃ t v n, memFind m₀ x = some ⟨t, true, [v, linkWord n]⟩ ∧
            memFind m' x = some ⟨t, false, [v, linkWord n]⟩ := by
        intro x hx
        cases hx with
        | head =>
            exact ⟨t₀, w, nL, by
              rw [← hinv.hrest a hanp]
              exact hfindA, hdeadA⟩
        | tail _ hxp =>
            obtain ⟨t1, v1, n1, h₀, h1⟩ := hinv.hcont x hxp
            refine ⟨t1, v1, n1, h₀, ?_⟩
            rw [memFind_memFree_other m m' a x t₀ hF (by
              intro hbad
              rw [hbad] at hxp
              exact hanp hxp)]
            exact h1
      have hrest' : ∀ x, x ∉ (a :: pref) →
          memFind m' x = memFind m₀ x := by
        intro x hx
        have hxne : x ≠ a := by
          intro hbad
          exact hx (by rw [hbad]; simp [List.mem_cons])
        have hxnp : x ∉ pref := by
          intro hbad
          exact hx (by simp [List.mem_cons, hbad])
        rw [memFind_memFree_other m m' a x t₀ hF hxne]
        exact hinv.hrest x hxnp
      have hsplit' : ∀ x, SegMem (m := m₀) head x →
          x ∈ (a :: pref) ∨ SegMem (m := m') nL x := by
        intro x hx
        cases hinv.hsplit x hx with
        | inl hxmem => exact .inl (by simp [List.mem_cons, hxmem])
        | inr hxcur =>
            by_cases hxa : x = a
            · exact .inl (by rw [hxa]; simp [List.mem_cons])
            · cases hxcur with
              | here _ => exact absurd rfl hxa
              | @there _ _ _ _ nQ hnodeQ htail =>
                  have hallocQ := SegMem_head_alloc htail
                  have halign : nQ = nL :=
                    nodeAt_link_unique hnodeQ hnode hinv.hex
                      hallocQ (ListSeg_start_alloc t2)
                  rw [halign] at htail
                  exact .inr (SegMem_free_other htail hF
                    (ListSeg_head_notin_tail hnode t2 hinv.hex))
      have hex' : ∀ x, (memFind m' x).isSome = true →
          x + 1 < 2 ^ 32 := by
        intro x hx
        by_cases hxa : x = a
        · have hax : (memFind m a).isSome = true := by
            rw [hfindA]
            rfl
          rw [hxa]
          exact hinv.hex a hax
        · have hfind : memFind m' x = memFind m x :=
            memFind_memFree_other m m' a x t₀ hF hxa
          rw [hfind] at hx
          exact hinv.hex x hx
      refine ⟨m', t₀, linkWord nL, hL1, hF, ?_⟩
      rw [hdec]
      exact
        { hseg := hseg'
          hcont := hcont'
          hrest := hrest'
          hsplit := hsplit'
          hex := hex'
          hlen := by
            have h := hinv.hlen
            simp only [List.length_cons] at h
            omega }

/-- The clear invariant lifts to larger fuel (only the length
    bound mentions fuel — one step down the bound). -/
theorem ClearInv.liftF {vs₀ : List (BitVec 32)} {F : Nat}
    {m₀ : Mem} {head : Option Addr} {m : Mem}
    {cur : Option Addr} {pref : List Addr}
    {suf : List (BitVec 32)}
    (h : ClearInv vs₀ F m₀ head m cur pref suf) :
    ClearInv vs₀ (F + 1) m₀ head m cur pref suf :=
  { h with hlen := Nat.le_succ_of_le h.hlen }

/-- The clear chase is correct: from any reachable invariant it
    returns `ok`, exhausts the chain, and leaves the cursor
    empty. -/
theorem listClearChase_ok {vs₀ : List (BitVec 32)} (F : Nat) :
    ∀ (m₀ : Mem) (head : Option Addr) (m : Mem)
      (cur : Option Addr) (pref : List Addr)
      (suf : List (BitVec 32))
      (hinv : ClearInv vs₀ F m₀ head m cur pref suf),
    ∃ m' pref',
      listClearChase F m cur = .ok m' ∧
      ClearInv vs₀ F m₀ head m' none pref' [] := by
  induction F with
  | zero =>
      intro m₀ head m cur pref suf hinv
      cases hinv.hseg with
      | nil =>
          exact ⟨m, pref, by simp [listClearChase], hinv⟩
      | cons hnode t2 =>
          have h := hinv.hlen
          simp only [List.length_cons] at h
          omega
  | succ F ih =>
      intro m₀ head m cur pref suf hinv
      cases hinv.hseg with
      | nil =>
          exact ⟨m, pref, by simp [listClearChase], hinv⟩
      | cons hnode t2 =>
          rename_i a₀ t₀ v₀ nL tsuf
          have hcell : cellsAt m a₀ t₀ [v₀, linkWord nL] := hnode
          have hfb : memFind m a₀ =
              some ⟨t₀, true, [v₀, linkWord nL]⟩ := hnode
          have hL1 : memLoad m a₀ t₀ 1 = .ok (linkWord nL) :=
            memLoad_cellsAt m a₀ t₀ 1 [v₀, linkWord nL]
              (linkWord nL) hcell (by simp)
          obtain ⟨m1, tS, lw, hLS, hFS, hinv'⟩ := clear_step hinv
          have hteq : tS = t₀ := memLoad_tag hLS hfb
          subst tS
          have hlweq : lw = linkWord nL := by
            have h := hLS.symm.trans hL1
            simpa using h
          subst hlweq
          obtain ⟨mF, prefF, hCF, hinvF⟩ :=
            ih m₀ head m1 (addrOfWord (linkWord nL)) (a₀ :: pref)
              tsuf hinv'
          refine ⟨mF, prefF, ?_, hinvF.liftF⟩
          unfold listClearChase
          simp only [hfb, hLS, hFS, hCF]

/-- The forward mirror is correct: every node of the input
    chain is dead on exit (live flag cleared, contents kept),
    and every other cell is either untouched or was freed by
    the run with contents preserved. -/
theorem listClearFwd_correct {vs₀ : List (BitVec 32)} {F : Nat}
    {m : Mem} {head : Option Addr} {m' : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hseg : ListSeg m head vs₀)
    (hlen : vs₀.length ≤ F)
    (hfwd : listClearFwd F m head = .ok (m', none)) :
    (∀ a, SegMem (m := m) head a →
      ∃ t v n, memFind m' a =
        some ⟨t, false, [v, linkWord n]⟩) ∧
    (∀ a, memFind m' a = memFind m a ∨
      ∃ t v n, memFind m a =
          some ⟨t, true, [v, linkWord n]⟩ ∧
        memFind m' a =
          some ⟨t, false, [v, linkWord n]⟩) := by
  have hinv : ClearInv vs₀ F m head m head [] vs₀ :=
    { hseg := hseg
      hcont := fun a h => by simp at h
      hrest := fun a _ => rfl
      hsplit := fun a h => .inr h
      hex := hex
      hlen := hlen }
  obtain ⟨mC', pref', hC, hinv'⟩ :=
    listClearChase_ok F m head m head [] vs₀ hinv
  unfold listClearFwd at hfwd
  rw [hC] at hfwd
  simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
  obtain ⟨e1, e2⟩ := hfwd
  subst e1
  refine ⟨?_, ?_⟩
  · intro a ha
    cases hinv'.hsplit a ha with
    | inl hmem =>
        obtain ⟨t, v, n, _, h2⟩ := hinv'.hcont a hmem
        exact ⟨t, v, n, h2⟩
    | inr hmem => cases hmem
  · intro a
    by_cases hmem : a ∈ pref'
    · obtain ⟨t, v, n, h1, h2⟩ := hinv'.hcont a hmem
      exact .inr ⟨t, v, n, h1, h2⟩
    · exact .inl (hinv'.hrest a hmem)

/-- The loop agrees with the chase: from any reachable invariant
    the evaluator runs the loop to fall-through and lands in the
    chase's final memory with an exhausted cursor. -/
theorem listClearLoop_agree {vs₀ : List (BitVec 32)} (F : Nat) :
    ∀ (m₀ : Mem) (head : Option Addr) (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (cur nxt : Option Addr) (pref : List Addr)
      (suf : List (BitVec 32))
      (hinv : ClearInv vs₀ F m₀ head m cur pref suf)
      (m' : Mem)
      (hC : listClearChase F m cur = .ok m'),
    ∃ nxt',
      memEvalStmtFuel F listClearLoop
        (mkListClearEnv head cur nxt) m π =
        .ok (((mkListClearEnv head none nxt'), m', π),
          .fellThrough) := by
  induction F with
  | zero =>
      intro m₀ head m π hex cur nxt pref suf hinv m' hC
      cases hinv.hseg with
      | nil =>
          have hC' : listClearChase 0 m none = .ok m := by
            simp [listClearChase]
          rw [hC'] at hC
          simp only [Except.ok.injEq] at hC
          subst hC
          refine ⟨nxt, ?_⟩
          have hcurE : memEvalExpr (.var "cur")
              (mkListClearEnv head none nxt) m π =
              .ok (.ptrVal none) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (mkListClearEnv_cur _ _ _)
          have hnullE : memEvalExpr (.lit .nullptr)
              (mkListClearEnv head none nxt) m π =
              .ok (.ptrVal none) := by
            simp [memEvalExpr, litVal]
          have hgF : memEvalExpr
              (.une (.var "cur") (.lit .nullptr))
              (mkListClearEnv head none nxt) m π =
              .ok (.b false) := by
            have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
              hcurE hnullE
            have hbe : ((none : Option Addr) != none) = false := by
              simp
            rw [hbe] at hg
            exact hg
          exact memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
      | cons hnode t2 =>
          have h := hinv.hlen
          simp only [List.length_cons] at h
          omega
  | succ F ih =>
      intro m₀ head m π hex cur nxt pref suf hinv m' hC
      cases hinv.hseg with
      | nil =>
          have hC' : listClearChase (F + 1) m none = .ok m := by
            simp [listClearChase]
          rw [hC'] at hC
          simp only [Except.ok.injEq] at hC
          subst hC
          refine ⟨nxt, ?_⟩
          have hcurE : memEvalExpr (.var "cur")
              (mkListClearEnv head none nxt) m π =
              .ok (.ptrVal none) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (mkListClearEnv_cur _ _ _)
          have hnullE : memEvalExpr (.lit .nullptr)
              (mkListClearEnv head none nxt) m π =
              .ok (.ptrVal none) := by
            simp [memEvalExpr, litVal]
          have hgF : memEvalExpr
              (.une (.var "cur") (.lit .nullptr))
              (mkListClearEnv head none nxt) m π =
              .ok (.b false) := by
            have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
              hcurE hnullE
            have hbe : ((none : Option Addr) != none) = false := by
              simp
            rw [hbe] at hg
            exact hg
          exact memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
      | cons hnode t2 =>
          rename_i a₀ t₀ v₀ nL tsuf
          have hcell : cellsAt m a₀ t₀ [v₀, linkWord nL] := hnode
          have hfb : memFind m a₀ =
              some ⟨t₀, true, [v₀, linkWord nL]⟩ := hnode
          have hL1 : memLoad m a₀ t₀ 1 = .ok (linkWord nL) :=
            memLoad_cellsAt m a₀ t₀ 1 [v₀, linkWord nL]
              (linkWord nL) hcell (by simp)
          obtain ⟨m1, tS, lw, hLS, hFS, hinv'⟩ := clear_step hinv
          have hteq : tS = t₀ := memLoad_tag hLS hfb
          subst tS
          have hlweq : lw = linkWord nL := by
            have h := hLS.symm.trans hL1
            simpa using h
          subst hlweq
          have hC' : listClearChase F m1
              (addrOfWord (linkWord nL)) = .ok m' := by
            unfold listClearChase at hC
            simp only [hfb, hLS, hFS] at hC
            exact hC
          obtain ⟨nxt', hIH⟩ :=
            ih m₀ head m1 π hinv'.hex (addrOfWord (linkWord nL))
              (addrOfWord (linkWord nL)) (a₀ :: pref) tsuf
              hinv' m' hC'
          refine ⟨nxt', ?_⟩
          have hcurE : memEvalExpr (.var "cur")
              (mkListClearEnv head (some a₀) nxt) m π =
              .ok (.ptrVal (some a₀)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (mkListClearEnv_cur _ _ _)
          have hnullE : memEvalExpr (.lit .nullptr)
              (mkListClearEnv head (some a₀) nxt) m π =
              .ok (.ptrVal none) := by
            simp [memEvalExpr, litVal]
          have hgT : memEvalExpr
              (.une (.var "cur") (.lit .nullptr))
              (mkListClearEnv head (some a₀) nxt) m π =
              .ok (.b true) := by
            have hg := memEvalExpr_une_ptrVal _ _ _ _ _
              (some a₀) none hcurE hnullE
            have hbe : ((some a₀) != none) = true := by simp
            rw [hbe] at hg
            exact hg
          have hpgn : memEvalExpr (.pgetNext (.var "cur"))
              (mkListClearEnv head (some a₀) nxt) m π =
              .ok (.ptrVal (addrOfWord (linkWord nL))) :=
            memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE
              hfb hL1
          have huN : envUpdate
              (mkListClearEnv head (some a₀) nxt) "next"
              (.ptrVal (addrOfWord (linkWord nL))) =
              some (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) := by
            simp [mkListClearEnv, envUpdate]
          have hassignN : memEvalStmtFuel F
              (.assign "next" (.pgetNext (.var "cur")))
              (mkListClearEnv head (some a₀) nxt) m π =
              .ok (((mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL)), m, π)),
                .fellThrough) :=
            memEvalStmtFuel_assign_mem F "next"
              (.pgetNext (.var "cur"))
              (mkListClearEnv head (some a₀) nxt) m π
              (.ptrVal (addrOfWord (linkWord nL)))
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) hpgn huN
          have hdC : memEvalExpr (.var "cur")
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) m π =
              .ok (.ptrVal (some a₀)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (mkListClearEnv_cur _ _ _)
          have hnfree : memEvalStmtFuel F
              (.nfree (.var "cur"))
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) m π =
              .ok (((mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL)), m1, π)),
                .fellThrough) :=
            memEvalStmtFuel_nfree_ok F (.var "cur")
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) m π a₀
              ⟨t₀, true, [v₀, linkWord nL]⟩ m1 hdC hfb hFS
          have hEq : memEvalExpr (.var "next")
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) m1 π =
              evalExpr (.var "next")
                (mkListClearEnv head (some a₀)
                  (addrOfWord (linkWord nL))) :=
            memEvalExpr_var _ _ _ _
          have hvN : evalExpr (.var "next")
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) =
              .ok (.ptrVal (addrOfWord (linkWord nL))) :=
            evalExpr_var_hit _ _ _
              (mkListClearEnv_next _ _ _)
          have huC : envUpdate
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) "cur"
              (.ptrVal (addrOfWord (linkWord nL))) =
              some (mkListClearEnv head
                (addrOfWord (linkWord nL))
                (addrOfWord (linkWord nL))) := by
            simp [mkListClearEnv, envUpdate]
          have hassignC : memEvalStmtFuel F
              (.assign "cur" (.var "next"))
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) m1 π =
              .ok (((mkListClearEnv head
                (addrOfWord (linkWord nL))
                (addrOfWord (linkWord nL)), m1, π)),
                .fellThrough) :=
            memEvalStmtFuel_assign F "cur" (.var "next")
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) m1 π
              (.ptrVal (addrOfWord (linkWord nL)))
              (mkListClearEnv head
                (addrOfWord (linkWord nL))
                (addrOfWord (linkWord nL))) hEq hvN huC
          have h2 : memEvalStmtFuel F
              (.seq (.nfree (.var "cur"))
                (.assign "cur" (.var "next")))
              (mkListClearEnv head (some a₀)
                (addrOfWord (linkWord nL))) m π =
              .ok (((mkListClearEnv head
                (addrOfWord (linkWord nL))
                (addrOfWord (linkWord nL)), m1, π)),
                .fellThrough) :=
            memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
              _ _ _ _ hnfree hassignC
          have hbody : memEvalStmtFuel F listClearLoopBody
              (mkListClearEnv head (some a₀) nxt) m π =
              .ok (((mkListClearEnv head
                (addrOfWord (linkWord nL))
                (addrOfWord (linkWord nL)), m1, π)),
                .fellThrough) := by
            unfold listClearLoopBody
            exact memEvalStmtFuel_seq_fallthrough_trans F _ _
              _ _ _ _ _ _ _ hassignN h2
          unfold listClearLoop
          rw [memEvalStmtFuel_while_true F _ _ _ _ _ hgT,
            hbody]
          exact hIH

/-- The entry triple: seeding the cursor and the link spare and
    running the loop evaluates the clear body to the empty head,
    with the full contract. -/
theorem listClearFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (vs₀ : List (BitVec 32))
    (m' : Mem)
    (hseg : ListSeg m head vs₀)
    (hlen : vs₀.length ≤ F)
    (hfwd : listClearFwd F m head = .ok (m', none)) :
    ∃ ρ', memEvalStmtFuel F listClearFunc.body
      [("head", .ptrVal head)] m π =
      .ok ((ρ', m', π), .returned (.ptrVal none)) ∧
      (∀ a, SegMem (m := m) head a →
        ∃ t v n, memFind m' a =
          some ⟨t, false, [v, linkWord n]⟩) ∧
      (∀ a, memFind m' a = memFind m a ∨
        ∃ t v n, memFind m a =
            some ⟨t, true, [v, linkWord n]⟩ ∧
          memFind m' a =
            some ⟨t, false, [v, linkWord n]⟩) := by
  have hcon := listClearFwd_correct hex hseg hlen hfwd
  obtain ⟨hdeadAll, hrestAll⟩ := hcon
  have hinv : ClearInv vs₀ F m head m head [] vs₀ :=
    { hseg := hseg
      hcont := fun a h => by simp at h
      hrest := fun a _ => rfl
      hsplit := fun a h => .inr h
      hex := hex
      hlen := hlen }
  obtain ⟨mC', pref', hC, hinv'⟩ :=
    listClearChase_ok F m head m head [] vs₀ hinv
  unfold listClearFwd at hfwd
  rw [hC] at hfwd
  simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
  obtain ⟨e1, e2⟩ := hfwd
  subst e1
  obtain ⟨nxt', hloop⟩ :=
    listClearLoop_agree F m head m π hinv.hex head none []
      vs₀ hinv mC' hC
  have eC : memEvalExpr (.var "head")
      [("head", .ptrVal head)] m π =
      evalExpr (.var "head") [("head", .ptrVal head)] :=
    memEvalExpr_var _ _ _ _
  have vC : evalExpr (.var "head") [("head", .ptrVal head)] =
      .ok (.ptrVal head) :=
    evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hletC : memEvalStmtFuel F
      (.let_ "cur" nodeTy (.var "head"))
      [("head", .ptrVal head)] m π =
      .ok (((("cur", .ptrVal head) ::
        [("head", .ptrVal head)], m, π)), .fellThrough) :=
    memEvalStmtFuel_let_pure F "cur" nodeTy (.var "head")
      [("head", .ptrVal head)] m π
      (.ptrVal head) (by simp) (by simp) (by simp) (by simp)
      eC vC
  have eN : memEvalExpr (.lit .nullptr)
      (("cur", .ptrVal head) :: [("head", .ptrVal head)]) m π =
      evalExpr (.lit .nullptr)
        (("cur", .ptrVal head) :: [("head", .ptrVal head)]) :=
    memEvalExpr_lit _ _ _ _
  have vN : evalExpr (.lit .nullptr)
      (("cur", .ptrVal head) :: [("head", .ptrVal head)]) =
      .ok (.ptrVal none) := by
    simp [evalExpr, litVal]
  have hletN : memEvalStmtFuel F
      (.let_ "next" nodeTy (.lit .nullptr))
      (("cur", .ptrVal head) :: [("head", .ptrVal head)]) m π =
      .ok (((("next", .ptrVal none) :: ("cur", .ptrVal head) ::
        [("head", .ptrVal head)], m, π)), .fellThrough) :=
    memEvalStmtFuel_let_pure F "next" nodeTy (.lit .nullptr)
      (("cur", .ptrVal head) :: [("head", .ptrVal head)]) m π
      (.ptrVal none) (by simp) (by simp) (by simp) (by simp)
      eN vN
  have hret : memEvalStmtFuel F
      (.return_ (.lit .nullptr))
      (mkListClearEnv head none nxt') mC' π =
      .ok (((mkListClearEnv head none nxt', mC', π)),
        .returned (.ptrVal none)) :=
    memEvalStmtFuel_return F _ _ _ _ _
      (memEvalExpr_lit _ _ _ _) (by simp [evalExpr, litVal])
  have hR2 : memEvalStmtFuel F
      (.seq listClearLoop (.return_ (.lit .nullptr)))
      (mkListClearEnv head head none) m π =
      .ok (((mkListClearEnv head none nxt', mC', π)),
        .returned (.ptrVal none)) :=
    memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
      hloop hret
  have hR1 : memEvalStmtFuel F
      (.seq (.let_ "next" nodeTy (.lit .nullptr))
        (.seq listClearLoop (.return_ (.lit .nullptr))))
      (("cur", .ptrVal head) :: [("head", .ptrVal head)]) m π =
      .ok (((mkListClearEnv head none nxt', mC', π)),
        .returned (.ptrVal none)) :=
    memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
      hletN hR2
  have hB : memEvalStmtFuel F
      (.seq (.let_ "cur" nodeTy (.var "head"))
        (.seq (.let_ "next" nodeTy (.lit .nullptr))
          (.seq listClearLoop (.return_ (.lit .nullptr)))))
      [("head", .ptrVal head)] m π =
      .ok (((mkListClearEnv head none nxt', mC', π)),
        .returned (.ptrVal none)) :=
    memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
      hletC hR1
  have hfunc : listClearFunc.body = listClearBody := rfl
  rw [hfunc]
  unfold listClearBody
  exact ⟨_, hB, hdeadAll, hrestAll⟩

