import Circe.Hoare.Def
import Circe.CondFrame

/-- Literal evaluation, quantified once: every gallery `hlit`
    block is an instance of this
    (use-site: `hoare_lit_eval _ ρ m π`). -/
theorem hoare_lit_eval (l : CLit) (ρ : Env) (m : Mem) (π : Layout) :
    memEvalExpr (.lit l) ρ m π = .ok (litVal l) := by
  rw [memEvalExpr_lit]
  rfl

/-- Guard-hypothesis closure: from a proved guard evaluation,
    discharge the per-state guard premise of the `if` rules
    (use-site collapses to one line). -/
theorem hoare_guard_of (ρ : Env) (m : Mem) (π : Layout) (c : CExpr)
    (bv : Bool) (h : memEvalExpr c ρ m π = .ok (.b bv))
    (ρ' : Env) (m' : Mem) (π' : Layout)
    (hP : (ρ', m', π') = (ρ, m, π)) :
    memEvalExpr c ρ' m' π' = .ok (.b bv) := by
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  exact h

/-- `skip` leaves everything. -/
theorem htriple_skip (P : Env × Mem × Layout → Prop) :
    HTriple P .skip (fun st o => P st ∧ o = .fellThrough) := by
  intro F ρ m π hP
  exact ⟨ρ, m, π, .fellThrough, by cases F <;> rfl, hP, rfl⟩

/-- Sequencing with the mid-outcome pinned to `fellThrough`:
    straight-line bodies return last. Early-return propagation
    needs Mem-side seq-return equations that do not exist yet
    (only `memEvalStmtFuel_seq`, `_seq_err`, and
    `_seq_fallthrough` exist) — deferred with that lemma named
    rather than silently assumed. -/
theorem htriple_seq (P R : Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop) (a b : CStmt)
    (ha : HTriple P a (fun st o => o = .fellThrough ∧ R st))
    (hb : HTriple R b Q) :
    HTriple P (.seq a b) Q := by
  intro F ρ m π hP
  obtain ⟨ρ₁, m₁, π₁, o₁, ha', hmid⟩ := ha F ρ m π hP
  obtain ⟨rfl, hR⟩ := hmid
  obtain ⟨ρ₂, m₂, π₂, o₂, hb', hQ⟩ := hb F ρ₁ m₁ π₁ hR
  exact ⟨ρ₂, m₂, π₂, o₂,
    memEvalStmtFuel_seq F a b ρ m π ρ₁ m₁ π₁ ρ₂ m₂ π₂ o₂ ha' hb',
    hQ⟩

/-- Program-level sequencing at fixed fuel (the `∀ F` rule is
    this pointwise): both components run at the same `F`, memory
    threaded. Mid-outcome pinned to `fellThrough`: straight-line
    call spines return last. Same scope as `htriple_seq` one
    level down — early-return propagation needs prog-level
    seq-return equations that do not exist yet, deferred with
    that lemma named rather than silently assumed. -/
theorem htripleProg_seq_at (prog : Prog) (F : Nat)
    (P R : Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop) (a b : CStmt)
    (ha : HTripleProgAt prog F P a (fun st o => o = .fellThrough ∧ R st))
    (hb : HTripleProgAt prog F R b Q) :
    HTripleProgAt prog F P (.seq a b) Q := by
  intro ρ m π hP
  obtain ⟨ρ₁, m₁, π₁, o₁, ha', hmid⟩ := ha ρ m π hP
  obtain ⟨rfl, hR⟩ := hmid
  obtain ⟨ρ₂, m₂, π₂, o₂, hb', hQ⟩ := hb ρ₁ m₁ π₁ hR
  exact ⟨ρ₂, m₂, π₂, o₂,
    memEvalProgStmt_seq prog F a b ρ m π ρ₁ m₁ π₁ ρ₂ m₂ π₂ o₂ ha' hb',
    hQ⟩

/-- `∀ F` program-level sequencing, pointwise from
    `htripleProg_seq_at`. -/
theorem htripleProg_seq (prog : Prog)
    (P R : Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop) (a b : CStmt)
    (ha : HTripleProg prog P a (fun st o => o = .fellThrough ∧ R st))
    (hb : HTripleProg prog R b Q) :
    HTripleProg prog P (.seq a b) Q :=
  fun F => htripleProg_seq_at prog F P R Q a b (ha F) (hb F)

/-- Program-level frame for `.callProg`: a caller-memory frame
    `R` rides across the call untouched. This is definitional,
    not deep: the callee body runs on fresh entry blocks
    (`memEvalProgFunc` binds into `emptyMem`, so caller memory
    is unreachable) and the equation keeps `(m, π)` identical —
    no address-inequality side conditions like `cellAt` framing.
    The real frame work (overlapping footprints, multi-word
    assertions) lives at statement level (H-track), not here. -/
theorem htripleProg_callProg_frame_at (prog : Prog) (F : Nat)
    (P : Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop)
    (R : Mem → Prop)
    (dst f : String) (xs : List String)
    (h : ∀ ρ m π, P (ρ, m, π) → R m →
      ∃ vs callee ret, lookupArgs ρ xs = some vs ∧
        findFunc prog f = some callee ∧
        memEvalProgFunc prog F callee vs = .ok ret ∧
        Q (envExtend ρ dst ret, m, π) .fellThrough) :
    HTripleProgAt prog (F + 1)
      (fun st => P st ∧ R st.2.1)
      (.callProg dst f xs)
      (fun st o => Q st o ∧ R st.2.1) := by
  intro ρ m π hP
  obtain ⟨hP', hR⟩ := hP
  obtain ⟨vs, callee, ret, hargs, hfind, hcall, hQ⟩ :=
    h ρ m π hP' hR
  exact ⟨envExtend ρ dst ret, m, π, .fellThrough,
    memEvalProgStmt_callProg_ok prog F dst f xs ρ m π vs callee ret
      hargs hfind hcall,
    hQ, hR⟩

/-- Program-level frame for `.callRet`: same shape at the same
    fuel (the leaf evaluator takes no fuel step — cf.
    `memEvalProgStmt_callRet_ok`). -/
theorem htripleProg_callRet_frame_at (prog : Prog) (F : Nat)
    (P : Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop)
    (R : Mem → Prop)
    (dst f : String) (xs : List String)
    (h : ∀ ρ m π, P (ρ, m, π) → R m →
      ∃ vs callee ret, lookupArgs ρ xs = some vs ∧
        findFunc prog f = some callee ∧
        memEvalFuncFuel F callee vs = .ok ret ∧
        Q (envExtend ρ dst ret, m, π) .fellThrough) :
    HTripleProgAt prog F
      (fun st => P st ∧ R st.2.1)
      (.callRet dst f xs)
      (fun st o => Q st o ∧ R st.2.1) := by
  intro ρ m π hP
  obtain ⟨hP', hR⟩ := hP
  obtain ⟨vs, callee, ret, hargs, hfind, hcall, hQ⟩ :=
    h ρ m π hP' hR
  exact ⟨envExtend ρ dst ret, m, π, .fellThrough,
    memEvalProgStmt_callRet_ok prog F dst f xs ρ m π vs callee ret
      hargs hfind hcall,
    hQ, hR⟩

/-- Program-level call: the caller triple for `.callProg` from
    the callee run at one less fuel. The `.callProg` arm errors
    at zero fuel, so this is `At (F + 1)`, not `∀ F` — the U2
    contract + transfer plug in as `hcall`, never re-verified.
    By-value threading: only `dst` extends, `(m, π)` unchanged. -/
theorem htripleProg_callProg_at (prog : Prog) (F : Nat)
    (P : Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop)
    (dst f : String) (xs : List String)
    (h : ∀ ρ m π, P (ρ, m, π) →
      ∃ vs callee ret, lookupArgs ρ xs = some vs ∧
        findFunc prog f = some callee ∧
        memEvalProgFunc prog F callee vs = .ok ret ∧
        Q (envExtend ρ dst ret, m, π) .fellThrough) :
    HTripleProgAt prog (F + 1) P (.callProg dst f xs) Q := by
  intro ρ m π hP
  obtain ⟨vs, callee, ret, hargs, hfind, hcall, hQ⟩ := h ρ m π hP
  exact ⟨envExtend ρ dst ret, m, π, .fellThrough,
    memEvalProgStmt_callProg_ok prog F dst f xs ρ m π vs callee ret
      hargs hfind hcall,
    hQ⟩

/-- Consequence (pre-strengthen, post-weaken). -/
theorem htriple_consequence (P P' : Env × Mem × Layout → Prop)
    (Q Q' : Env × Mem × Layout → Outcome → Prop) (s : CStmt)
    (hpre : ∀ st, P st → P' st)
    (h : HTriple P' s Q)
    (hpost : ∀ st o, Q st o → Q' st o) :
    HTriple P s Q' := by
  intro F ρ m π hP
  obtain ⟨ρ', m', π', o, hev, hQ⟩ := h F ρ m π (hpre _ hP)
  exact ⟨ρ', m', π', o, hev, hpost _ _ hQ⟩

/-- `mstore` with framing: stores `xv`, produces the stored-cell
    fact, preserves one framed cell across the store. The store
    index is pinned to `0`, which is complete rather than
    limiting: `cellAt` is a singleton assertion (`memFind m a =
    some ⟨t, true, [v]⟩`), so any successful store into a
    `cellAt` cell is at index 0 — anything else is OOB on the
    1-word block. Multi-word indexed assertions wait for H2. -/
theorem htriple_mstore_frame (s : String) (ie ve : CExpr)
    (ρ : Env) (m : Mem) (π : Layout)
    (i : BitVec 64) (xv : BitVec 32) (a : Addr) (t : Nat)
    (m' : Mem) (wold : BitVec 32)
    (b : Addr) (t₂ : Nat) (qv : BitVec 32)
    (hi : memEvalExpr ie ρ m π = .ok (.u64 i))
    (hi0 : i.toNat = 0)
    (hv : memEvalExpr ve ρ m π = .ok (.i32 xv))
    (hlay : layoutLookup π s = some (a, t))
    (hstore : memStore m a t i.toNat xv = .ok m')
    (hpre : cellAt m a t wold)
    (hq : cellAt m b t₂ qv) (hne : b ≠ a) :
    HTriple (fun st => st = (ρ, m, π))
      (.mstore s ie ve)
      (fun st o => st = (ρ, m', π) ∧ o = .fellThrough ∧
        cellAt m' a t xv ∧ cellAt m' b t₂ qv) := by
  intro F ρ₀ m₀ π₀ hP
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  refine ⟨ρ₀, m', π₀, .fellThrough,
    memEvalStmtFuel_mstore_ok F s ie ve ρ₀ m₀ π₀ i xv a t m'
      hi hv hlay hstore,
    rfl, rfl, ?_, ?_⟩
  · have hstore0 : memStore m₀ a t 0 xv = .ok m' := by
      rw [← hi0]; exact hstore
    exact memFind_cell_store _ _ _ _ _ hpre _ hstore0
  · unfold cellAt
    rw [memFind_memStore_other _ _ a b t i.toNat _ hstore hne]
    exact hq

/-- Expression-level load helper: `mload` has no value mirror (the
    pure evaluator reports `AssertFail` on any evaluated index),
    so loads cannot form statement triples — they appear inside
    `mstore` value expressions, where only this Mem-side equation
    is needed. -/
theorem hexpr_mload (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (i : BitVec 64) (w : BitVec 32)
    (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hi : memEvalExpr ie ρ m π = .ok (.u64 i))
    (hmem : memLoad m a t i.toNat = .ok w) :
    memEvalExpr (.mload s ie) ρ m π = .ok (.i32 w) :=
  memEvalExpr_mload_hit s ie ρ m π i w a t hlay hi hmem

/-- Value-side `usub` on two `u32`-valued expressions (mirrors
    `evalExpr_usub_u64u64`; the countdown body decrements `u32`). -/
theorem heval_usub_u32 (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 32)
    (h₁ : evalExpr e₁ ρ = .ok (.u32 x))
    (h₂ : evalExpr e₂ ρ = .ok (.u32 y)) :
    evalExpr (.usub e₁ e₂) ρ = .ok (.u32 (x - y)) := by
  simp [evalExpr, h₁, h₂]

/-- Value-side `une` on two `u32`-valued expressions (the
    countdown guard shape). -/
theorem heval_une_u32 (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 32)
    (h₁ : evalExpr e₁ ρ = .ok (.u32 x))
    (h₂ : evalExpr e₂ ρ = .ok (.u32 y)) :
    evalExpr (.une e₁ e₂) ρ = .ok (.b (x != y)) := by
  simp [evalExpr, h₁, h₂]

/-- `if_` on a true guard runs the then-branch. -/
theorem htriple_if_true (P : Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop)
    (c : CExpr) (t e : CStmt)
    (hc : ∀ ρ m π, P (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b true))
    (ht : HTriple P t Q) :
    HTriple P (.if_ c t e) Q := by
  intro F ρ m π hP
  have hguard := hc ρ m π hP
  obtain ⟨ρ', m', π', o, hev, hQ⟩ := ht F ρ m π hP
  exact ⟨ρ', m', π', o,
    by rw [memEvalStmtFuel_if_true F c t e ρ m π hguard]; exact hev,
    hQ⟩

/-- `if_` on a false guard runs the else-branch. -/
theorem htriple_if_false (P : Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop)
    (c : CExpr) (t e : CStmt)
    (hc : ∀ ρ m π, P (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b false))
    (he : HTriple P e Q) :
    HTriple P (.if_ c t e) Q := by
  intro F ρ m π hP
  have hguard := hc ρ m π hP
  obtain ⟨ρ', m', π', o, hev, hQ⟩ := he F ρ m π hP
  exact ⟨ρ', m', π', o,
    by rw [memEvalStmtFuel_if_false F c t e ρ m π hguard]; exact hev,
    hQ⟩

/-- `return_` delivers its value as a `.returned` outcome —
    the first rule producing a non-`fellThrough` post. -/
theorem htriple_return (e : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (v : Value)
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v) :
    HTriple (fun st => st = (ρ, m, π)) (.return_ e)
      (fun st o => st = (ρ, m, π) ∧ o = .returned v) := by
  intro F ρ₀ m₀ π₀ hP
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  exact ⟨ρ₀, m₀, π₀, .returned v,
    memEvalStmtFuel_return F e ρ₀ m₀ π₀ v h hv, rfl, rfl⟩

/-- `let_` binds a pure value, extending the environment. The
    allocating arms (`vnew` / `boxNew` / `vgrowNew`) are excluded
    by hypotheses — the caller discharges them per concrete RHS
    (each is a constructor discrimination). -/
theorem htriple_let (x : String) (ty : CType) (e : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (v : Value)
    (hnot : ∀ se, e ≠ .vnew se)
    (hnotBox : ∀ se, e ≠ .boxNew se)
    (hnotGrow : ∀ ce, e ≠ .vgrowNew ce)
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v) :
    HTriple (fun st => st = (ρ, m, π)) (.let_ x ty e)
      (fun st o => st = (((x, v) :: ρ, m, π)) ∧ o = .fellThrough) := by
  intro F ρ₀ m₀ π₀ hP
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  exact ⟨_, _, _, _, memEvalStmtFuel_let_pure F x ty e ρ₀ m₀ π₀ v
    hnot hnotBox hnotGrow h hv, rfl, rfl⟩

/-- `assign` updates the environment binding, memory untouched. -/
theorem htriple_assign (x : String) (e : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (v : Value) (ρ' : Env)
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v) (hu : envUpdate ρ x v = some ρ') :
    HTriple (fun st => st = (ρ, m, π)) (.assign x e)
      (fun st o => st = (ρ', m, π) ∧ o = .fellThrough) := by
  intro F ρ₀ m₀ π₀ hP
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  exact ⟨ρ', m₀, π₀, .fellThrough,
    memEvalStmtFuel_assign F x e ρ₀ m₀ π₀ v ρ' h hv hu, rfl, rfl⟩

/-- `while_` with a fuel-indexed invariant. The index is
    load-bearing, not decorative: at fuel 0 a true-guard loop
    errors (`AssertFail` via the zero handler), so a fuel-blind
    `∀ F` triple over a looping state is unprovable — `I 0`
    admits only guard-false states, and each true-guard step
    delivers an `I k` state from `I (k+1)`. Fuel does the
    bounding, so no separate termination measure is needed for
    soundness. Body iterations must end `fellThrough` or
    `continued`; `broke` / `returned` bodies are excluded (named
    limitation — the handler arms exist but the exit-post
    plumbing is deferred). -/
theorem htriple_while_at (I : Nat → Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop) (c : CExpr) (b : CStmt)
    (hzero : ∀ ρ m π, I 0 (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b false))
    (hexit : ∀ k ρ m π, I k (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b false) → Q (ρ, m, π) .fellThrough)
    (hdec : ∀ k ρ m π, I (k + 1) (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b false) ∨
      memEvalExpr c ρ m π = .ok (.b true))
    (hstep : ∀ k ρ m π, I (k + 1) (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b true) →
      ∃ Pmid Qmid, HTriple Pmid b Qmid ∧ Pmid (ρ, m, π) ∧
        (∀ ρ' m' π' o, Qmid (ρ', m', π') o →
          (o = .fellThrough ∨ o = .continued) ∧ I k (ρ', m', π'))) :
    ∀ F, HTripleAt F (fun st => I F st) (.while_ c b) Q := by
  intro F
  induction F with
  | zero =>
    intro ρ m π hP
    have hguard := hzero ρ m π hP
    exact ⟨ρ, m, π, .fellThrough,
      memEvalStmtFuel_while_false 0 c b ρ m π hguard,
      hexit 0 ρ m π hP hguard⟩
  | succ k ih =>
    intro ρ m π hP
    obtain hgf | hgt := hdec k ρ m π hP
    · exact ⟨ρ, m, π, .fellThrough,
        memEvalStmtFuel_while_false (k + 1) c b ρ m π hgf,
        hexit (k + 1) ρ m π hP hgf⟩
    · obtain ⟨Pmid, Qmid, hbody, hpre, hpost⟩ := hstep k ρ m π hP hgt
      obtain ⟨ρ₁, m₁, π₁, o₁, hev, hQ⟩ := hbody k ρ m π hpre
      obtain ⟨ho, hI⟩ := hpost ρ₁ m₁ π₁ o₁ hQ
      obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := ih ρ₁ m₁ π₁ hI
      refine ⟨ρ₂, m₂, π₂, o₂, ?_, hQ₂⟩
      rw [memEvalStmtFuel_while_true k c b ρ m π hgt, hev]
      obtain rfl | rfl := ho
      · exact hev₂
      · exact hev₂

/-- Program-level `while_` rule: mirrors `htriple_while_at` over
    `memEvalProgStmt`, so loop bodies with `callRet` leaves (every
    admitted vector loop) prove as rule applications instead of
    hand-rolled fuel inductions. Same four premises; the
    triple-step consumes/produces `HTripleProgAt` at the
    iteration fuel. -/
theorem htripleProg_while_at (prog : Prog)
    (I : Nat → Env × Mem × Layout → Prop)
    (Q : Env × Mem × Layout → Outcome → Prop) (c : CExpr) (b : CStmt)
    (hzero : ∀ ρ m π, I 0 (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b false))
    (hexit : ∀ k ρ m π, I k (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b false) → Q (ρ, m, π) .fellThrough)
    (hdec : ∀ k ρ m π, I (k + 1) (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b false) ∨
      memEvalExpr c ρ m π = .ok (.b true))
    (hstep : ∀ k ρ m π, I (k + 1) (ρ, m, π) →
      memEvalExpr c ρ m π = .ok (.b true) →
      ∃ Pmid Qmid, HTripleProg prog Pmid b Qmid ∧ Pmid (ρ, m, π) ∧
        (∀ ρ' m' π' o, Qmid (ρ', m', π') o →
          (o = .fellThrough ∨ o = .continued) ∧ I k (ρ', m', π'))) :
    ∀ F, HTripleProgAt prog F (fun st => I F st) (.while_ c b) Q := by
  intro F
  induction F with
  | zero =>
    intro ρ m π hP
    have hguard := hzero ρ m π hP
    exact ⟨ρ, m, π, .fellThrough,
      memEvalProgStmt_while_false prog 0 c b ρ m π hguard,
      hexit 0 ρ m π hP hguard⟩
  | succ k ih =>
    intro ρ m π hP
    obtain hgf | hgt := hdec k ρ m π hP
    · exact ⟨ρ, m, π, .fellThrough,
        memEvalProgStmt_while_false prog (k + 1) c b ρ m π hgf,
        hexit (k + 1) ρ m π hP hgf⟩
    · obtain ⟨Pmid, Qmid, hbody, hpre, hpost⟩ := hstep k ρ m π hP hgt
      obtain ⟨ρ₁, m₁, π₁, o₁, hev, hQ⟩ := hbody k ρ m π hpre
      obtain ⟨ho, hI⟩ := hpost ρ₁ m₁ π₁ o₁ hQ
      obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := ih ρ₁ m₁ π₁ hI
      refine ⟨ρ₂, m₂, π₂, o₂, ?_, hQ₂⟩
      rw [memEvalProgStmt_while_true prog k c b ρ m π hgt, hev]
      obtain rfl | rfl := ho
      · exact hev₂
      · exact hev₂

/-- `u64` length round-trip for loop bounds: the bound literal
    evaluates back to the list length (needs `hn`). -/
theorem ofNat64_toNat (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

/-- `ult` against a `u64` length literal, true case. -/
theorem ult_ofNat64_true (n : Nat) (hn : n < 2 ^ 64) (iv : BitVec 64)
    (hlt : iv.toNat < n) : iv.ult (BitVec.ofNat 64 n) = true := by
  rw [BitVec.ult_eq_decide, ofNat64_toNat n hn]
  exact decide_eq_true hlt

/-- `ult` against a `u64` length literal, false case. -/
theorem ult_ofNat64_false (n : Nat) (hn : n < 2 ^ 64) (iv : BitVec 64)
    (hle : n ≤ iv.toNat) : iv.ult (BitVec.ofNat 64 n) = false := by
  rw [BitVec.ult_eq_decide, ofNat64_toNat n hn]
  exact decide_eq_false (Nat.not_lt.mpr hle)

/-- `u64` successor stays in bounds over a short length. -/
theorem u64_succ_toNat (iv : BitVec 64) (n : Nat) (hn : n < 2 ^ 64)
    (hlt : iv.toNat < n) : (iv + 1).toNat = iv.toNat + 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]

/-- `ult` guard evaluation under the shared `i`/`len` loop
    environment (both array loops use this exact guard). -/
theorem memEvalExpr_ult_ilen (ρ : Env) (m' : Mem) (π' : Layout)
    (iv : BitVec 64) (n : Nat)
    (hi : envLookup ρ "i" = some (.u64 iv))
    (hlen : envLookup ρ "len" = some (.u64 (BitVec.ofNat 64 n))) :
    memEvalExpr (.ult (.var "i") (.var "len")) ρ m' π'
      = .ok (.b (iv.ult (BitVec.ofNat 64 n))) := by
  rw [memEvalExpr_ult_agree _ _ ρ m' π'
    (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _),
    evalExpr_ult_u64 _ _ ρ iv _ (evalExpr_var_hit _ _ _ hi)
      (evalExpr_var_hit _ _ _ hlen)]

/-- Loop-index environment lookups, closed in one step from the
    environment shape (both array loops share it). -/
theorem envLookup_ilen (ρ : Env) (iv : BitVec 64) (n : Nat) (rest : Env)
    (hρ : ρ = ("i", .u64 iv) ::
      ("len", .u64 (BitVec.ofNat 64 n)) :: rest) :
    envLookup ρ "i" = some (.u64 iv) ∧
      envLookup ρ "len" = some (.u64 (BitVec.ofNat 64 n)) := by
  rw [hρ]
  exact ⟨by simp [envLookup], by simp [envLookup]⟩

/-- Increment-step facts for `i = i + 1` under the shared loop
    environment: agreement, value, and update, from the shape. -/
theorem hoare_uadd_incr_facts (ρ' : Env) (m₀ : Mem) (π' : Layout)
    (iv : BitVec 64) (rest : Env) (n : Nat)
    (hρ : ρ' = ("i", .u64 iv) ::
      ("len", .u64 (BitVec.ofNat 64 n)) :: rest) :
    memEvalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' m₀ π'
      = evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' ∧
    evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' = .ok (.u64 (iv + 1)) ∧
    envUpdate ρ' "i" (.u64 (iv + 1))
      = some ((("i", .u64 (iv + 1)) ::
        ("len", .u64 (BitVec.ofNat 64 n)) :: rest)) := by
  have hi' : envLookup ρ' "i" = some (.u64 iv) := by
    rw [hρ]; simp [envLookup]
  refine ⟨?_, ?_, ?_⟩
  · exact memEvalExpr_uadd_agree _ _ _ _ _
      (by rw [memEvalExpr_var]) (by rw [memEvalExpr_lit])
  · exact evalExpr_uadd_u64 _ _ _ _ _ (evalExpr_var_hit _ _ _ hi') rfl
  · rw [hρ]; exact envUpdate_hit _ _ _ _
