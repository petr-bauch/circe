-- Hoare gallery (H1): the two-cell `pa[0] += 1; pb[0] += 1`
-- body proved end-to-end with the `Circe.Hoare` rule library.
-- Overflow-freedom is explicit hypothesis debt (`hov`/`how`);
-- the frame leg carries the untouched cell through each store.
-- Loads appear inside `mstore` value expressions via
-- `hexpr_mload` (`mload` has no value mirror, so it cannot form
-- statement triples).
--
-- Compile-gated: building this root (`lake build HoareGallery`)
-- is the check.
import Circe.Hoare.Def
import Circe.Hoare.Rules
import Circe.Emit.AliasCond
import Circe.Emit.CondPair

namespace HoareGallery

/-- The gallery body, shared by the proof below and the
    closed-instance runtime check in `main`. -/
def galleryBody : CStmt :=
  .seq (.mstore "pa" (.lit (.u64 0))
          (.add (.mload "pa" (.lit (.u64 0))) (.lit (.i32 1))))
        (.mstore "pb" (.lit (.u64 0))
          (.add (.mload "pb" (.lit (.u64 0))) (.lit (.i32 1))))

theorem hoare_gallery (ρ : Env) (m : Mem) (π : Layout)
    (a b : Addr) (t₁ t₂ : Nat) (v w : BitVec 32)
    (ma mb : Mem)
    (hla : layoutLookup π "pa" = some (a, t₁))
    (hlb : layoutLookup π "pb" = some (b, t₂))
    (hca : cellAt m a t₁ v) (hcb : cellAt m b t₂ w)
    (hne : b ≠ a)
    (hma : memLoad m a t₁ 0 = .ok v)
    (hmb : memLoad ma b t₂ 0 = .ok w)
    (hov : checkedAddI32 v 1 = .ok (v + 1))
    (how : checkedAddI32 w 1 = .ok (w + 1))
    (hsa : memStore m a t₁ 0 (v + 1) = .ok ma)
    (hsb : memStore ma b t₂ 0 (w + 1) = .ok mb) :
    HTriple (fun st => st = (ρ, m, π))
      galleryBody
      (fun st o => st = (ρ, mb, π) ∧ o = .fellThrough ∧
        cellAt mb a t₁ (v + 1) ∧ cellAt mb b t₂ (w + 1)) := by
  have hv1 : memEvalExpr
      (.add (.mload "pa" (.lit (.u64 0))) (.lit (.i32 1))) ρ m π
      = .ok (.i32 (v + 1)) := by
    have h := memEvalExpr_add_ok _ _ ρ m π v 1
      (hexpr_mload "pa" (.lit (.u64 0)) ρ m π 0 v a t₁
        hla (hoare_lit_eval (.u64 0) ρ m π) hma)
      (hoare_lit_eval (.i32 1) ρ m π)
    rw [hov] at h
    exact h
  have hv2 : memEvalExpr
      (.add (.mload "pb" (.lit (.u64 0))) (.lit (.i32 1))) ρ ma π
      = .ok (.i32 (w + 1)) := by
    have h := memEvalExpr_add_ok _ _ ρ ma π w 1
      (hexpr_mload "pb" (.lit (.u64 0)) ρ ma π 0 w b t₂
        hlb (hoare_lit_eval (.u64 0) ρ ma π) hmb)
      (hoare_lit_eval (.i32 1) ρ ma π)
    rw [how] at h
    exact h
  have hfirst : HTriple (fun st => st = (ρ, m, π))
      (.mstore "pa" (.lit (.u64 0))
        (.add (.mload "pa" (.lit (.u64 0))) (.lit (.i32 1))))
      (fun st o => o = .fellThrough ∧ st = (ρ, ma, π) ∧
        cellAt ma a t₁ (v + 1) ∧ cellAt ma b t₂ w) :=
    htriple_consequence _ _ _ _
      (.mstore "pa" (.lit (.u64 0))
        (.add (.mload "pa" (.lit (.u64 0))) (.lit (.i32 1))))
      (fun _ => id)
      (htriple_mstore_frame "pa" (.lit (.u64 0))
        (.add (.mload "pa" (.lit (.u64 0))) (.lit (.i32 1)))
        ρ m π 0 (v + 1) a t₁ ma v b t₂ w
        (hoare_lit_eval (.u64 0) ρ m π) rfl hv1 hla hsa hca hcb hne)
      (fun st o h => ⟨h.2.1, h.1, h.2.2.1, h.2.2.2⟩)
  have hsecond : HTriple
      (fun st => st = (ρ, ma, π) ∧
        cellAt ma a t₁ (v + 1) ∧ cellAt ma b t₂ w)
      (.mstore "pb" (.lit (.u64 0))
        (.add (.mload "pb" (.lit (.u64 0))) (.lit (.i32 1))))
      (fun st o => st = (ρ, mb, π) ∧ o = .fellThrough ∧
        cellAt mb a t₁ (v + 1) ∧ cellAt mb b t₂ (w + 1)) := by
    intro F ρ₀ m₀ π₀ hP
    obtain ⟨⟨rfl, rfl, rfl⟩, hA, hB⟩ := hP
    have hfr := htriple_mstore_frame "pb" (.lit (.u64 0))
      (.add (.mload "pb" (.lit (.u64 0))) (.lit (.i32 1)))
      ρ ma π 0 (w + 1) b t₂ mb w a t₁ (v + 1)
      (hoare_lit_eval (.u64 0) ρ ma π) rfl hv2 hlb hsb hB hA (Ne.symm hne)
    obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := hfr F ρ ma π rfl
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, hW, hF⟩ := hQ₂
    exact ⟨ρ, mb, π, .fellThrough, hev₂, rfl, rfl, hF, hW⟩
  exact htriple_seq _ _ _ _ _ hfirst hsecond

/-- `alias_cond` under `c = true` over the real emitted body:
    the `if_` rule fires the `p`-store, framing carries both
    cells through the `q`-store, `return_` delivers the void
    zero word. First triple exercising H1's `if`-rules. -/
theorem hoare_aliasCond_true (ρ : Env) (m : Mem) (π : Layout)
    (a b : Addr) (t₁ t₂ : Nat) (p q : BitVec 32)
    (ma mb : Mem)
    (hla : layoutLookup π "p" = some (a, t₁))
    (hlb : layoutLookup π "q" = some (b, t₂))
    (hc : envLookup ρ "c" = some (.b true))
    (hca : cellAt m a t₁ p) (hcb : cellAt m b t₂ q)
    (hne : b ≠ a)
    (hma : memLoad m a t₁ 0 = .ok p)
    (hmb : memLoad ma b t₂ 0 = .ok q)
    (hov : checkedAddI32 p 1 = .ok (p + 1))
    (how : checkedAddI32 q 2 = .ok (q + 2))
    (hsa : memStore m a t₁ 0 (p + 1) = .ok ma)
    (hsb : memStore ma b t₂ 0 (q + 2) = .ok mb) :
    HTriple (fun st => st = (ρ, m, π))
      aliasCondFunc.body
      (fun st o => st = (ρ, mb, π) ∧ o = .returned (.u32 0) ∧
        cellAt mb a t₁ (p + 1) ∧ cellAt mb b t₂ (q + 2)) := by
  have hguard : memEvalExpr (.var "c") ρ m π = .ok (.b true) := by
    rw [memEvalExpr_var]
    simp [evalExpr, hc]
  have hvp : memEvalExpr
      (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))) ρ m π
      = .ok (.i32 (p + 1)) := by
    have h := memEvalExpr_add_ok _ _ ρ m π p 1
      (hexpr_mload "p" (.lit (.u64 0)) ρ m π 0 p a t₁
        hla (hoare_lit_eval (.u64 0) ρ m π) hma)
      (hoare_lit_eval (.i32 1) ρ m π)
    rw [hov] at h
    exact h
  have hvq : memEvalExpr
      (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))) ρ ma π
      = .ok (.i32 (q + 2)) := by
    have h := memEvalExpr_add_ok _ _ ρ ma π q 2
      (hexpr_mload "q" (.lit (.u64 0)) ρ ma π 0 q b t₂
        hlb (hoare_lit_eval (.u64 0) ρ ma π) hmb)
      (hoare_lit_eval (.i32 2) ρ ma π)
    rw [how] at h
    exact h
  have hif : HTriple (fun st => st = (ρ, m, π))
      (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      (fun st o => o = .fellThrough ∧ st = (ρ, ma, π) ∧
        cellAt ma a t₁ (p + 1) ∧ cellAt ma b t₂ q) :=
    htriple_consequence _ _ _ _ _ (fun _ => id)
      (htriple_if_true _ _ _ _ _
        (fun _ _ _ hP => hoare_guard_of _ _ _ _ _ hguard _ _ _ hP)
        (htriple_mstore_frame "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1)))
          ρ m π 0 (p + 1) a t₁ ma p b t₂ q
          (hoare_lit_eval (.u64 0) ρ m π) rfl hvp hla hsa hca hcb hne))
      (fun st o h => ⟨h.2.1, h.1, h.2.2.1, h.2.2.2⟩)
  have htail : HTriple
      (fun st => st = (ρ, ma, π) ∧
        cellAt ma a t₁ (p + 1) ∧ cellAt ma b t₂ q)
      (.seq (.mstore "q" (.lit (.u64 0))
              (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
            (.return_ (.lit (.u32 0))))
      (fun st o => st = (ρ, mb, π) ∧ o = .returned (.u32 0) ∧
        cellAt mb a t₁ (p + 1) ∧ cellAt mb b t₂ (q + 2)) := by
    have hstore : HTriple
        (fun st => st = (ρ, ma, π) ∧
          cellAt ma a t₁ (p + 1) ∧ cellAt ma b t₂ q)
        (.mstore "q" (.lit (.u64 0))
          (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
        (fun st o => o = .fellThrough ∧ st = (ρ, mb, π) ∧
          cellAt mb a t₁ (p + 1) ∧ cellAt mb b t₂ (q + 2)) := by
      intro F ρ₀ m₀ π₀ hP
      obtain ⟨⟨rfl, rfl, rfl⟩, hA, hB⟩ := hP
      have hfr := htriple_mstore_frame "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2)))
        ρ ma π 0 (q + 2) b t₂ mb q a t₁ (p + 1)
        (hoare_lit_eval (.u64 0) ρ ma π) rfl hvq hlb hsb hB hA (Ne.symm hne)
      obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := hfr F ρ ma π rfl
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl, hW, hF⟩ := hQ₂
      exact ⟨ρ, mb, π, .fellThrough, hev₂, rfl, rfl, hF, hW⟩
    have hret : HTriple
        (fun st => st = (ρ, mb, π) ∧
          cellAt mb a t₁ (p + 1) ∧ cellAt mb b t₂ (q + 2))
        (.return_ (.lit (.u32 0)))
        (fun st o => st = (ρ, mb, π) ∧ o = .returned (.u32 0) ∧
          cellAt mb a t₁ (p + 1) ∧ cellAt mb b t₂ (q + 2)) := by
      intro F ρ₀ m₀ π₀ hP
      obtain ⟨⟨rfl, rfl, rfl⟩, hA, hB⟩ := hP
      have hfr := htriple_return (.lit (.u32 0)) ρ mb π (.u32 0)
        (memEvalExpr_lit _ _ _ _) rfl
      obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := hfr F ρ mb π rfl
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hQ₂
      exact ⟨ρ, mb, π, .returned (.u32 0), hev₂, rfl, rfl, hA, hB⟩
    exact htriple_seq _ _ _ _ _ hstore hret
  exact htriple_seq _ _ _ _ _ hif htail

/-- `alias_cond` under `c = false`: the `skip` branch leaves `p`
    alone (via consequence over `htriple_skip`), then the same
    `q`-store + void return. -/
theorem hoare_aliasCond_false (ρ : Env) (m : Mem) (π : Layout)
    (a b : Addr) (t₁ t₂ : Nat) (p q : BitVec 32)
    (mb : Mem)
    (_hla : layoutLookup π "p" = some (a, t₁))
    (hlb : layoutLookup π "q" = some (b, t₂))
    (hc : envLookup ρ "c" = some (.b false))
    (hca : cellAt m a t₁ p) (hcb : cellAt m b t₂ q)
    (hne : b ≠ a)
    (hmb : memLoad m b t₂ 0 = .ok q)
    (how : checkedAddI32 q 2 = .ok (q + 2))
    (hsb : memStore m b t₂ 0 (q + 2) = .ok mb) :
    HTriple (fun st => st = (ρ, m, π))
      aliasCondFunc.body
      (fun st o => st = (ρ, mb, π) ∧ o = .returned (.u32 0) ∧
        cellAt mb a t₁ p ∧ cellAt mb b t₂ (q + 2)) := by
  have hguard : memEvalExpr (.var "c") ρ m π = .ok (.b false) := by
    rw [memEvalExpr_var]
    simp [evalExpr, hc]
  have hvq : memEvalExpr
      (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))) ρ m π
      = .ok (.i32 (q + 2)) := by
    have h := memEvalExpr_add_ok _ _ ρ m π q 2
      (hexpr_mload "q" (.lit (.u64 0)) ρ m π 0 q b t₂
        hlb (hoare_lit_eval (.u64 0) ρ m π) hmb)
      (hoare_lit_eval (.i32 2) ρ m π)
    rw [how] at h
    exact h
  have hskip : HTriple (fun st => st = (ρ, m, π)) .skip
      (fun st o => o = .fellThrough ∧ st = (ρ, m, π) ∧
        cellAt m a t₁ p ∧ cellAt m b t₂ q) :=
    htriple_consequence _ _ _ _ .skip (fun _ => id)
      (htriple_skip _)
      (fun st o h => ⟨h.2, h.1, hca, hcb⟩)
  have hif : HTriple (fun st => st = (ρ, m, π))
      (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      (fun st o => o = .fellThrough ∧ st = (ρ, m, π) ∧
        cellAt m a t₁ p ∧ cellAt m b t₂ q) :=
    htriple_consequence _ _ _ _ _ (fun _ => id)
      (htriple_if_false _ _ _ _ _
        (fun _ _ _ hP => hoare_guard_of _ _ _ _ _ hguard _ _ _ hP)
        hskip)
      (fun st o h => h)
  have htail : HTriple
      (fun st => st = (ρ, m, π) ∧
        cellAt m a t₁ p ∧ cellAt m b t₂ q)
      (.seq (.mstore "q" (.lit (.u64 0))
              (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
            (.return_ (.lit (.u32 0))))
      (fun st o => st = (ρ, mb, π) ∧ o = .returned (.u32 0) ∧
        cellAt mb a t₁ p ∧ cellAt mb b t₂ (q + 2)) := by
    have hstore : HTriple
        (fun st => st = (ρ, m, π) ∧
          cellAt m a t₁ p ∧ cellAt m b t₂ q)
        (.mstore "q" (.lit (.u64 0))
          (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
        (fun st o => o = .fellThrough ∧ st = (ρ, mb, π) ∧
          cellAt mb a t₁ p ∧ cellAt mb b t₂ (q + 2)) := by
      intro F ρ₀ m₀ π₀ hP
      obtain ⟨⟨rfl, rfl, rfl⟩, hA, hB⟩ := hP
      have hfr := htriple_mstore_frame "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2)))
        ρ m π 0 (q + 2) b t₂ mb q a t₁ p
        (hoare_lit_eval (.u64 0) ρ m π) rfl hvq hlb hsb hB hA (Ne.symm hne)
      obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := hfr F ρ m π rfl
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl, hW, hF⟩ := hQ₂
      exact ⟨ρ, mb, π, .fellThrough, hev₂, rfl, rfl, hF, hW⟩
    have hret : HTriple
        (fun st => st = (ρ, mb, π) ∧
          cellAt mb a t₁ p ∧ cellAt mb b t₂ (q + 2))
        (.return_ (.lit (.u32 0)))
        (fun st o => st = (ρ, mb, π) ∧ o = .returned (.u32 0) ∧
          cellAt mb a t₁ p ∧ cellAt mb b t₂ (q + 2)) := by
      intro F ρ₀ m₀ π₀ hP
      obtain ⟨⟨rfl, rfl, rfl⟩, hA, hB⟩ := hP
      have hfr := htriple_return (.lit (.u32 0)) ρ mb π (.u32 0)
        (memEvalExpr_lit _ _ _ _) rfl
      obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := hfr F ρ mb π rfl
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hQ₂
      exact ⟨ρ, mb, π, .returned (.u32 0), hev₂, rfl, rfl, hA, hB⟩
    exact htriple_seq _ _ _ _ _ hstore hret
  exact htriple_seq _ _ _ _ _ hif htail

/-- Countdown body: `while (n != 0) { n = n - 1 }` over a `u32`
    env variable — the first loop gallery (no Mem cells). -/
def countdownBody : CStmt :=
  .while_ (.une (.var "n") (.lit (.u32 0)))
    (.assign "n" (.usub (.var "n") (.lit (.u32 1))))

/-- Fuel-indexed countdown invariant: `n` holds `v` with
    `v.toNat ≤ k` (memory and layout pinned — `assign` touches
    neither). -/
def countdownInv (m : Mem) (π : Layout) (k : Nat) :
    Env × Mem × Layout → Prop :=
  fun st => ∃ ρ rest v, st = (ρ, m, π) ∧
    ρ = ("n", .u32 v) :: rest ∧ v.toNat ≤ k

/-- Countdown post: exited with `n = 0`. -/
def countdownPost (m : Mem) (π : Layout) :
    Env × Mem × Layout → Outcome → Prop :=
  fun st o => o = .fellThrough ∧ ∃ ρ', st = (ρ', m, π) ∧
    envLookup ρ' "n" = some (.u32 0)

/-- Countdown triple via `htriple_while_at`: the fuel index is
    the bound (`n ≤ F` at fuel `F`), each iteration consumes one
    level with an exact `u32` decrement. -/
theorem hoare_countdown (m : Mem) (π : Layout) :
    ∀ F, HTripleAt F (countdownInv m π F) countdownBody
      (countdownPost m π) := by
  have hguardv : ∀ (ρ : Env) (v : BitVec 32),
      envLookup ρ "n" = some (.u32 v) →
      memEvalExpr (.une (.var "n") (.lit (.u32 0))) ρ m π
        = .ok (.b (v != 0)) := by
    intro ρ v hl
    rw [memEvalExpr_une_agree _ _ ρ m π
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _),
      heval_une_u32 _ _ ρ v 0 (evalExpr_var_hit _ _ _ hl) rfl]
  have hsub : ∀ (v : BitVec 32), 1 ≤ v.toNat →
      (v - 1).toNat = v.toNat - 1 := by
    intro v hle
    rw [BitVec.toNat_sub]
    have hx : v.toNat < 2 ^ 32 := v.isLt
    have h1 : (1 : BitVec 32).toNat < 2 ^ 32 := (1 : BitVec 32).isLt
    have h1v : (1 : BitVec 32).toNat = 1 := rfl
    omega
  have hzero : ∀ (ρ' : Env) (m' : Mem) (π' : Layout),
      countdownInv m π 0 (ρ', m', π') →
      memEvalExpr (.une (.var "n") (.lit (.u32 0))) ρ' m' π'
        = .ok (.b false) := by
    intro ρ' m' π' hI
    simp only [countdownInv] at hI
    obtain ⟨ρ'', rest, v, heq, hρ, hle⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hv0 : v = 0 :=
      BitVec.toNat_inj.mp (by simpa using Nat.le_zero.mp hle)
    have hl : envLookup ρ' "n" = some (.u32 v) := by
      rw [hρ]; simp [envLookup]
    rw [hguardv _ _ hl, hv0]
    simp
  have hexit : ∀ (k : Nat) (ρ' : Env) (m' : Mem) (π' : Layout),
      countdownInv m π k (ρ', m', π') →
      memEvalExpr (.une (.var "n") (.lit (.u32 0))) ρ' m' π'
        = .ok (.b false) →
      countdownPost m π (ρ', m', π') .fellThrough := by
    intro k ρ' m' π' hI hgf
    simp only [countdownInv] at hI
    obtain ⟨ρ'', rest, v, heq, hρ, hle⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hl : envLookup ρ' "n" = some (.u32 v) := by
      rw [hρ]; simp [envLookup]
    by_cases hv0 : v = 0
    · subst hv0
      exact ⟨rfl, ρ', rfl, hl⟩
    · have htrue : (v != 0) = true := by simp; exact hv0
      rw [hguardv _ _ hl, htrue] at hgf
      simp at hgf
  have hdec : ∀ (k : Nat) (ρ' : Env) (m' : Mem) (π' : Layout),
      countdownInv m π (k + 1) (ρ', m', π') →
      memEvalExpr (.une (.var "n") (.lit (.u32 0))) ρ' m' π'
        = .ok (.b false) ∨
      memEvalExpr (.une (.var "n") (.lit (.u32 0))) ρ' m' π'
        = .ok (.b true) := by
    intro k ρ' m' π' hI
    simp only [countdownInv] at hI
    obtain ⟨ρ'', rest, v, heq, hρ, hle⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hl : envLookup ρ' "n" = some (.u32 v) := by
      rw [hρ]; simp [envLookup]
    by_cases hv0 : v = 0
    · left; rw [hguardv _ _ hl, hv0]; simp
    · right; rw [hguardv _ _ hl]; simp; exact hv0
  have hstep : ∀ (k : Nat) (ρ' : Env) (m' : Mem) (π' : Layout),
      countdownInv m π (k + 1) (ρ', m', π') →
      memEvalExpr (.une (.var "n") (.lit (.u32 0))) ρ' m' π'
        = .ok (.b true) →
      ∃ Pmid Qmid, HTriple Pmid
        (.assign "n" (.usub (.var "n") (.lit (.u32 1)))) Qmid ∧
        Pmid (ρ', m', π') ∧
        (∀ ρ₁ m₁ π₁ o, Qmid (ρ₁, m₁, π₁) o →
          (o = .fellThrough ∨ o = .continued) ∧
          countdownInv m π k (ρ₁, m₁, π₁)) := by
    intro k ρ' m' π' hI hgt
    simp only [countdownInv] at hI
    obtain ⟨ρ'', rest, v, heq, hρ, hle⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hl : envLookup ρ' "n" = some (.u32 v) := by
      rw [hρ]; simp [envLookup]
    by_cases hv0 : v = 0
    · subst hv0
      have hb0 : ((0 : BitVec 32) != 0) = false := by simp
      rw [hguardv ρ' 0 hl, hb0] at hgt
      simp at hgt
    · have hne1 : 1 ≤ v.toNat := by
        match ht : v.toNat with
        | 0 =>
          have hv0' : v = 0 :=
            BitVec.toNat_inj.mp (by simpa using ht)
          exact absurd hv0' hv0
        | Nat.succ _ => omega
      have hagree :
          memEvalExpr (.usub (.var "n") (.lit (.u32 1))) ρ' m' π'
            = evalExpr (.usub (.var "n") (.lit (.u32 1))) ρ' :=
        memEvalExpr_usub_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
      have hval :
          evalExpr (.usub (.var "n") (.lit (.u32 1))) ρ'
            = .ok (.u32 (v - 1)) :=
        heval_usub_u32 _ _ _ v 1 (evalExpr_var_hit _ _ _ hl) rfl
      have hu : envUpdate ρ' "n" (.u32 (v - 1))
          = some ((("n", .u32 (v - 1)) :: rest)) := by
        rw [hρ]; exact envUpdate_hit _ _ _ _
      have hbody : HTriple (fun st => st = (ρ', m', π'))
          (.assign "n" (.usub (.var "n") (.lit (.u32 1))))
          (fun st o => o = .fellThrough ∧ ∃ rest' w,
            st = ((("n", .u32 w) :: rest'), m', π') ∧
            w.toNat ≤ k) := by
        intro F ρ₀ m₀ π₀ hP
        simp only [Prod.mk.injEq] at hP
        obtain ⟨rfl, rfl, rfl⟩ := hP
        have hfr := htriple_assign "n"
          (.usub (.var "n") (.lit (.u32 1)))
          ρ₀ m₀ π₀ (.u32 (v - 1)) ((("n", .u32 (v - 1)) :: rest))
          hagree hval hu
        obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := hfr F ρ₀ m₀ π₀ rfl
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hQ₂
        exact ⟨_, _, _, _, hev₂, rfl, rest, (v - 1), rfl,
          by rw [hsub v hne1]; omega⟩
      refine ⟨_, _, hbody, rfl, fun ρ₁ m₁ π₁ o hQ => ?_⟩
      obtain ⟨rfl, rest', w, heq1, hle1⟩ := hQ
      simp only [countdownInv]
      exact ⟨Or.inl trivial, (("n", .u32 w) :: rest'), rest', w,
        heq1, rfl, hle1⟩
  exact htriple_while_at (countdownInv m π) _ _ _ hzero hexit hdec hstep

/-- `cond_pair` under `c = true` over the real emitted body:
    `tif` takes the incrementing branch (both overflow debts
    live), two lets thread the environment, `return_` delivers
    the pair. Exercises the new `htriple_let`. -/
theorem hoare_condPair_true (ρ : Env) (m : Mem) (π : Layout)
    (p q a b : BitVec 32)
    (hp : envLookup ρ "p" = some (.i32 p))
    (hq : envLookup ρ "q" = some (.i32 q))
    (hc : envLookup ρ "c" = some (.b true))
    (h1 : checkedAddI32 p 1 = .ok a)
    (h2 : checkedAddI32 q 2 = .ok b) :
    HTriple (fun st => st = (ρ, m, π))
      condPairFunc.body
      (fun st o => st = (((("b", .i32 b) :: ("a", .i32 a) :: ρ), m, π)) ∧
        o = .returned (.structVal "IPair" [("a", a), ("b", b)])) := by
  have hvc : evalExpr (.var "c") ρ = .ok (.b true) :=
    evalExpr_var_hit _ _ _ hc
  have hadd_agree :
      memEvalExpr (.add (.var "p") (.lit (.i32 1))) ρ m π =
        evalExpr (.add (.var "p") (.lit (.i32 1))) ρ :=
    memEvalExpr_add_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have htif_agree :
      memEvalExpr (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")) ρ m π =
      evalExpr (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")) ρ :=
    memEvalExpr_tif_true _ _ _ _ _ _
      (memEvalExpr_var _ _ _ _) hvc hadd_agree
  have htif_val :
      evalExpr (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")) ρ
        = .ok (.i32 a) := by
    rw [evalExpr_tif_true _ _ _ _ hvc,
      evalExpr_add_var_lit _ _ _ _ hp, h1]
    rfl
  have hletA : HTriple (fun st => st = (ρ, m, π))
      (.let_ "a" (.i 32) (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")))
      (fun st o => st = ((("a", .i32 a) :: ρ, m, π)) ∧
        o = .fellThrough) :=
    htriple_let "a" (.i 32) _ ρ m π (.i32 a)
      (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ h => by cases h) htif_agree htif_val
  have hseqA : HTriple (fun st => st = (ρ, m, π))
      (.let_ "a" (.i 32) (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")))
      (fun st o => o = .fellThrough ∧
        st = ((("a", .i32 a) :: ρ, m, π))) :=
    htriple_consequence _ _ _ _ _ (fun _ => id) hletA
      (fun st o h => ⟨h.2, h.1⟩)
  have htail : HTriple
      (fun st => st = ((("a", .i32 a) :: ρ, m, π)))
      (.seq (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
            (.return_ (.pair (.var "a") (.var "b"))))
      (fun st o => st = (((("b", .i32 b) :: ("a", .i32 a) :: ρ), m, π)) ∧
        o = .returned (.structVal "IPair" [("a", a), ("b", b)])) := by
    have hq1 : envLookup (("a", .i32 a) :: ρ) "q" = some (.i32 q) := by
      simp [envLookup, hq]
    have hadd_agree1 :
        memEvalExpr (.add (.var "q") (.lit (.i32 2)))
          ((("a", .i32 a) :: ρ)) m π =
        evalExpr (.add (.var "q") (.lit (.i32 2)))
          ((("a", .i32 a) :: ρ)) :=
      memEvalExpr_add_agree _ _ _ _ _
        (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
    have hadd_val1 :
        evalExpr (.add (.var "q") (.lit (.i32 2)))
          ((("a", .i32 a) :: ρ)) = .ok (.i32 b) := by
      rw [evalExpr_add_var_lit _ _ _ _ hq1, h2]
      rfl
    have hletB : HTriple
        (fun st => st = ((("a", .i32 a) :: ρ, m, π)))
        (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
        (fun st o => st = (((("b", .i32 b) :: ("a", .i32 a) :: ρ), m, π)) ∧
          o = .fellThrough) := by
      intro F ρ₀ m₀ π₀ hP
      simp only [Prod.mk.injEq] at hP
      obtain ⟨rfl, rfl, rfl⟩ := hP
      exact htriple_let "b" (.i 32) _ _ _ _ (.i32 b)
        (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) hadd_agree1 hadd_val1
        F _ _ _ rfl
    have hseqB : HTriple
        (fun st => st = ((("a", .i32 a) :: ρ, m, π)))
        (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
        (fun st o => o = .fellThrough ∧
          st = (((("b", .i32 b) :: ("a", .i32 a) :: ρ), m, π))) :=
      htriple_consequence _ _ _ _ _ (fun _ => id) hletB
        (fun st o h => ⟨h.2, h.1⟩)
    have hret : HTriple
        (fun st => st = (((("b", .i32 b) :: ("a", .i32 a) :: ρ), m, π)))
        (.return_ (.pair (.var "a") (.var "b")))
        (fun st o => st = (((("b", .i32 b) :: ("a", .i32 a) :: ρ), m, π)) ∧
          o = .returned (.structVal "IPair" [("a", a), ("b", b)])) := by
      have hla : envLookup ((("b", .i32 b) :: ("a", .i32 a) :: ρ)) "a" =
          some (.i32 a) := by simp [envLookup]
      have hlb : envLookup ((("b", .i32 b) :: ("a", .i32 a) :: ρ)) "b" =
          some (.i32 b) := by simp [envLookup]
      have hagree :
          memEvalExpr (.pair (.var "a") (.var "b"))
            ((("b", .i32 b) :: ("a", .i32 a) :: ρ)) m π =
          evalExpr (.pair (.var "a") (.var "b"))
            ((("b", .i32 b) :: ("a", .i32 a) :: ρ)) :=
        memEvalExpr_pair_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hval :
          evalExpr (.pair (.var "a") (.var "b"))
            ((("b", .i32 b) :: ("a", .i32 a) :: ρ)) =
          .ok (.structVal "IPair" [("a", a), ("b", b)]) := by
        simp [evalExpr, hla, hlb]
      intro F ρ₀ m₀ π₀ hP
      simp only [Prod.mk.injEq] at hP
      obtain ⟨rfl, rfl, rfl⟩ := hP
      exact htriple_return _ _ _ _ _ hagree hval F _ _ _ rfl
    exact htriple_seq _ _ _ _ _ hseqB hret
  exact htriple_seq _ _ _ _ _ hseqA htail

/-- `cond_pair` under `c = false`: `tif` takes the passthrough
    branch, so the first add is never evaluated — no `p`
    overflow debt (masking made explicit). Only the `q` debt
    is owed. -/
theorem hoare_condPair_false (ρ : Env) (m : Mem) (π : Layout)
    (p q b : BitVec 32)
    (hp : envLookup ρ "p" = some (.i32 p))
    (hq : envLookup ρ "q" = some (.i32 q))
    (hc : envLookup ρ "c" = some (.b false))
    (h2 : checkedAddI32 q 2 = .ok b) :
    HTriple (fun st => st = (ρ, m, π))
      condPairFunc.body
      (fun st o => st = (((("b", .i32 b) :: ("a", .i32 p) :: ρ), m, π)) ∧
        o = .returned (.structVal "IPair" [("a", p), ("b", b)])) := by
  have hvc : evalExpr (.var "c") ρ = .ok (.b false) :=
    evalExpr_var_hit _ _ _ hc
  have htif_agree :
      memEvalExpr (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")) ρ m π =
      evalExpr (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")) ρ :=
    memEvalExpr_tif_false _ _ _ _ _ _
      (memEvalExpr_var _ _ _ _) hvc
      (memEvalExpr_var _ _ _ _)
  have htif_val :
      evalExpr (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")) ρ
        = .ok (.i32 p) := by
    rw [evalExpr_tif_false _ _ _ _ hvc,
      evalExpr_var_hit _ _ _ hp]
  have hletA : HTriple (fun st => st = (ρ, m, π))
      (.let_ "a" (.i 32) (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")))
      (fun st o => st = ((("a", .i32 p) :: ρ, m, π)) ∧
        o = .fellThrough) :=
    htriple_let "a" (.i 32) _ ρ m π (.i32 p)
      (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ h => by cases h) htif_agree htif_val
  have hseqA : HTriple (fun st => st = (ρ, m, π))
      (.let_ "a" (.i 32) (.tif (.var "c")
        (.add (.var "p") (.lit (.i32 1))) (.var "p")))
      (fun st o => o = .fellThrough ∧
        st = ((("a", .i32 p) :: ρ, m, π))) :=
    htriple_consequence _ _ _ _ _ (fun _ => id) hletA
      (fun st o h => ⟨h.2, h.1⟩)
  have htail : HTriple
      (fun st => st = ((("a", .i32 p) :: ρ, m, π)))
      (.seq (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
            (.return_ (.pair (.var "a") (.var "b"))))
      (fun st o => st = (((("b", .i32 b) :: ("a", .i32 p) :: ρ), m, π)) ∧
        o = .returned (.structVal "IPair" [("a", p), ("b", b)])) := by
    have hq1 : envLookup (("a", .i32 p) :: ρ) "q" = some (.i32 q) := by
      simp [envLookup, hq]
    have hadd_agree1 :
        memEvalExpr (.add (.var "q") (.lit (.i32 2)))
          ((("a", .i32 p) :: ρ)) m π =
        evalExpr (.add (.var "q") (.lit (.i32 2)))
          ((("a", .i32 p) :: ρ)) :=
      memEvalExpr_add_agree _ _ _ _ _
        (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
    have hadd_val1 :
        evalExpr (.add (.var "q") (.lit (.i32 2)))
          ((("a", .i32 p) :: ρ)) = .ok (.i32 b) := by
      rw [evalExpr_add_var_lit _ _ _ _ hq1, h2]
      rfl
    have hletB : HTriple
        (fun st => st = ((("a", .i32 p) :: ρ, m, π)))
        (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
        (fun st o => st = (((("b", .i32 b) :: ("a", .i32 p) :: ρ), m, π)) ∧
          o = .fellThrough) := by
      intro F ρ₀ m₀ π₀ hP
      simp only [Prod.mk.injEq] at hP
      obtain ⟨rfl, rfl, rfl⟩ := hP
      exact htriple_let "b" (.i 32) _ _ _ _ (.i32 b)
        (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) hadd_agree1 hadd_val1
        F _ _ _ rfl
    have hseqB : HTriple
        (fun st => st = ((("a", .i32 p) :: ρ, m, π)))
        (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
        (fun st o => o = .fellThrough ∧
          st = (((("b", .i32 b) :: ("a", .i32 p) :: ρ), m, π))) :=
      htriple_consequence _ _ _ _ _ (fun _ => id) hletB
        (fun st o h => ⟨h.2, h.1⟩)
    have hret : HTriple
        (fun st => st = (((("b", .i32 b) :: ("a", .i32 p) :: ρ), m, π)))
        (.return_ (.pair (.var "a") (.var "b")))
        (fun st o => st = (((("b", .i32 b) :: ("a", .i32 p) :: ρ), m, π)) ∧
          o = .returned (.structVal "IPair" [("a", p), ("b", b)])) := by
      have hla : envLookup ((("b", .i32 b) :: ("a", .i32 p) :: ρ)) "a" =
          some (.i32 p) := by simp [envLookup]
      have hlb : envLookup ((("b", .i32 b) :: ("a", .i32 p) :: ρ)) "b" =
          some (.i32 b) := by simp [envLookup]
      have hagree :
          memEvalExpr (.pair (.var "a") (.var "b"))
            ((("b", .i32 b) :: ("a", .i32 p) :: ρ)) m π =
          evalExpr (.pair (.var "a") (.var "b"))
            ((("b", .i32 b) :: ("a", .i32 p) :: ρ)) :=
        memEvalExpr_pair_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hval :
          evalExpr (.pair (.var "a") (.var "b"))
            ((("b", .i32 b) :: ("a", .i32 p) :: ρ)) =
          .ok (.structVal "IPair" [("a", p), ("b", b)]) := by
        simp [evalExpr, hla, hlb]
      intro F ρ₀ m₀ π₀ hP
      simp only [Prod.mk.injEq] at hP
      obtain ⟨rfl, rfl, rfl⟩ := hP
      exact htriple_return _ _ _ _ _ hagree hval F _ _ _ rfl
    exact htriple_seq _ _ _ _ _ hseqB hret
  exact htriple_seq _ _ _ _ _ hseqA htail

/-- Sum-loop body: `while (i < len) { acc = acc + arr[i]; i = i + 1 }`.
    The accumulator lives in a `Mem` cell: `assign`/`let_` need a
    value mirror that `mload` lacks, while `mstore` takes
    Mem-side values directly — so checked accumulation goes
    through a singleton cell framed against the array (read-only
    loop; the first array gallery). -/
def sumLoopBody : CStmt :=
  .while_ (.ult (.var "i") (.var "len"))
    (.seq (.mstore "acc" (.lit (.u64 0))
              (.add (.mload "acc" (.lit (.u64 0)))
                (.mload "arr" (.var "i"))))
          (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))

/-- In-place increment body: `while (i < len) { arr[i] = arr[i] + 1;
    i = i + 1 }`. Single array block, no side cell — the second
    array gallery, with the contents evolving under the loop. -/
def incrLoopBody : CStmt :=
  .while_ (.ult (.var "i") (.var "len"))
    (.seq (.mstore "arr" (.var "i")
              (.add (.mload "arr" (.var "i")) (.lit (.i32 1))))
          (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))

/-- Closed-instance runtime checks — executable shadows of the
    gallery triples at one point each (the proofs themselves are
    compile-gated): the two-cell incr, `alias_cond` under both
    guard values over the real emitted body, the countdown
    from 3, the read-only sum loop over `[1,2,3,4]`, and the
    in-place increment over `[1,2,3]`. -/
def main : IO Unit := do
  let mut passed := 0
  -- Two-cell incr: `pa=10, pb=20` → `pa=11, pb=21`.
  let (m0, a) := memAllocData emptyMem [10]
  let (m1, b) := memAllocData m0 [20]
  let π : Layout := [("pa", a, a), ("pb", b, b)]
  match memEvalStmtFuel 20 galleryBody [] m1 π with
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: incr instance failed: {(repr e).pretty}")
  | .ok ((_, m', _), .fellThrough) =>
    match memFind m' a, memFind m' b with
    | some ba, some bb =>
      if ba.data != [11] || bb.data != [21] then
        throw (IO.userError
          s!"hoare-gallery: cells={ba.data},{bb.data}, want ([11],[21])")
      else passed := passed + 1
    | _, _ =>
      throw (IO.userError "hoare-gallery: cells missing after run")
  | .ok _ =>
    throw (IO.userError "hoare-gallery: want fellThrough")
  -- `alias_cond` over the emitted body: `(10, 20)` → `(11, 22)`
  -- under `c`, `(10, 22)` without.
  let (n0, p) := memAllocData emptyMem [10]
  let (n1, q) := memAllocData n0 [20]
  let πac : Layout := [("p", p, p), ("q", q, q)]
  for (c, wantP, wantQ) in [(true, 11, 22), (false, 10, 22)] do
    let ρ : Env := [("c", .b c)]
    match memEvalStmtFuel 20 aliasCondFunc.body ρ n1 πac with
    | .ok ((_, m', _), .returned (.u32 0)) =>
      match memFind m' p, memFind m' q with
      | some bp, some bq =>
        if bp.data != [wantP] || bq.data != [wantQ] then
          throw (IO.userError
            s!"hoare-gallery: alias_cond c={c}: cells={bp.data},{bq.data}")
        else passed := passed + 1
      | _, _ =>
        throw (IO.userError
          s!"hoare-gallery: alias_cond c={c}: cells missing")
    | .ok _ =>
      throw (IO.userError
        s!"hoare-gallery: alias_cond c={c}: want returned u32 0")
    | .error e =>
      throw (IO.userError
        s!"hoare-gallery: alias_cond c={c} failed: {(repr e).pretty}")
  -- `cond_pair` over the emitted body is pure-env: `(10, 20)`
  -- answers `(11, 22)` under `c`, `(10, 22)` without (masking).
  for (c, wantA, wantB) in [(true, 11, 22), (false, 10, 22)] do
    let ρcp : Env := [("p", .i32 10), ("q", .i32 20), ("c", .b c)]
    match memEvalStmtFuel 20 condPairFunc.body ρcp emptyMem [] with
    | .ok (_, .returned (.structVal "IPair" [("a", a), ("b", b)])) =>
      if a != wantA || b != wantB then
        throw (IO.userError
          s!"hoare-gallery: cond_pair c={c}: got ({a}, {b})")
      else passed := passed + 1
    | .ok _ =>
      throw (IO.userError
        s!"hoare-gallery: cond_pair c={c}: want returned pair")
    | .error e =>
      throw (IO.userError
        s!"hoare-gallery: cond_pair c={c} failed: {(repr e).pretty}")
  -- Countdown from 3 ends at 0.
  match memEvalStmtFuel 20 countdownBody [("n", .u32 3)] emptyMem [] with
  | .ok ((ρ', _, _), .fellThrough) =>
    match envLookup ρ' "n" with
    | some (.u32 v) =>
      if v != 0 then
        throw (IO.userError "hoare-gallery: countdown did not reach 0")
      else passed := passed + 1
    | _ =>
      throw (IO.userError "hoare-gallery: countdown lost its counter")
  | .ok _ =>
    throw (IO.userError "hoare-gallery: countdown want fellThrough")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: countdown failed: {(repr e).pretty}")
  -- Read-only sum loop over `[1,2,3,4]` totals 10 in `acc`.
  let (s0, aa) := memAllocData emptyMem [(1 : BitVec 32), 2, 3, 4]
  let (s1, ac) := memAllocData s0 [0]
  let πsum : Layout := [("arr", aa, aa), ("acc", ac, ac)]
  let ρsum : Env := [("i", .u64 0), ("len", .u64 4)]
  match memEvalStmtFuel 40 sumLoopBody ρsum s1 πsum with
  | .ok ((_, m', _), .fellThrough) =>
    match memFind m' ac with
    | some b =>
      if b.data != [10] then
        throw (IO.userError
          s!"hoare-gallery: sum loop total={b.data}, want [10]")
      else passed := passed + 1
    | _ =>
      throw (IO.userError "hoare-gallery: sum loop lost accumulator")
  | .ok _ =>
    throw (IO.userError "hoare-gallery: sum loop want fellThrough")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: sum loop failed: {(repr e).pretty}")
  -- In-place increment over `[1,2,3]` gives `[2,3,4]`.
  let (t0, ab) := memAllocData emptyMem [(1 : BitVec 32), 2, 3]
  let πincr : Layout := [("arr", ab, ab)]
  let ρincr : Env := [("i", .u64 0), ("len", .u64 3)]
  match memEvalStmtFuel 40 incrLoopBody ρincr t0 πincr with
  | .ok ((_, m', _), .fellThrough) =>
    match memFind m' ab with
    | some b =>
      if b.data != [2, 3, 4] then
        throw (IO.userError
          s!"hoare-gallery: incr loop cells={b.data}, want [2,3,4]")
      else passed := passed + 1
    | _ =>
      throw (IO.userError "hoare-gallery: incr loop lost array")
  | .ok _ =>
    throw (IO.userError "hoare-gallery: incr loop want fellThrough")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: incr loop failed: {(repr e).pretty}")
  IO.println s!"HOAREGALLERY-OK passed={passed}"

/-- Fuel-indexed sum invariant: index `iv` with checked prefix
    sum, `len - iv` iterations of fuel left, both cells pinned.
    Memory and its layout float existentially (`mc`, `πc = π`):
    the accumulator store evolves `mc` every iteration, so the
    invariant cannot pin entry memory. -/
def sumLoopInv (π : Layout) (aa : Addr) (ta : Nat)
    (ac : Addr) (tc : Nat) (l : List (BitVec 32)) (k : Nat) :
    Env × Mem × Layout → Prop :=
  fun st => ∃ ρ rest iv accv mc πc, st = (ρ, mc, πc) ∧ πc = π ∧
    ρ = ("i", .u64 iv) :: ("len", .u64 (BitVec.ofNat 64 l.length)) :: rest ∧
    iv.toNat ≤ l.length ∧
    accv = (l.take iv.toNat).sum ∧
    l.length - iv.toNat ≤ k ∧
    cellsAt mc aa ta l ∧
    cellsAt mc ac tc [accv]

/-- Sum-loop post: index at length, accumulator holds the total
    (memory floats existentially, as in the invariant). -/
def sumLoopPost (π : Layout) (aa : Addr) (ta : Nat)
    (ac : Addr) (tc : Nat) (l : List (BitVec 32)) :
    Env × Mem × Layout → Outcome → Prop :=
  fun st o => o = .fellThrough ∧ ∃ ρ' mc πc, st = (ρ', mc, πc) ∧ πc = π ∧
    envLookup ρ' "i" = some (.u64 (BitVec.ofNat 64 l.length)) ∧
    cellsAt mc ac tc [l.sum] ∧
    cellsAt mc aa ta l

/-- Sum-loop triple: per-prefix overflow freedom is explicit
    caller debt (`hdebt`), lengths fit `u64` (`hn`). -/
theorem hoare_sumLoop (π : Layout) (aa : Addr) (ta : Nat)
    (ac : Addr) (tc : Nat) (l : List (BitVec 32))
    (hlaArr : layoutLookup π "arr" = some (aa, ta))
    (hlaAcc : layoutLookup π "acc" = some (ac, tc))
    (hne : aa ≠ ac)
    (hn : l.length < 2 ^ 64)
    (hdebt : ∀ j (x : BitVec 32), l[j]? = some x →
      checkedAddI32 ((l.take j).sum) x = .ok ((l.take (j + 1)).sum)) :
    ∀ F, HTripleAt F (sumLoopInv π aa ta ac tc l F) sumLoopBody
      (sumLoopPost π aa ta ac tc l) := by
  have hlenv : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hguardv : ∀ (ρ : Env) (m' : Mem) (π' : Layout) (iv : BitVec 64),
      envLookup ρ "i" = some (.u64 iv) →
      envLookup ρ "len" = some (.u64 (BitVec.ofNat 64 l.length)) →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ m' π'
        = .ok (.b (iv.ult (BitVec.ofNat 64 l.length))) := by
    intro ρ m' π' iv hi hl
    rw [memEvalExpr_ult_agree _ _ ρ m' π'
      (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _),
      evalExpr_ult_u64 _ _ ρ iv _ (evalExpr_var_hit _ _ _ hi)
        (evalExpr_var_hit _ _ _ hl)]
  have hultT : ∀ (iv : BitVec 64), iv.toNat < l.length →
      iv.ult (BitVec.ofNat 64 l.length) = true := by
    intro iv hlt
    rw [BitVec.ult_eq_decide, hlenv]
    exact decide_eq_true hlt
  have hultF : ∀ (iv : BitVec 64), l.length ≤ iv.toNat →
      iv.ult (BitVec.ofNat 64 l.length) = false := by
    intro iv hle
    rw [BitVec.ult_eq_decide, hlenv]
    exact decide_eq_false (Nat.not_lt.mpr hle)
  have hincr : ∀ (iv : BitVec 64), iv.toNat < l.length →
      (iv + 1).toNat = iv.toNat + 1 := by
    intro iv hlt
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  have hexitQ : ∀ (πq : Layout) (ρs : Env) (ms : Mem) (πs : Layout)
      (iv : BitVec 64) (accv : BitVec 32) (rest : Env),
      πs = πq →
      ρs = ("i", .u64 iv) ::
        ("len", .u64 (BitVec.ofNat 64 l.length)) :: rest →
      iv.toNat = l.length → accv = l.sum →
      cellsAt ms aa ta l → cellsAt ms ac tc [accv] →
      sumLoopPost πq aa ta ac tc l (ρs, ms, πs) .fellThrough := by
    intro πq ρs ms πs iv accv rest hπ hρ heqn htotal harr haccC
    subst htotal
    have hiv : iv = BitVec.ofNat 64 l.length :=
      BitVec.toNat_inj.mp (by rw [hlenv]; exact heqn)
    subst hiv
    exact ⟨rfl, ρs, ms, πs, rfl, hπ, by rw [hρ]; simp [envLookup], haccC, harr⟩
  have hzero : ∀ (ρ' : Env) (m' : Mem) (π' : Layout),
      sumLoopInv π aa ta ac tc l 0 (ρ', m', π') →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b false) := by
    intro ρ' m' π' hI
    simp only [sumLoopInv] at hI
    obtain ⟨ρ'', rest, iv, accv, mc, πc, heq, _hπc, hρ, hle, hacc, hk, harr,
      haccC⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hi : envLookup ρ' "i" = some (.u64 iv) := by
      rw [hρ]; simp [envLookup]
    have hlen : envLookup ρ' "len" =
        some (.u64 (BitVec.ofNat 64 l.length)) := by
      rw [hρ]; simp [envLookup]
    have hle' : l.length ≤ iv.toNat := by omega
    rw [hguardv _ _ _ _ hi hlen, hultF _ hle']
  have hexit : ∀ (k : Nat) (ρ' : Env) (m' : Mem) (π' : Layout),
      sumLoopInv π aa ta ac tc l k (ρ', m', π') →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b false) →
      sumLoopPost π aa ta ac tc l (ρ', m', π') .fellThrough := by
    intro k ρ' m' π' hI hgf
    simp only [sumLoopInv] at hI
    obtain ⟨ρ'', rest, iv, accv, mc, πc, heq, hπc, hρ, hle, hacc, hk, harr,
      haccC⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hi : envLookup ρ' "i" = some (.u64 iv) := by
      rw [hρ]; simp [envLookup]
    have hlen : envLookup ρ' "len" =
        some (.u64 (BitVec.ofNat 64 l.length)) := by
      rw [hρ]; simp [envLookup]
    have hnb : ¬ iv.toNat < l.length := by
      intro hlt
      rw [hguardv _ _ _ _ hi hlen, hultT _ hlt] at hgf
      simp at hgf
    have heqn : iv.toNat = l.length := by omega
    have htotal : accv = l.sum := by
      rw [hacc, heqn, List.take_length]
    exact hexitQ π ρ' m' π' iv accv rest hπc hρ heqn htotal harr haccC
  have hdec : ∀ (k : Nat) (ρ' : Env) (m' : Mem) (π' : Layout),
      sumLoopInv π aa ta ac tc l (k + 1) (ρ', m', π') →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b false) ∨
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b true) := by
    intro k ρ' m' π' hI
    simp only [sumLoopInv] at hI
    obtain ⟨ρ'', rest, iv, accv, mc, πc, heq, _hπc, hρ, hle, hacc, hk, harr,
      haccC⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hi : envLookup ρ' "i" = some (.u64 iv) := by
      rw [hρ]; simp [envLookup]
    have hlen : envLookup ρ' "len" =
        some (.u64 (BitVec.ofNat 64 l.length)) := by
      rw [hρ]; simp [envLookup]
    by_cases hlt : iv.toNat < l.length
    · right; rw [hguardv _ _ _ _ hi hlen, hultT _ hlt]
    · left; rw [hguardv _ _ _ _ hi hlen, hultF _ (Nat.le_of_not_lt hlt)]
  have hstep : ∀ (k : Nat) (ρ' : Env) (m' : Mem) (π' : Layout),
      sumLoopInv π aa ta ac tc l (k + 1) (ρ', m', π') →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b true) →
      ∃ Pmid Qmid, HTriple Pmid
        (.seq (.mstore "acc" (.lit (.u64 0))
                (.add (.mload "acc" (.lit (.u64 0)))
                  (.mload "arr" (.var "i"))))
              (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) Qmid ∧
        Pmid (ρ', m', π') ∧
        (∀ ρ₁ m₁ π₁ o, Qmid (ρ₁, m₁, π₁) o →
          (o = .fellThrough ∨ o = .continued) ∧
          sumLoopInv π aa ta ac tc l k (ρ₁, m₁, π₁)) := by
    intro k ρ' m' π' hI hgt
    simp only [sumLoopInv] at hI
    obtain ⟨ρ'', rest, iv, accv, mc, πc, heq, hπc, hρ, hle, hacc, hk, harr,
      haccC⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hi : envLookup ρ' "i" = some (.u64 iv) := by
      rw [hρ]; simp [envLookup]
    have hlen : envLookup ρ' "len" =
        some (.u64 (BitVec.ofNat 64 l.length)) := by
      rw [hρ]; simp [envLookup]
    have hlaArr' : layoutLookup π' "arr" = some (aa, ta) := by
      rw [hπc]; exact hlaArr
    have hlaAcc' : layoutLookup π' "acc" = some (ac, tc) := by
      rw [hπc]; exact hlaAcc
    by_cases hlt : iv.toNat < l.length
    · have hget : l[iv.toNat]? = some l[iv.toNat] :=
        List.getElem?_eq_getElem hlt
      have hmemArr : memLoad m' aa ta iv.toNat = .ok l[iv.toNat] :=
        memLoad_cellsAt _ _ _ _ _ _ harr hget
      have hmemAcc : memLoad m' ac tc 0 = .ok accv :=
        memLoad_cellsAt _ _ _ _ _ _ haccC
          (List.getElem?_eq_getElem (Nat.zero_lt_succ _))
      have hi_eval : memEvalExpr (.var "i") ρ' m' π' = .ok (.u64 iv) := by
        rw [memEvalExpr_var]; exact evalExpr_var_hit _ _ _ hi
      have hmArr : memEvalExpr (.mload "arr" (.var "i")) ρ' m' π'
          = .ok (.i32 l[iv.toNat]) :=
        hexpr_mload "arr" (.var "i") ρ' m' π' iv _ aa ta hlaArr' hi_eval hmemArr
      have hmAcc : memEvalExpr (.mload "acc" (.lit (.u64 0))) ρ' m' π'
          = .ok (.i32 accv) :=
        hexpr_mload "acc" (.lit (.u64 0)) ρ' m' π' 0 accv ac tc hlaAcc'
          (hoare_lit_eval (.u64 0) _ _ _) hmemAcc
      have hadd : memEvalExpr
          (.add (.mload "acc" (.lit (.u64 0)))
            (.mload "arr" (.var "i"))) ρ' m' π'
          = .ok (.i32 ((l.take (iv.toNat + 1)).sum)) := by
        have h := memEvalExpr_add_ok _ _ ρ' m' π' accv _ hmAcc hmArr
        have hd := hdebt iv.toNat _ hget
        rw [hacc, hd] at h
        exact h
      have hsa : memStore m' ac tc 0 ((l.take (iv.toNat + 1)).sum)
          = .ok ⟨m'.next, (ac, ⟨tc, true,
            [accv].set 0 ((l.take (iv.toNat + 1)).sum)⟩) :: m'.blocks,
            m'.blocks64⟩ :=
        memStore_cellsAt _ _ _ _ _ _ haccC (Nat.zero_lt_succ _)
      have hstore : HTriple (fun st => st = (ρ', m', π'))
          (.mstore "acc" (.lit (.u64 0))
            (.add (.mload "acc" (.lit (.u64 0)))
              (.mload "arr" (.var "i"))))
          (fun st o => o = .fellThrough ∧ ∃ m₁, st = (ρ', m₁, π') ∧
            cellsAt m₁ aa ta l ∧
            cellsAt m₁ ac tc ([accv].set 0 ((l.take (iv.toNat + 1)).sum))) := by
        intro F ρ₀ m₀ π₀ hP
        simp only [Prod.mk.injEq] at hP
        obtain ⟨rfl, rfl, rfl⟩ := hP
        have hev := memEvalStmtFuel_mstore_ok F "acc" (.lit (.u64 0))
          (.add (.mload "acc" (.lit (.u64 0)))
            (.mload "arr" (.var "i")))
          ρ₀ m₀ π₀ 0 _ ac tc _
          (hoare_lit_eval (.u64 0) _ _ _) hadd hlaAcc' hsa
        refine ⟨ρ₀, _, π₀, .fellThrough, hev, rfl, ⟨_, rfl, ?_, ?_⟩⟩
        · unfold cellsAt
          rw [memFind_memStore_other _ _ _ _ _ _ _ hsa hne]
          exact harr
        · exact memFind_cellsAt_store _ _ _ _ _ _ _ haccC
            (Nat.zero_lt_succ _) hsa
      have hassign : HTriple
          (fun st => ∃ m₁, st = (ρ', m₁, π') ∧
            cellsAt m₁ aa ta l ∧
            cellsAt m₁ ac tc ([accv].set 0 ((l.take (iv.toNat + 1)).sum)))
          (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
          (fun st o => (o = .fellThrough ∨ o = .continued) ∧
            sumLoopInv π aa ta ac tc l k st) := by
        intro F ρ₀ m₀ π₀ hP
        obtain ⟨m₁, heq1, hA, hB⟩ := hP
        obtain ⟨rfl, rfl, rfl⟩ := heq1
        have hi' : envLookup ρ' "i" = some (.u64 iv) := by
          rw [hρ]; simp [envLookup]
        have hagree :
            memEvalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' m₀ π'
              = evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' :=
          memEvalExpr_uadd_agree _ _ _ _ _
            (by rw [memEvalExpr_var])
            (by rw [memEvalExpr_lit])
        have hval :
            evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ'
              = .ok (.u64 (iv + 1)) :=
          evalExpr_uadd_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hi') rfl
        have hu : envUpdate ρ' "i" (.u64 (iv + 1))
            = some ((("i", .u64 (iv + 1)) ::
              ("len", .u64 (BitVec.ofNat 64 l.length)) :: rest)) := by
          rw [hρ]; exact envUpdate_hit _ _ _ _
        have hfr := htriple_assign "i"
          (.uadd (.var "i") (.lit (.u64 1)))
          ρ' m₀ π' (.u64 (iv + 1))
          ((("i", .u64 (iv + 1)) ::
            ("len", .u64 (BitVec.ofNat 64 l.length)) :: rest))
          hagree hval hu
        obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := hfr F ρ' m₀ π' rfl
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hQ₂
        refine ⟨_, _, _, _, hev₂, Or.inl rfl, _, _, (iv + 1),
          ((l.take (iv.toNat + 1)).sum), _, _, rfl, hπc, rfl,
          ?_, ?_, ?_, ?_, ?_⟩
        · rw [hincr _ hlt]; omega
        · rw [hincr _ hlt]
        · rw [hincr _ hlt]; omega
        · exact hA
        · simpa using hB
      exact ⟨_, _, htriple_seq _ _ _ _ _ hstore hassign, rfl,
        fun ρ₁ m₁ π₁ o h => h⟩
    · rw [hguardv _ _ _ _ hi hlen, hultF _ (Nat.le_of_not_lt hlt)] at hgt
      simp at hgt
  exact htriple_while_at _ _ _ _ hzero hexit hdec hstep

/-- Fuel-indexed increment invariant: the visited prefix is
    incremented, the suffix untouched, `len - iv` fuel left.
    Memory floats existentially, as in the sum loop. -/
def incrLoopInv (π : Layout) (aa : Addr) (ta : Nat)
    (l : List (BitVec 32)) (k : Nat) :
    Env × Mem × Layout → Prop :=
  fun st => ∃ ρ rest iv mc πc, st = (ρ, mc, πc) ∧ πc = π ∧
    ρ = ("i", .u64 iv) :: ("len", .u64 (BitVec.ofNat 64 l.length)) :: rest ∧
    iv.toNat ≤ l.length ∧
    l.length - iv.toNat ≤ k ∧
    cellsAt mc aa ta ((l.take iv.toNat).map (· + 1) ++ l.drop iv.toNat)

/-- Increment post: every word incremented, index at length. -/
def incrLoopPost (π : Layout) (aa : Addr) (ta : Nat)
    (l : List (BitVec 32)) :
    Env × Mem × Layout → Outcome → Prop :=
  fun st o => o = .fellThrough ∧ ∃ ρ' mc πc, st = (ρ', mc, πc) ∧ πc = π ∧
    envLookup ρ' "i" = some (.u64 (BitVec.ofNat 64 l.length)) ∧
    cellsAt mc aa ta (l.map (· + 1))

/-- In-place increment triple: per-word overflow freedom is
    explicit caller debt (`hdebt`), lengths fit `u64` (`hn`). -/
theorem hoare_incrLoop (π : Layout) (aa : Addr) (ta : Nat)
    (l : List (BitVec 32))
    (hlaArr : layoutLookup π "arr" = some (aa, ta))
    (hn : l.length < 2 ^ 64)
    (hdebt : ∀ (j : Nat) (x : BitVec 32), l[j]? = some x →
      checkedAddI32 x 1 = .ok (x + 1)) :
    ∀ F, HTripleAt F (incrLoopInv π aa ta l F) incrLoopBody
      (incrLoopPost π aa ta l) := by
  have ihlenv : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have ihguardv : ∀ (ρ : Env) (m' : Mem) (π' : Layout) (iv : BitVec 64),
      envLookup ρ "i" = some (.u64 iv) →
      envLookup ρ "len" = some (.u64 (BitVec.ofNat 64 l.length)) →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ m' π'
        = .ok (.b (iv.ult (BitVec.ofNat 64 l.length))) := by
    intro ρ m' π' iv hi hl
    rw [memEvalExpr_ult_agree _ _ ρ m' π'
      (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _),
      evalExpr_ult_u64 _ _ ρ iv _ (evalExpr_var_hit _ _ _ hi)
        (evalExpr_var_hit _ _ _ hl)]
  have ihultT : ∀ (iv : BitVec 64), iv.toNat < l.length →
      iv.ult (BitVec.ofNat 64 l.length) = true := by
    intro iv hlt
    rw [BitVec.ult_eq_decide, ihlenv]
    exact decide_eq_true hlt
  have ihultF : ∀ (iv : BitVec 64), l.length ≤ iv.toNat →
      iv.ult (BitVec.ofNat 64 l.length) = false := by
    intro iv hle
    rw [BitVec.ult_eq_decide, ihlenv]
    exact decide_eq_false (Nat.not_lt.mpr hle)
  have ihincr : ∀ (iv : BitVec 64), iv.toNat < l.length →
      (iv + 1).toNat = iv.toNat + 1 := by
    intro iv hlt
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  have ihexitQ : ∀ (πq : Layout) (ρs : Env) (ms : Mem) (πs : Layout)
      (iv : BitVec 64) (rest : Env),
      πs = πq →
      ρs = ("i", .u64 iv) ::
        ("len", .u64 (BitVec.ofNat 64 l.length)) :: rest →
      iv.toNat = l.length →
      cellsAt ms aa ta ((l.take iv.toNat).map (· + 1) ++ l.drop iv.toNat) →
      incrLoopPost πq aa ta l (ρs, ms, πs) .fellThrough := by
    intro πq ρs ms πs iv rest hπ hρ heqn harr
    have hiv : iv = BitVec.ofNat 64 l.length :=
      BitVec.toNat_inj.mp (by rw [ihlenv]; exact heqn)
    subst hiv
    rw [ihlenv, List.take_length, List.drop_length] at harr
    exact ⟨rfl, ρs, ms, πs, rfl, hπ, by rw [hρ]; simp [envLookup],
      by simpa using harr⟩
  have ihzero : ∀ (ρ' : Env) (m' : Mem) (π' : Layout),
      incrLoopInv π aa ta l 0 (ρ', m', π') →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b false) := by
    intro ρ' m' π' hI
    simp only [incrLoopInv] at hI
    obtain ⟨ρ'', rest, iv, mc, πc, heq, _hπc, hρ, hle, hk, harr⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hi : envLookup ρ' "i" = some (.u64 iv) := by
      rw [hρ]; simp [envLookup]
    have hlen : envLookup ρ' "len" =
        some (.u64 (BitVec.ofNat 64 l.length)) := by
      rw [hρ]; simp [envLookup]
    have hle' : l.length ≤ iv.toNat := by omega
    rw [ihguardv _ _ _ _ hi hlen, ihultF _ hle']
  have ihexit : ∀ (k : Nat) (ρ' : Env) (m' : Mem) (π' : Layout),
      incrLoopInv π aa ta l k (ρ', m', π') →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b false) →
      incrLoopPost π aa ta l (ρ', m', π') .fellThrough := by
    intro k ρ' m' π' hI hgf
    simp only [incrLoopInv] at hI
    obtain ⟨ρ'', rest, iv, mc, πc, heq, hπc, hρ, hle, hk, harr⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hi : envLookup ρ' "i" = some (.u64 iv) := by
      rw [hρ]; simp [envLookup]
    have hlen : envLookup ρ' "len" =
        some (.u64 (BitVec.ofNat 64 l.length)) := by
      rw [hρ]; simp [envLookup]
    have hnb : ¬ iv.toNat < l.length := by
      intro hlt
      rw [ihguardv _ _ _ _ hi hlen, ihultT _ hlt] at hgf
      simp at hgf
    have heqn : iv.toNat = l.length := by omega
    exact ihexitQ π ρ' m' π' iv rest hπc hρ heqn harr
  have ihdec : ∀ (k : Nat) (ρ' : Env) (m' : Mem) (π' : Layout),
      incrLoopInv π aa ta l (k + 1) (ρ', m', π') →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b false) ∨
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b true) := by
    intro k ρ' m' π' hI
    simp only [incrLoopInv] at hI
    obtain ⟨ρ'', rest, iv, mc, πc, heq, _hπc, hρ, hle, hk, harr⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hi : envLookup ρ' "i" = some (.u64 iv) := by
      rw [hρ]; simp [envLookup]
    have hlen : envLookup ρ' "len" =
        some (.u64 (BitVec.ofNat 64 l.length)) := by
      rw [hρ]; simp [envLookup]
    by_cases hlt : iv.toNat < l.length
    · right; rw [ihguardv _ _ _ _ hi hlen, ihultT _ hlt]
    · left; rw [ihguardv _ _ _ _ hi hlen, ihultF _ (Nat.le_of_not_lt hlt)]
  have ihstep : ∀ (k : Nat) (ρ' : Env) (m' : Mem) (π' : Layout),
      incrLoopInv π aa ta l (k + 1) (ρ', m', π') →
      memEvalExpr (.ult (.var "i") (.var "len")) ρ' m' π'
        = .ok (.b true) →
      ∃ Pmid Qmid, HTriple Pmid
        (.seq (.mstore "arr" (.var "i")
                (.add (.mload "arr" (.var "i")) (.lit (.i32 1))))
              (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) Qmid ∧
        Pmid (ρ', m', π') ∧
        (∀ ρ₁ m₁ π₁ o, Qmid (ρ₁, m₁, π₁) o →
          (o = .fellThrough ∨ o = .continued) ∧
          incrLoopInv π aa ta l k (ρ₁, m₁, π₁)) := by
    intro k ρ' m' π' hI hgt
    simp only [incrLoopInv] at hI
    obtain ⟨ρ'', rest, iv, mc, πc, heq, hπc, hρ, hle, hk, harr⟩ := hI
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hi : envLookup ρ' "i" = some (.u64 iv) := by
      rw [hρ]; simp [envLookup]
    have hlen : envLookup ρ' "len" =
        some (.u64 (BitVec.ofNat 64 l.length)) := by
      rw [hρ]; simp [envLookup]
    have hlaArr' : layoutLookup π' "arr" = some (aa, ta) := by
      rw [hπc]; exact hlaArr
    by_cases hlt : iv.toNat < l.length
    · have hget : l[iv.toNat]? = some l[iv.toNat] :=
        List.getElem?_eq_getElem hlt
      have hgetC : (((l.take iv.toNat).map (· + 1) ++
          l.drop iv.toNat)[iv.toNat]? = some l[iv.toNat]) := by
        have hlenA : ((l.take iv.toNat).map (· + 1)).length = iv.toNat := by
          simp only [List.length_map, List.length_take]; omega
        rw [List.getElem?_append_right (by omega), hlenA, Nat.sub_self,
          List.getElem?_drop, Nat.add_zero]
        exact List.getElem?_eq_getElem hlt
      have hmemArr : memLoad m' aa ta iv.toNat = .ok l[iv.toNat] :=
        memLoad_cellsAt _ _ _ _ _ _ harr hgetC
      have hi_eval : memEvalExpr (.var "i") ρ' m' π' = .ok (.u64 iv) := by
        rw [memEvalExpr_var]; exact evalExpr_var_hit _ _ _ hi
      have hmArr : memEvalExpr (.mload "arr" (.var "i")) ρ' m' π'
          = .ok (.i32 l[iv.toNat]) :=
        hexpr_mload "arr" (.var "i") ρ' m' π' iv _ aa ta hlaArr' hi_eval hmemArr
      have hlit1 : memEvalExpr (.lit (.i32 1)) ρ' m' π' = .ok (.i32 1) :=
        hoare_lit_eval (.i32 1) _ _ _
      have hadd : memEvalExpr
          (.add (.mload "arr" (.var "i")) (.lit (.i32 1))) ρ' m' π'
          = .ok (.i32 (l[iv.toNat] + 1)) := by
        have h := memEvalExpr_add_ok _ _ ρ' m' π' _ _ hmArr hlit1
        have hd := hdebt iv.toNat _ hget
        rw [hd] at h
        exact h
      have hlenC : iv.toNat <
          (((l.take iv.toNat).map (· + 1) ++ l.drop iv.toNat).length) := by
        simp only [List.length_append, List.length_map, List.length_take,
          List.length_drop]
        omega
      have hsa : memStore m' aa ta iv.toNat (l[iv.toNat] + 1)
          = .ok ⟨m'.next, (aa, ⟨ta, true,
            ((l.take iv.toNat).map (· + 1) ++ l.drop iv.toNat).set iv.toNat
              (l[iv.toNat] + 1)⟩) :: m'.blocks,
            m'.blocks64⟩ :=
        memStore_cellsAt _ _ _ _ _ _ harr hlenC
      have hstore : HTriple (fun st => st = (ρ', m', π'))
          (.mstore "arr" (.var "i")
            (.add (.mload "arr" (.var "i")) (.lit (.i32 1))))
          (fun st o => o = .fellThrough ∧ ∃ m₁, st = (ρ', m₁, π') ∧
            cellsAt m₁ aa ta (((l.take iv.toNat).map (· + 1) ++
              l.drop iv.toNat).set iv.toNat (l[iv.toNat] + 1))) := by
        intro F ρ₀ m₀ π₀ hP
        simp only [Prod.mk.injEq] at hP
        obtain ⟨rfl, rfl, rfl⟩ := hP
        have hev := memEvalStmtFuel_mstore_ok F "arr" (.var "i")
          (.add (.mload "arr" (.var "i")) (.lit (.i32 1)))
          ρ₀ m₀ π₀ iv _ aa ta _
          hi_eval hadd hlaArr' hsa
        refine ⟨ρ₀, _, π₀, .fellThrough, hev, rfl, ⟨_, rfl, ?_⟩⟩
        exact memFind_cellsAt_store _ _ _ _ _ _ _ harr hlenC hsa
      have hassign : HTriple
          (fun st => ∃ m₁, st = (ρ', m₁, π') ∧
            cellsAt m₁ aa ta (((l.take iv.toNat).map (· + 1) ++
              l.drop iv.toNat).set iv.toNat (l[iv.toNat] + 1)))
          (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
          (fun st o => (o = .fellThrough ∨ o = .continued) ∧
            incrLoopInv π aa ta l k st) := by
        intro F ρ₀ m₀ π₀ hP
        obtain ⟨m₁, heq1, hA⟩ := hP
        obtain ⟨rfl, rfl, rfl⟩ := heq1
        have hi' : envLookup ρ' "i" = some (.u64 iv) := by
          rw [hρ]; simp [envLookup]
        have hagree :
            memEvalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' m₀ π'
              = evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' :=
          memEvalExpr_uadd_agree _ _ _ _ _
            (by rw [memEvalExpr_var])
            (by rw [memEvalExpr_lit])
        have hval :
            evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ'
              = .ok (.u64 (iv + 1)) :=
          evalExpr_uadd_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hi') rfl
        have hu : envUpdate ρ' "i" (.u64 (iv + 1))
            = some ((("i", .u64 (iv + 1)) ::
              ("len", .u64 (BitVec.ofNat 64 l.length)) :: rest)) := by
          rw [hρ]; exact envUpdate_hit _ _ _ _
        have hfr := htriple_assign "i"
          (.uadd (.var "i") (.lit (.u64 1)))
          ρ' m₀ π' (.u64 (iv + 1))
          ((("i", .u64 (iv + 1)) ::
            ("len", .u64 (BitVec.ofNat 64 l.length)) :: rest))
          hagree hval hu
        obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := hfr F ρ' m₀ π' rfl
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hQ₂
        refine ⟨_, _, _, _, hev₂, Or.inl rfl, _, _, (iv + 1), _, _,
          rfl, hπc, rfl, ?_, ?_, ?_⟩
        · rw [ihincr _ hlt]; omega
        · rw [ihincr _ hlt]; omega
        · have hlenA : ((l.take iv.toNat).map (· + 1)).length = iv.toNat := by
            simp only [List.length_map, List.length_take]; omega
          have hdz : ((l.drop iv.toNat).set 0 (l[iv.toNat] + 1)
              = (l[iv.toNat] + 1) :: l.drop (iv.toNat + 1)) := by
            apply List.ext_getElem?
            intro i
            cases i with
            | zero =>
              have hne : l.length - iv.toNat ≠ 0 := by omega
              simp [List.getElem?_set, hne]
            | succ i =>
              simp only [List.getElem?_set, show ¬(0 = i + 1) from by omega,
                ite_false, List.getElem?_cons_succ, List.getElem?_drop]
              congr 1
              omega
          have hbridge : ((((l.take iv.toNat).map (· + 1) ++
              l.drop iv.toNat).set iv.toNat (l[iv.toNat] + 1)) =
              (((l.take (iv.toNat + 1)).map (· + 1) ++
                l.drop (iv.toNat + 1)))) := by
            rw [List.set_append_right _ _ (by omega), hlenA, Nat.sub_self,
              hdz, List.take_add_one, List.map_append, hget,
              Option.toList_some, List.map_cons, List.map_nil,
              List.append_assoc]
            rfl
          rw [ihincr _ hlt, ←hbridge]
          exact hA
      exact ⟨_, _, htriple_seq _ _ _ _ _ hstore hassign, rfl,
        fun ρ₁ m₁ π₁ o h => h⟩
    · rw [ihguardv _ _ _ _ hi hlen, ihultF _ (Nat.le_of_not_lt hlt)] at hgt
      simp at hgt
  exact htriple_while_at _ _ _ _ ihzero ihexit ihdec ihstep

end HoareGallery
