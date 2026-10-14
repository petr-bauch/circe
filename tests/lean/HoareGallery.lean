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

/-- Closed-instance runtime checks — executable shadows of the
    gallery triples at one point each (the proofs themselves are
    compile-gated): the two-cell incr, `alias_cond` under both
    guard values over the real emitted body, and the countdown
    from 3. -/
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
  IO.println s!"HOAREGALLERY-OK passed={passed}"

end HoareGallery
