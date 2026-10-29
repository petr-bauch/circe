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
import Circe.Transfer.VecReverse
import Circe.Transfer.VecSegReverse
import Circe.Transfer.VecRotate
import Circe.Emit.VecListRev
import Circe.Emit.VecHeapSort

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
  -- Reverse swap step over `[1,2,3]`: one body iteration swaps the
  -- window ends (`i=0, j=3` gives `v=[3,2,1]`, `i=1, j=2`).
  let revL : List (BitVec 32) := [1, 2, 3]
  let revM : Mem := ⟨1, [(0, ⟨0, true,
    (BitVec.ofNat 32 3) :: revL⟩)], []⟩
  let revPi : Layout := [("v", 0, 0)]
  let revRho : Env := [("v", .stdVecVal revL),
    ("i", .u64 0), ("j", .u64 3)]
  match memEvalProgStmt vecReverseProg 5 vecReverseBody revRho revM revPi with
  | .ok ((ρ', _, _), .fellThrough) =>
    match envLookup ρ' "v", envLookup ρ' "i", envLookup ρ' "j" with
    | some (.stdVecVal got), some (.u64 gotI), some (.u64 gotJ) =>
      if got != [3, 2, 1] || gotI.toNat != 1 || gotJ.toNat != 2 then
        throw (IO.userError
          s!"hoare-gallery: reverse swap got={got.map (·.toInt)}, want [3,2,1]")
      else passed := passed + 1
    | _, _, _ =>
      throw (IO.userError "hoare-gallery: reverse swap env lost")
  | .ok _ =>
    throw (IO.userError "hoare-gallery: reverse swap want fellThrough")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: reverse swap failed: {(repr e).pretty}")
  -- Whole countdown over `[1,2,3]`: the while-rule loop exits with
  -- `v=[3,2,1]` (executable instance of `hoare_reverseWhileProg`).
  let wrevL : List (BitVec 32) := [1, 2, 3]
  let wrevM : Mem := ⟨1, [(0, ⟨0, true,
    (BitVec.ofNat 32 3) :: wrevL⟩)], []⟩
  let wrevPi : Layout := [("v", 0, 0)]
  let wrevRho : Env := [("v", .stdVecVal wrevL),
    ("i", .u64 0), ("j", .u64 3)]
  match memEvalProgStmt vecReverseProg 20 vecReverseWhile
      wrevRho wrevM wrevPi with
  | .ok ((ρ', _, _), .fellThrough) =>
    match envLookup ρ' "v" with
    | some (.stdVecVal got) =>
      if got != [3, 2, 1] then
        throw (IO.userError
          s!"hoare-gallery: reverse loop got={got.map (·.toInt)}, want [3,2,1]")
      else passed := passed + 1
    | _ =>
      throw (IO.userError "hoare-gallery: reverse loop env lost")
  | .ok _ =>
    throw (IO.userError "hoare-gallery: reverse loop want fellThrough")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: reverse loop failed: {(repr e).pretty}")
  -- Segment window `[1,4)` over `[1,2,3,4,5]` exits with
  -- `v=[1,4,3,2,5]` (executable instance of the `hoare_segSwap`
  -- window shape, entry-level).
  match memEvalProgFunc vecSegReverseProg 30 vecSegReverseFunc
      [.stdVecVal ([1, 2, 3, 4, 5] : List (BitVec 32)),
        .u64 1, .u64 4] with
  | .ok (.stdVecVal got) =>
    if got != [1, 4, 3, 2, 5] then
      throw (IO.userError
        s!"hoare-gallery: seg window got={got.map (·.toInt)}, want [1,4,3,2,5]")
    else passed := passed + 1
  | .ok _ =>
    throw (IO.userError "hoare-gallery: seg window want stdVecVal")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: seg window failed: {(repr e).pretty}")
  -- Left rotation by 1 over `[1,2,3,4]` exits with `v=[2,3,4,1]`.
  -- Prose note on the while-rule boundary: the rotate entry is
  -- loopless triple entry-over-entry composition, so there is no
  -- loop for `htripleProg_while_at` to consume — a Hoare triple
  -- for the entry would need program-level `seq`/`callRet`
  -- composition rules, which do not exist yet (named future work;
  -- the executable instance below pins the behavior instead).
  match memEvalProgFunc vecRotateProg 30 vecRotateFunc
      [.stdVecVal ([1, 2, 3, 4] : List (BitVec 32)), .u64 1] with
  | .ok (.stdVecVal got) =>
    if got != [2, 3, 4, 1] then
      throw (IO.userError
        s!"hoare-gallery: rotate got={got.map (·.toInt)}, want [2,3,4,1]")
    else passed := passed + 1
  | .ok _ =>
    throw (IO.userError "hoare-gallery: rotate want stdVecVal")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: rotate failed: {(repr e).pretty}")
  -- Link-rewire step over `nxt=[1,2,3]` from the seeded entry
  -- state (`prev=n=3`, `cur=head=0`): one `revBody` iteration
  -- rewires `nxt[0]` to the predecessor and advances both
  -- cursors (`prev=0`, `cur=1`, `nxt_cur=1`, `nxt=[3,2,3]`).
  let revData : List (BitVec 32) := [10, 20, 30]
  let revNxt : List (BitVec 32) := [1, 2, 3]
  match evalStmtFuel 10 revBody
      (mkRevEnv revData revNxt 3 0 3 0 0) with
  | .ok (ρ', .fellThrough) =>
    match envLookup ρ' "nxt", envLookup ρ' "prev",
        envLookup ρ' "cur", envLookup ρ' "nxt_cur" with
    | some (.stdVecVal gotNxt), some (.u64 gotP),
      some (.u64 gotC), some (.u64 gotX) =>
      if gotNxt != [3, 2, 3] || gotP.toNat != 0 ||
          gotC.toNat != 1 || gotX.toNat != 1 then
        throw (IO.userError
          s!"hoare-gallery: listrev step got nxt={gotNxt.map (·.toInt)}, want [3,2,3]")
      else passed := passed + 1
    | _, _, _, _ =>
      throw (IO.userError "hoare-gallery: listrev step env lost")
  | .ok _ =>
    throw (IO.userError "hoare-gallery: listrev step want fellThrough")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: listrev step failed: {(repr e).pretty}")
  -- Whole chase over `nxt=[1,2,3]` from `head=0` exits with the
  -- new head 2 and rewired links `[3,0,1]` (the links leg is what
  -- sets reversal apart from a head-only spec).
  -- Prose note on the Hoare boundary: J has no Mem-level
  -- (Transfer) presence, so there is no rewire-step triple for
  -- `htripleProg_while_at` to consume yet — a triple would need
  -- the step at Mem level plus the loop-rule application (named
  -- future work; the executable instances above pin the behavior
  -- instead). Rule-of-three status: the R/S swap-step tactics
  -- are Mem-level, so the Func-level chase step is not a third
  -- use — no tactic harvest.
  match revOuterFwd 40 revNxt 3 3 0 with
  | .ok (gotNxt, gotP, gotC) =>
    if gotNxt != [3, 0, 1] || gotP.toNat != 2 || gotC.toNat != 3 then
      throw (IO.userError
        s!"hoare-gallery: listrev chase got nxt={gotNxt.map (·.toInt)}, want [3,0,1]")
    else passed := passed + 1
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: listrev chase failed: {(repr e).pretty}")
  -- Sift step over `v=[1,3,2]` from `root=0, B=3`: `child=2*0+1=1`,
  -- `other=2` loses the pick (`v[1]=3` is not less than `v[2]=2`),
  -- `aR=1 < aC=3` swaps through `vecSet`, `root=1`; the next
  -- descent reads `child=3`, out of bound, and breaks
  -- (`v=[3,1,2]`, `root=1`).
  -- Prose note on the Hoare boundary: H has no Mem-level
  -- (Transfer) presence — all reads are pure `stdVecAt` (the J
  -- precedent) — so there is no sift-step triple for
  -- `htripleProg_while_at` to consume yet (named future work; the
  -- executable instances below pin the behavior instead).
  match evalStmtFuel 40 heapSift
      (mkHeapEnv ([1, 3, 2] : List (BitVec 32))
        (BitVec.ofNat 64 3) (BitVec.ofNat 64 3)
        (BitVec.ofNat 64 3) (BitVec.ofNat 64 3)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0)) with
  | .ok (ρ', .fellThrough) =>
    match envLookup ρ' "v", envLookup ρ' "root" with
    | some (.stdVecVal gotV), some (.u64 gotR) =>
      if gotV != [3, 1, 2] || gotR.toNat != 1 then
        throw (IO.userError
          s!"hoare-gallery: heap sift got v={gotV.map (·.toInt)} root={gotR.toNat}, want [3,1,2]/1")
      else passed := passed + 1
    | _, _ =>
      throw (IO.userError "hoare-gallery: heap sift env lost")
  | .ok _ =>
    throw (IO.userError "hoare-gallery: heap sift want fellThrough")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: heap sift failed: {(repr e).pretty}")
  -- Whole entry over `[3,1,2]` exits with `v=[1,2,3]`
  -- (executable instance of `heapSort_body_ok`: the heapify drain
  -- builds the heap, the extract drain emits ascending order).
  match evalProgFunc heapSortProg 60 heapSortFunc
      [.stdVecVal ([3, 1, 2] : List (BitVec 32)),
        .u64 (BitVec.ofNat 64 3)] with
  | .ok (.stdVecVal got) =>
    if got != [1, 2, 3] then
      throw (IO.userError
        s!"hoare-gallery: heap entry got={got.map (·.toInt)}, want [1,2,3]")
    else passed := passed + 1
  | .ok _ =>
    throw (IO.userError "hoare-gallery: heap entry want stdVecVal")
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: heap entry failed: {(repr e).pretty}")
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
      BitVec.toNat_inj.mp (by rw [ofNat64_toNat _ hn]; exact heqn)
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
    obtain ⟨hi, hlen⟩ := envLookup_ilen _ _ _ _ hρ
    have hle' : l.length ≤ iv.toNat := by omega
    rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_false _ hn _ hle']
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
    obtain ⟨hi, hlen⟩ := envLookup_ilen _ _ _ _ hρ
    have hnb : ¬ iv.toNat < l.length := by
      intro hlt
      rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_true _ hn _ hlt] at hgf
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
    obtain ⟨hi, hlen⟩ := envLookup_ilen _ _ _ _ hρ
    by_cases hlt : iv.toNat < l.length
    · right; rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_true _ hn _ hlt]
    · left; rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_false _ hn _ (Nat.le_of_not_lt hlt)]
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
    obtain ⟨hi, hlen⟩ := envLookup_ilen _ _ _ _ hρ
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
        obtain ⟨hagree, hval, hu⟩ := hoare_uadd_incr_facts _ _ _ _ _ _ hρ
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
        · rw [u64_succ_toNat _ _ hn hlt]; omega
        · rw [u64_succ_toNat _ _ hn hlt]
        · rw [u64_succ_toNat _ _ hn hlt]; omega
        · exact hA
        · simpa using hB
      exact ⟨_, _, htriple_seq _ _ _ _ _ hstore hassign, rfl,
        fun ρ₁ m₁ π₁ o h => h⟩
    · rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_false _ hn _ (Nat.le_of_not_lt hlt)] at hgt
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
      BitVec.toNat_inj.mp (by rw [ofNat64_toNat _ hn]; exact heqn)
    subst hiv
    rw [ofNat64_toNat _ hn, List.take_length, List.drop_length] at harr
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
    obtain ⟨hi, hlen⟩ := envLookup_ilen _ _ _ _ hρ
    have hle' : l.length ≤ iv.toNat := by omega
    rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_false _ hn _ hle']
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
    obtain ⟨hi, hlen⟩ := envLookup_ilen _ _ _ _ hρ
    have hnb : ¬ iv.toNat < l.length := by
      intro hlt
      rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_true _ hn _ hlt] at hgf
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
    obtain ⟨hi, hlen⟩ := envLookup_ilen _ _ _ _ hρ
    by_cases hlt : iv.toNat < l.length
    · right; rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_true _ hn _ hlt]
    · left; rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_false _ hn _ (Nat.le_of_not_lt hlt)]
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
    obtain ⟨hi, hlen⟩ := envLookup_ilen _ _ _ _ hρ
    have hlaArr' : layoutLookup π' "arr" = some (aa, ta) := by
      rw [hπc]; exact hlaArr
    by_cases hlt : iv.toNat < l.length
    · have hget : l[iv.toNat]? = some l[iv.toNat] :=
        List.getElem?_eq_getElem hlt
      have hgetC : (((l.take iv.toNat).map (· + 1) ++
          l.drop iv.toNat)[iv.toNat]? = some l[iv.toNat]) :=
        take_map_drop_getElem l iv.toNat hlt
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
        obtain ⟨hagree, hval, hu⟩ := hoare_uadd_incr_facts _ _ _ _ _ _ hρ
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
        · rw [u64_succ_toNat _ _ hn hlt]; omega
        · rw [u64_succ_toNat _ _ hn hlt]; omega
        · rw [u64_succ_toNat _ _ hn hlt,
            ←take_map_drop_set_succ l iv.toNat hlt]
          exact hA
      exact ⟨_, _, htriple_seq _ _ _ _ _ hstore hassign, rfl,
        fun ρ₁ m₁ π₁ o h => h⟩
    · rw [memEvalExpr_ult_ilen _ _ _ _ _ hi hlen, ult_ofNat64_false _ hn _ (Nat.le_of_not_lt hlt)] at hgt
      simp at hgt
  exact htriple_while_at _ _ _ _ ihzero ihexit ihdec ihstep

/-- Reverse swap-step triple: one `vecReverseBody` iteration swaps
    the window ends and advances the indices (thin triple sugar
    over `memBody_hit`; the `hstep`-shaped premise a
    program-level while-rule will consume). -/
theorem hoare_reverseSwap (F : Nat)
    (orig l : List (BitVec 32)) (n i j : Nat)
    (iB jB : BitVec 64) (a b : BitVec 32)
    (hinv : RevInv orig l n i j)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (hlt : i < j)
    (ha : l[i]? = some a) (hb : l[j - 1]? = some b)
    (hn64 : n < 2 ^ 64) :
    HTripleProgAt vecReverseProg F
      (fun st => ∃ ρ m π, st = (ρ, m, π) ∧
        envLookup ρ "v" = some (.stdVecVal l) ∧
        envLookup ρ "i" = some (.u64 iB) ∧
        envLookup ρ "j" = some (.u64 jB) ∧
        layoutLookup π "v" = some (0, 0) ∧
        memFind m 0 = some ⟨0, true, (BitVec.ofNat 32 n) :: l⟩)
      vecReverseBody
      (fun st o => o = .fellThrough ∧
        ∃ ρ' m' π', st = (ρ', m', π') ∧
        envLookup ρ' "v" =
          some (.stdVecVal ((l.set i b).set (j - 1) a)) ∧
        envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
        envLookup ρ' "j" = some (.u64 (jB - 1)) ∧
        layoutLookup π' "v" = some (0, 0) ∧
        memFind m' 0 = some ⟨0, true, (BitVec.ofNat 32 n) ::
          ((l.set i b).set (j - 1) a)⟩ ∧
        RevInv orig ((l.set i b).set (j - 1) a) n (i + 1)
          (j - 1)) := by
  intro ρ₀ m₀ π₀ hP
  obtain ⟨ρ₁, m₁, π₁, heq, hv, hi, hj, hlay, hmem⟩ := hP
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  obtain ⟨ρ', m', heval, hv', hi', hj', hmem', hinv'⟩ :=
    memBody_hit F ρ₀ m₀ π₀ orig l n i j iB jB a b
      hinv hiN hjN hlt ha hb hn64 hv hi hj hlay hmem
  exact ⟨ρ', m', π₀, .fellThrough, heval, rfl,
    ρ', m', π₀, rfl, hv', hi', hj', hlay, hmem', hinv'⟩

/-- `ult` guard evaluation for the `i`/`j` countdown environment
    (first use, prose-note stage: the same `ult_agree` + `var` +
    `ult_u64` cascade as `memEvalExpr_ult_ilen`, generalized from
    the `i`/`len` pair to two index variables). -/
theorem memEvalExpr_ult_ij (ρ : Env) (m : Mem) (π : Layout)
    (iB jB : BitVec 64)
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB)) :
    memEvalExpr (.ult (.var "i") (.var "j")) ρ m π
      = .ok (.b (iB.ult jB)) := by
  rw [memEvalExpr_ult_agree _ _ ρ m π
    (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _),
    evalExpr_ult_u64 _ _ ρ iB _ (evalExpr_var_hit _ _ _ hi)
      (evalExpr_var_hit _ _ _ hj)]

/-- Fuel-indexed countdown invariant: `revIters i j = k` iterations
    remain, with the `RevInv` words, index bindings, snapshot, and
    layout (the shape `htripleProg_while_at` counts down). -/
abbrev revInvK (orig : List (BitVec 32)) (n k : Nat) :
    Env × Mem × Layout → Prop :=
  fun st => ∃ ρ m π l i j iB jB, st = (ρ, m, π) ∧
    revIters i j = k ∧
    envLookup ρ "v" = some (.stdVecVal l) ∧
    envLookup ρ "i" = some (.u64 iB) ∧ iB.toNat = i ∧
    envLookup ρ "j" = some (.u64 jB) ∧ jB.toNat = j ∧
    layoutLookup π "v" = some (0, 0) ∧
    memFind m 0 = some ⟨0, true, (BitVec.ofNat 32 n) :: l⟩ ∧
    RevInv orig l n i j

/-- Whole countdown as a rule application: the R loop triple via
    `htripleProg_while_at` (first use — the hand-rolled fuel
    induction in `revWhile_ok` becomes the rule's induction; each
    premise below names the R lemma that used to be an inline
    proof step). -/
theorem hoare_reverseWhileProg (F : Nat) (orig : List (BitVec 32))
    (n : Nat) (hn64 : n < 2 ^ 64) :
    HTripleProgAt vecReverseProg F (revInvK orig n F)
      vecReverseWhile
      (fun st o => o = .fellThrough ∧ ∃ ρ' m' π' l',
        st = (ρ', m', π') ∧ l' = orig.reverse ∧
        envLookup ρ' "v" = some (.stdVecVal l')) := by
  have hzero : ∀ ρ m π, revInvK orig n 0 (ρ, m, π) →
      memEvalExpr (.ult (.var "i") (.var "j")) ρ m π
        = .ok (.b false) := by
    intro ρ m π hP
    obtain ⟨ρ₀, m₀, π₀, l, i, j, iB, jB, heq, hkit,
      hv, hi, hiN, hj, hjN, hlay, hmem, hinv⟩ := hP
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hle : j ≤ i := by
      by_cases hc : i < j
      · have hs := revIters_step i j hc
        omega
      · omega
    have hg := memEvalExpr_ult_ij ρ m π iB jB hi hj
    have hfb : (iB.ult jB) = false := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_false (by omega)
    rwa [hfb] at hg
  have hexit : ∀ k ρ m π, revInvK orig n k (ρ, m, π) →
      memEvalExpr (.ult (.var "i") (.var "j")) ρ m π
        = .ok (.b false) →
      (Outcome.fellThrough = Outcome.fellThrough ∧ ∃ ρ' m' π' l',
        (ρ, m, π) = (ρ', m', π') ∧ l' = orig.reverse ∧
        envLookup ρ' "v" = some (.stdVecVal l')) := by
    intro k ρ m π hP hg
    obtain ⟨ρ₀, m₀, π₀, l, i, j, iB, jB, heq, hkit,
      hv, hi, hiN, hj, hjN, hlay, hmem, hinv⟩ := hP
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hult := memEvalExpr_ult_ij ρ m π iB jB hi hj
    rw [hult] at hg
    have hbj : j ≤ i := by
      have h2 : (iB.ult jB) = false := by simpa using hg
      rw [BitVec.ult_eq_decide] at h2
      simp at h2
      omega
    exact ⟨rfl, ρ, m, π, l, rfl,
      RevInv_exit orig l n i j hinv hbj, hv⟩
  have hdec : ∀ k ρ m π, revInvK orig n (k + 1) (ρ, m, π) →
      memEvalExpr (.ult (.var "i") (.var "j")) ρ m π
        = .ok (.b false) ∨
      memEvalExpr (.ult (.var "i") (.var "j")) ρ m π
        = .ok (.b true) := by
    intro k ρ m π hP
    obtain ⟨ρ₀, m₀, π₀, l, i, j, iB, jB, heq, hkit,
      hv, hi, hiN, hj, hjN, hlay, hmem, hinv⟩ := hP
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hg := memEvalExpr_ult_ij ρ m π iB jB hi hj
    cases h : (iB.ult jB) with
    | false => exact Or.inl (by rwa [h] at hg)
    | true => exact Or.inr (by rwa [h] at hg)
  have hstep : ∀ k ρ m π, revInvK orig n (k + 1) (ρ, m, π) →
      memEvalExpr (.ult (.var "i") (.var "j")) ρ m π
        = .ok (.b true) →
      ∃ Pmid Qmid, HTripleProg vecReverseProg Pmid vecReverseBody Qmid ∧
        Pmid (ρ, m, π) ∧
        (∀ ρ' m' π' o, Qmid (ρ', m', π') o →
          (o = .fellThrough ∨ o = .continued) ∧
          revInvK orig n k (ρ', m', π')) := by
    intro k ρ m π hP hgt
    obtain ⟨ρ₀, m₀, π₀, l, i, j, iB, jB, heq, hkit,
      hv, hi, hiN, hj, hjN, hlay, hmem, hinv⟩ := hP
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hult := memEvalExpr_ult_ij ρ m π iB jB hi hj
    rw [hult] at hgt
    have htb : (iB.ult jB) = true := by simpa using hgt
    have hlt : i < j := by
      rw [BitVec.ult_eq_decide] at htb
      simp at htb
      omega
    obtain ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩ := hinv
    have hiL : i < l.length := by omega
    have hjL : j - 1 < l.length := by omega
    have ha : l[i]? = some l[i] := List.getElem?_eq_getElem hiL
    have hb : l[j - 1]? = some l[j - 1] :=
      List.getElem?_eq_getElem hjL
    refine ⟨_, _, (fun F' => hoare_reverseSwap F' orig l n i j
      iB jB l[i] l[j - 1]
      ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩
      hiN hjN hlt ha hb hn64), ?_, ?_⟩
    · exact ⟨ρ, m, π, rfl, hv, hi, hj, hlay, hmem⟩
    · intro ρ' m' π' o hQ
      obtain ⟨ho, ρ₁, m₁, π₁, heq', hv', hi', hj', hlay', hmem',
        hinv'⟩ := hQ
      simp only [Prod.mk.injEq] at heq'
      obtain ⟨rfl, rfl, rfl⟩ := heq'
      have hkit' : revIters (i + 1) (j - 1) = k := by
        have hs := revIters_step i j hlt
        omega
      have hsucc : (iB + 1).toNat = i + 1 := by
        have h := revU64_succ_toNat iB n (by omega) hn64
        omega
      have hpred : (jB - 1).toNat = j - 1 := by
        have h := revU64_pred_toNat jB (by omega)
        omega
      exact ⟨Or.inl ho, ρ', m', π', ((l.set i l[j - 1]).set (j - 1) l[i]),
        i + 1, j - 1, iB + 1, jB - 1, rfl, hkit', hv', hi', hsucc,
        hj', hpred, hlay', hmem', hinv'⟩
  exact htripleProg_while_at vecReverseProg (revInvK orig n)
    (fun st o => o = .fellThrough ∧ ∃ ρ' m' π' l',
      st = (ρ', m', π') ∧ l' = orig.reverse ∧
      envLookup ρ' "v" = some (.stdVecVal l'))
    (.ult (.var "i") (.var "j")) vecReverseBody
    hzero hexit hdec hstep F

/-- Segment swap-step triple: one shared `vecReverseBody` iteration
    over the window `[lo, hi)` (the S sibling of `hoare_reverseSwap`
    — thin triple sugar over `segMemBody_hit`; second use of the
    swap-step shape, still prose stage per the rule of three). -/
theorem hoare_segSwap (F : Nat)
    (orig l : List (BitVec 32)) (lo hiW i j : Nat)
    (iB jB : BitVec 64) (a b : BitVec 32)
    (hinv : SegInv orig l lo hiW i j)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (hlt : i < j)
    (ha : l[i]? = some a) (hb : l[j - 1]? = some b)
    (hlen64 : l.length < 2 ^ 64) :
    HTripleProgAt vecSegReverseProg F
      (fun st => ∃ ρ m π, st = (ρ, m, π) ∧
        envLookup ρ "v" = some (.stdVecVal l) ∧
        envLookup ρ "i" = some (.u64 iB) ∧
        envLookup ρ "j" = some (.u64 jB) ∧
        layoutLookup π "v" = some (0, 0) ∧
        memFind m 0 = some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)
      vecReverseBody
      (fun st o => o = .fellThrough ∧
        ∃ ρ' m' π', st = (ρ', m', π') ∧
        envLookup ρ' "v" =
          some (.stdVecVal ((l.set i b).set (j - 1) a)) ∧
        envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
        envLookup ρ' "j" = some (.u64 (jB - 1)) ∧
        layoutLookup π' "v" = some (0, 0) ∧
        memFind m' 0 = some ⟨0, true, (BitVec.ofNat 32 l.length) ::
          ((l.set i b).set (j - 1) a)⟩ ∧
        SegInv orig ((l.set i b).set (j - 1) a) lo hiW (i + 1)
          (j - 1)) := by
  intro ρ₀ m₀ π₀ hP
  obtain ⟨ρ₁, m₁, π₁, heq, hv, hi, hj, hlay, hmem⟩ := hP
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  obtain ⟨ρ', m', heval, hv', hi', hj', hmem', hinv'⟩ :=
    segMemBody_hit vecSegReverseProg F ρ₀ m₀ π₀ orig l lo hiW i j
      iB jB a b hinv hiN hjN hlt ha hb hlen64 hv hi hj hlay hmem
      segFindAt
  exact ⟨ρ', m', π₀, .fellThrough, heval, rfl,
    ρ', m', π₀, rfl, hv', hi', hj', hlay, hmem', hinv'⟩

end HoareGallery
