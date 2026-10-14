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
  have hlit0 : ∀ (ρ' : Env) (m' : Mem),
      memEvalExpr (.lit (.u64 0)) ρ' m' π = .ok (.u64 0) := by
    intro ρ' m'
    rw [memEvalExpr_lit]
    rfl
  have hlit1 : ∀ (ρ' : Env) (m' : Mem),
      memEvalExpr (.lit (.i32 1)) ρ' m' π = .ok (.i32 1) := by
    intro ρ' m'
    rw [memEvalExpr_lit]
    rfl
  have hv1 : memEvalExpr
      (.add (.mload "pa" (.lit (.u64 0))) (.lit (.i32 1))) ρ m π
      = .ok (.i32 (v + 1)) := by
    have h := memEvalExpr_add_ok _ _ ρ m π v 1
      (hexpr_mload "pa" (.lit (.u64 0)) ρ m π 0 v a t₁
        hla (hlit0 ρ m) hma)
      (hlit1 ρ m)
    rw [hov] at h
    exact h
  have hv2 : memEvalExpr
      (.add (.mload "pb" (.lit (.u64 0))) (.lit (.i32 1))) ρ ma π
      = .ok (.i32 (w + 1)) := by
    have h := memEvalExpr_add_ok _ _ ρ ma π w 1
      (hexpr_mload "pb" (.lit (.u64 0)) ρ ma π 0 w b t₂
        hlb (hlit0 ρ ma) hmb)
      (hlit1 ρ ma)
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
        (hlit0 ρ m) rfl hv1 hla hsa hca hcb hne)
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
      (hlit0 ρ ma) rfl hv2 hlb hsb hB hA (Ne.symm hne)
    obtain ⟨ρ₂, m₂, π₂, o₂, hev₂, hQ₂⟩ := hfr F ρ ma π rfl
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, hW, hF⟩ := hQ₂
    exact ⟨ρ, mb, π, .fellThrough, hev₂, rfl, rfl, hF, hW⟩
  exact htriple_seq _ _ _ _ _ hfirst hsecond

/-- Closed-instance runtime check: `pa=10, pb=20` evaluates to
    `pa=11, pb=21` with `fellThrough` — the executable shadow of
    `hoare_gallery` at one point (the proof itself is
    compile-gated). -/
def main : IO Unit := do
  let (m0, a) := memAllocData emptyMem [10]
  let (m1, b) := memAllocData m0 [20]
  let π : Layout := [("pa", a, a), ("pb", b, b)]
  match memEvalStmtFuel 20 galleryBody [] m1 π with
  | .error e =>
    throw (IO.userError
      s!"hoare-gallery: closed instance failed: {(repr e).pretty}")
  | .ok ((_, m', _), .fellThrough) =>
    match memFind m' a, memFind m' b with
    | some ba, some bb =>
      if ba.data != [11] || bb.data != [21] then
        throw (IO.userError
          s!"hoare-gallery: cells={ba.data},{bb.data}, want ([11],[21])")
      else IO.println "HOAREGALLERY-OK passed=1"
    | _, _ =>
      throw (IO.userError "hoare-gallery: cells missing after run")
  | .ok _ =>
    throw (IO.userError "hoare-gallery: want fellThrough")

end HoareGallery
