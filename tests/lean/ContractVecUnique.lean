-- Contract-facade regression test (pillar-3 P3-N7): the squeeze
-- pack lemmas compute on concrete data, the `cir_*` tactics close
-- synthetic goals, and the facade pieces compose. Run from the
-- repo root via the driver (`lake exe circe-test` runs
-- `ContractVecUnique.main`).
import Circe.Contracts.VecUnique

namespace ContractVecUnique

/-- Pack lemma on a concrete squeeze: the `w'`-prefix of the final
    words is the oracle squeeze, so the count is the oracle
    length (covers `squeeze_length_eq` + `take_length_of_le`). -/
example : (3 : Nat) = (dedupAdj ([1, 2, 3, 3] : List (BitVec 32))).length := by
  have hpre : ([1, 2, 3, 3] : List (BitVec 32)).take 3
      = dedupAdj (([1, 2, 3, 3] : List (BitVec 32)).take 4) := by decide
  exact squeeze_length_eq _ _ 3 hpre (by decide)

/-- Facade pieces compose: the `(1, 1)` seed establishes the
    invariant on any nonempty input. -/
example (x : BitVec 32) (xs : List (BitVec 32)) :
    squeezeInv (x :: xs) 1 1 (x :: xs) :=
  squeezeInv_entry x xs

/-- `cir_mem_let` on a synthetic pure-`let_` goal (covers both
    discrimination shapes: binder-ful `vnew`/`boxNew`/`vgrowNew`
    and binder-free `nnew`). -/
example (prog : Prog) (F : Nat) (ρ : Env) (m : Mem) (π : Layout)
    (v : Value)
    (hM : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 7))) ρ m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 7))) ρ)
    (hV : evalExpr (.lit (.u64 (BitVec.ofNat 64 7))) ρ = .ok v) :
    memEvalProgStmt prog F
      (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 7)))) ρ m π =
      .ok ((envExtend ρ "w" v, m, π), .fellThrough) := by
  cir_mem_let (hM, hV)

/-- `cir_lookup`: direct hit. -/
example (ρ : Env) (v : Value) :
    envLookup (envExtend ρ "w" v) "w" = some v := by
  cir_lookup

/-- `cir_lookup`: one-deep miss chain (sought name under an outer
    frame). -/
example (ρ : Env) (v₁ v₂ : Value) :
    envLookup (envExtend (envExtend ρ "w" v₂) "r" v₁) "w" = some v₂ := by
  cir_lookup

/-- `cir_lookup`: two-deep miss chain. -/
example (ρ : Env) (v₁ v₂ v₃ : Value) :
    envLookup (envExtend (envExtend (envExtend ρ "w" v₃) "n" v₂) "r" v₁)
      "w" = some v₃ := by
  cir_lookup

def checkPack : IO Nat := do
  let mut n := 0
  let l : List (BitVec 32) := [1, 2, 3, 3]
  if l.take 3 != dedupAdj (l.take 4) then
    throw (IO.userError "contract-vecunique: squeeze prefix mismatch")
  IO.println "PASS contract-vecunique squeeze-prefix [concrete]"
  n := n + 1
  if (l.take 3).length != 3 then
    throw (IO.userError "contract-vecunique: take length mismatch")
  IO.println "PASS contract-vecunique take-length [concrete]"
  n := n + 1
  if (dedupAdj l).length != 3 then
    throw (IO.userError "contract-vecunique: squeezed length mismatch")
  IO.println "PASS contract-vecunique squeezed-length [concrete]"
  n := n + 1
  pure n

def main : IO Unit := do
  let c ← checkPack
  IO.println s!"CONTRACTVECUNIQUE-OK passed={c}"

end ContractVecUnique
