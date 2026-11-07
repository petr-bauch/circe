/-
Circe.Contracts.VecUnique — stable contract for `vec_unique`
(P3-N2/N7 facade).

The kernel proofs (`Circe.Emit.VecUnique`,
`Circe.Transfer.VecUnique`, `Circe.Specs`) thread fuel,
environments, layouts, memory blocks, and `BitVec` conversions
through ~1,700 lines. Callers should not re-thread any of
that. This module is the public surface:

- `vec_unique_contract`: memory evaluation agrees with value
  evaluation and returns the squeezed length — one theorem,
  no `Env`/`Mem`/`Layout`/fuel in the statement beyond the
  fuel bound every entry takes;
- `vecUnique_prelude_triple`: the `(w, r) := (1, 1)` prelude
  as a Hoare triple over `cursorAt` assertions — the shape of
  future loop-triple proofs, proved with the `cir_*` tactics;
- `caller_truncate_length`: a caller-side consequence proved
  using only the contract plus the `TwoCursor` pack — the
  plug-in-larger-proofs demo;
- `squeezeInv` / `squeezeInv_entry`: the loop invariant in
  ideal vocabulary and its establishment at the `(1, 1)`
  seed (maintenance is `uniqueFwd_prefix`).

Nothing here changes existing statements: the facade delegates
to `evalProgFunc_vecUnique_spec`, `memTransferProg_vecUnique_ok`,
and the evaluator equations.
-/
import Circe.Transfer.VecUnique
import Circe.Specs
import Circe.Lemmas.TwoCursor
import Circe.Hoare.Vec
import Circe.Contracts.Tactics

/-- Loop invariant in ideal vocabulary: cursors in range, the
    kept prefix is the squeeze of the scanned prefix, length
    preserved. Maintenance across keep/drop steps is
    `uniqueFwd_prefix`; establishment at the seed is
    `squeezeInv_entry` below. -/
def squeezeInv (l₀ : List (BitVec 32)) (w r : Nat)
    (l : List (BitVec 32)) : Prop :=
  1 ≤ w ∧ w ≤ r ∧ r ≤ l₀.length ∧
    l.take w = dedupAdj (l₀.take r) ∧ l.length = l₀.length

/-- The `(1, 1)` seed establishes the invariant on any nonempty
    input: the first word is the implicit first survivor. -/
theorem squeezeInv_entry (x : BitVec 32) (xs : List (BitVec 32)) :
    squeezeInv (x :: xs) 1 1 (x :: xs) := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, by simp, ?_, rfl⟩
  simp [dedupAdj]

/-- Stable contract: on sufficient fuel the memory run returns
    the squeezed length, bounded by the input length. This is
    the only theorem callers need — it bundles the value spec
    (`evalProgFunc_vecUnique_spec`) with the memory/value
    agreement (`memTransferProg_vecUnique_ok`). -/
theorem vec_unique_contract (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y) :
    ∃ w', memEvalProgFunc vecUniqueProg F vecUniqueFunc
      [.stdVecVal l] = .ok (.u64 (BitVec.ofNat 64 w')) ∧
      w' = (dedupAdj l).length ∧ w' ≤ l.length := by
  obtain ⟨w', heval, hlen, hle⟩ :=
    evalProgFunc_vecUnique_spec F l hl64 hF hread
  refine ⟨w', ?_, hlen, hle⟩
  rw [memTransferProg_vecUnique_ok F l hl64 hF hread
    (oracleNoalias_vecUnique l)]
  exact heval

/-- The `(w, r) := (1, 1)` prelude as a Hoare triple: both
    cursors hold `1`, memory and layout untouched. Proved with
    `cir_mem_let` (the two `let_` steps) and `cir_lookup` (the
    cursor facts) — no manual `envExtend` chains. -/
theorem vecUnique_prelude_triple (ρ : Env) (m : Mem) (π : Layout) :
    HTripleProg vecUniqueProg (fun st => st = (ρ, m, π))
      (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
        (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1)))))
      (fun st o => o = .fellThrough ∧ cursorAt "w" 1 st ∧
        cursorAt "r" 1 st ∧ st.2.1 = m ∧ st.2.2 = π) := by
  intro F
  have h1N : (BitVec.ofNat 64 1).toNat = 1 := by decide
  have litW : evalExpr (.lit (.u64 (BitVec.ofNat 64 1))) ρ =
      .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
  have hlitWM : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1))) ρ m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1))) ρ :=
    memEvalExpr_lit _ _ _ _
  have hletW : memEvalProgStmt vecUniqueProg F
      (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1)))) ρ m π =
      .ok ((envExtend ρ "w" (.u64 (BitVec.ofNat 64 1)), m, π),
        .fellThrough) := by
    cir_mem_let (hlitWM, litW)
  have litR : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1))) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
  have hlitRM : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1))) m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1))) :=
    memEvalExpr_lit _ _ _ _
  have hletR : memEvalProgStmt vecUniqueProg F
      (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1))) m π =
      .ok ((envExtend (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1)), m, π),
        .fellThrough) := by
    cir_mem_let (hlitRM, litR)
  have hW1 : cursorAt "w" 1
      (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1)), m, π) := by
    have hlookup : envLookup
        (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1))) "w" =
        some (.u64 (BitVec.ofNat 64 1)) := by cir_lookup
    exact cursorAt_of "w" 1 _ _ _ _ hlookup h1N
  intro ρ₀ m₀ π₀ hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  have hseq := memEvalProgStmt_seq_fallthrough vecUniqueProg F
    (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
    (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
    ρ m π _ _ _ hletW
  rw [hseq, hletR]
  have hW2 : cursorAt "w" 1
      (envExtend (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1)), m, π) := by
    obtain ⟨b, hb, hbn⟩ := hW1
    have hmiss : envLookup
        (envExtend (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1))) "w" =
        envLookup (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1))) "w" :=
      envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "r" by decide)
    exact ⟨b, by rw [hmiss]; exact hb, hbn⟩
  have hR2 : cursorAt "r" 1
      (envExtend (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1)), m, π) := by
    have hlookup : envLookup
        (envExtend (envExtend ρ "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1))) "r" =
        some (.u64 (BitVec.ofNat 64 1)) := by cir_lookup
    exact cursorAt_of "r" 1 _ _ _ _ hlookup h1N
  exact ⟨_, _, _, _, rfl, rfl, hW2, hR2, rfl, rfl⟩

/-- Caller-side consequence, proved using only the contract
    plus the `TwoCursor` pack: truncating the squeeze to the
    returned count yields a prefix of exactly that length.
    No evaluator, memory, or fuel facts appear — the larger
    proof plugs the contract in and reasons about lists. -/
theorem caller_truncate_length (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y) :
    ∃ w', memEvalProgFunc vecUniqueProg F vecUniqueFunc
      [.stdVecVal l] = .ok (.u64 (BitVec.ofNat 64 w')) ∧
      ((dedupAdj l).take w').length = w' := by
  obtain ⟨w', heval, hlen, hle⟩ :=
    vec_unique_contract F l hl64 hF hread
  refine ⟨w', heval, ?_⟩
  rw [hlen]
  exact take_length_of_le _ _ (Nat.le_refl _)
