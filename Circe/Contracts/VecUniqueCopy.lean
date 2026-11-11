/-
Circe.Contracts.VecUniqueCopy — stable contract for
`vec_unique_copy` (pillar-2 P2-M16 caller-record squeeze).

The kernel proofs (`Circe.Emit.VecUniqueCopy`,
`Circe.Transfer.VecUniqueCopy`) thread fuel, environments,
layouts, memory blocks, and `BitVec` conversions through
~2,000 lines. Callers should not re-thread any of that. This
module is the public surface:

- `vec_unique_copy_contract`: fits leg — the memory run
  returns the squeeze count over the squeezed prefix, record
  length unchanged; one theorem, no `Env`/`Mem`/`Layout`/fuel
  in the statement beyond the fuel bound every entry takes;
- `vec_unique_copy_contract_short`: short leg — a short
  record fails loud;
- `squeezeCopyInv` / `squeezeCopyInv_entry`: the loop
  invariant in ideal vocabulary and its establishment at the
  `(1, 1)` seed (maintenance is `uniqueCopyFwd_prefix`);
- `caller_copy_prefix_length`: a caller-side consequence
  proved using only the contract plus the `TwoCursor` pack —
  the plug-in-larger-proofs demo.

Nothing here changes existing statements: the facade
delegates to `evalProgFunc_vecUniqueCopy_spec_ok/_err`.
-/
import Circe.Transfer.VecUniqueCopy
import Circe.Lemmas.TwoCursor

/-- Loop invariant in ideal vocabulary: cursors in range, the
    recorded prefix is the squeeze of the scanned prefix,
    record length preserved against the caller-supplied
    length. Maintenance across keep/drop steps is
    `uniqueCopyFwd_prefix`; establishment at the seed is
    `squeezeCopyInv_entry` below. -/
def squeezeCopyInv (la lo₀ : List (BitVec 32)) (w r : Nat)
    (lo : List (BitVec 32)) : Prop :=
  1 ≤ w ∧ w ≤ r ∧ r ≤ la.length ∧
    lo.take w = dedupAdj (la.take r) ∧ lo.length = lo₀.length

/-- The `(1, 1)` seed establishes the invariant on any
    nonempty input with a nonempty record: the first word is
    the implicit first survivor, planted at record index 0. -/
theorem squeezeCopyInv_entry (a0 : BitVec 32)
    (xs lo : List (BitVec 32)) (h0lt : 0 < lo.length) :
    squeezeCopyInv (a0 :: xs) lo 1 1 (lo.set 0 a0) := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, by simp, ?_,
    by simp [List.length_set]⟩
  rw [show (1 : Nat) = 0 + 1 from rfl,
    take_set_succ_self lo 0 a0 h0lt]
  simp [dedupAdj]

/-- Stable contract, fits leg: on sufficient fuel with a
    fitting record, the memory run returns the squeeze count
    over the squeezed prefix, record length unchanged. This
    is the only theorem callers need for the fits case — it
    is `evalProgFunc_vecUniqueCopy_spec_ok` restated without
    kernel vocabulary. -/
theorem vec_unique_copy_contract (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hcap : (dedupAdj la).length ≤ lo.length) :
    ∃ (w' : Nat) (lo' : List (BitVec 32)),
      memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
        [.stdVecVal la, .stdVecVal lo] =
        .ok (.u64 (BitVec.ofNat 64 w')) ∧
      lo'.take w' = dedupAdj la ∧
      w' = (dedupAdj la).length ∧
      lo'.length = lo.length :=
  evalProgFunc_vecUniqueCopy_spec_ok F la lo hla64 hlo64 hF hcap

/-- Stable contract, short leg: a short record fails loud on
    the memory layer. (The kernel spec previously carried a
    contradictory capacity hypothesis alongside the
    shortness fact, making this leg unusable; the facade
    takes only the shortness fact.) -/
theorem vec_unique_copy_contract_short (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hmore : lo.length < (dedupAdj la).length) :
    memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .error .AssertFail :=
  evalProgFunc_vecUniqueCopy_spec_err F la lo hla64 hlo64 hF hmore

/-- Caller-side consequence, proved using only the contract
    plus the `TwoCursor` pack: the recorded prefix has
    exactly the returned length. No evaluator, memory, or
    fuel facts appear — the larger proof plugs the contract
    in and reasons about lists. -/
theorem caller_copy_prefix_length (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hcap : (dedupAdj la).length ≤ lo.length) :
    ∃ (w' : Nat) (lo' : List (BitVec 32)),
      memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
        [.stdVecVal la, .stdVecVal lo] =
        .ok (.u64 (BitVec.ofNat 64 w')) ∧
      (lo'.take w').length = w' := by
  obtain ⟨w', lo', heval, _hpref, hwlen, hlen'⟩ :=
    vec_unique_copy_contract F la lo hla64 hlo64 hF hcap
  refine ⟨w', lo', heval, ?_⟩
  exact take_length_of_le _ _ (by omega)
