-- Tactic showcase for users (U1): every tactic reachable via
-- `import Circe.Tactics` demonstrated on the Hello program or its
-- immediate neighbors. `Spec.lean` stays plain-Lean (the no-magic
-- baseline); this file shows the shortcuts. All proofs are checked
-- by `lake build Hello` — this module IS the tactic test suite.
import Hello.Emitted
import Hello.Spec
import Circe.Tactics
import Circe.Emit.Choose
import Circe.Emit.Span

/-- Algebraic facts stay explicit: commutativity is one lemma
    application (`checkedAddI32_comm`), not a simp call — `simp`
    rejects permutative rewrites it cannot orient, so the curated
    set deliberately carries no commutation lemmas. -/
theorem hello_add_comm_simp (x y : BitVec 32) :
    add_fwd x y = add_fwd y x := by
  unfold add_fwd
  exact checkedAddI32_comm x y

/-- `cir_simp`: the curated simp set. Unfold your own forward,
    then let it discharge the library layer — here it unfolds the
    checked op, applies the ok-rule with the certificate `h`, and
    splits the range test, leaving pure integer arithmetic for
    the next tactic. -/
theorem hello_add_ok_set (x y : BitVec 32)
    (h : inInt32Range (x.toInt + y.toInt) = true) :
    add_fwd x y = .ok (x + y) := by
  unfold add_fwd
  cir_simp
  exact (inInt32Range_iff _).mp h

/-- `cir_eval_closed`: closed executable checks evaluate in the
    kernel (`native_decide`). The same fact the gate checks at
    runtime via `hello_spec_check`. -/
theorem hello_check_true : hello_spec_check = true := by
  cir_eval_closed

/-- `cir_fuel`: fuel-side arithmetic (`k ≤ F` from `k + 1 ≤ F`) —
    the side-condition shape composer fuel splits leave behind.
    Advanced tier: only fuel-induction proofs meet it. -/
theorem hello_fuel_side (k F : Nat) (h : k + 1 ≤ F) : k ≤ F := by
  cir_fuel

/-- `cir_choose`: case-split on a boolean selector, then simplify
    with the verified forward/backward equations. Specialized to
    choose-family programs (cf. the library `choose_back_get_put`);
    the selector must be a variable — casing on a literal leaves
    the impossible branch behind. -/
theorem hello_choose_get_put (b : Bool) (x y : BitVec 32) :
    chooseBack b x y (if b then x else y) = .ok (.i32 x, .i32 y) := by
  cir_choose b

/-- `cir_step`: one symbolic evaluator-cascade step with explicit
    hypotheses as arguments — the per-step shape composer loop
    proofs repeat (`Span.lean` precedent). Pass every lookup fact
    the step touches: the cascade unfolds the evaluator, rewrites
    each `envLookup`, and reduces what the hypotheses cover.
    Advanced tier: statement-level fuel equation proofs. -/
theorem hello_step_uadd (aB bB : BitVec 64) (ρ : Env)
    (ha : envLookup ρ "a" = some (.u64 aB))
    (hb : envLookup ρ "b" = some (.u64 bB)) :
    evalExpr (.uadd (.var "a") (.var "b")) ρ
      = .ok (.u64 (aB + bB)) := by
  cir_step evalExpr [ha, hb]

/-- `cir_fold_end`: the suffix-fold end script — unfold one step on
    the left via the drop equation, discharge the lookup. The six
    in-repo sites (`spanFold_*`, `viewFold_*`, `stdVecFold_*`
    step/nil pairs) run this exact script; here it is on the
    library `spanFold` itself, the same shape a user meets at the
    end of any suffix-fold proof. Pass the drop equation for your
    fold plus the lookup fact. -/
theorem hello_fold_end (l : List (BitVec 32)) (k : Nat)
    (acc : BitVec 32) (hget : l[k]? = none) :
    spanFold (l.drop k) acc = .ok acc := by
  cir_fold_end (spanFold_drop, hget)
