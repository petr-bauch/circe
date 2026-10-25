import Circe.Eval.Stmt

/-!
# Short-read loop plumbing

Reusable first-order bricks for loops that fail on an out-of-bounds
read. The recipe, used by the K6c twins and any future short-read
loop:

* induction on "iterations remaining until the failing read",
  generalizing the mutated state (message, counter) and fuel;
* zero case: the guard holds and the failing read evaluates to
  `.error`, so the body errors and `whileErr_of_bodyErr` closes
  the loop;
* successor case: both reads hit, the body falls through, and
  `whileStep_of_bodyOk` advances the loop to the post-body env
  for the induction hypothesis;
* fuel covers one iteration per remaining word (`n + 1 ≤ F`),
  discharged by `cases F` with the zero subcase closed by
  the fuel hypothesis.

The read-miss evaluations and the remaining-iterations measure
stay per-loop (they name the loop's arrays); everything about
the `while` itself lives here.
-/

/-- One failing iteration: the guard holds and the body errors, so
    the loop errors (any short-read loop, any panic). -/
theorem whileErr_of_bodyErr (prog : Prog) (F' : Nat)
    (c : CExpr) (body loop : CStmt) (ρ : Env) (e : Panic)
    (hloop : loop = .while_ c body)
    (hguard : evalExpr c ρ = .ok (.b true))
    (herr : evalProgStmt prog F' body ρ = .error e) :
    evalProgStmt prog (F' + 1) loop ρ = .error e := by
  rw [hloop, evalProgStmt_while_true _ _ _ _ _ hguard, herr]

/-- One successful iteration: the guard holds and the body falls
    through, so the loop steps to the post-body env at predecessor
    fuel (any short-read loop). -/
theorem whileStep_of_bodyOk (prog : Prog) (F' : Nat)
    (c : CExpr) (body loop : CStmt) (ρ ρ' : Env)
    (hloop : loop = .while_ c body)
    (hguard : evalExpr c ρ = .ok (.b true))
    (hok : evalProgStmt prog F' body ρ = .ok (ρ', .fellThrough)) :
    evalProgStmt prog (F' + 1) loop ρ =
      evalProgStmt prog F' loop ρ' := by
  simp only [hloop, evalProgStmt_while_true prog F' _ _ _ hguard, hok]

/-- An `i`-bounded loop guard reads true: the counter is below the
    bound and the bound expression evaluates (any short-read loop;
    the counter lookup and bound fact stay caller-side). -/
theorem iterGuardT (bnd : CExpr) (ρ : Env) (iB : BitVec 64) (i N : Nat)
    (hi : iB.toNat = i) (hN64 : N < 2 ^ 64) (hiN : i < N)
    (hivar : evalExpr (.var "i") ρ = .ok (.u64 iB))
    (hb : evalExpr bnd ρ = .ok (.u64 (BitVec.ofNat 64 N))) :
    evalExpr (.ult (.var "i") bnd) ρ = .ok (.b true) := by
  have hN : (BitVec.ofNat 64 N).toNat = N := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hN64
  have htrue : iB.ult (BitVec.ofNat 64 N) = true := by
    rw [BitVec.ult_eq_decide, hi, hN]
    exact decide_eq_true (by omega)
  have h := evalExpr_ult_u64 (.var "i") bnd _ iB (BitVec.ofNat 64 N)
    hivar hb
  rwa [htrue] at h
