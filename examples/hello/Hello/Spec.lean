-- User-written spec + proof against `circe-emit` output.
-- This is the whole frontend loop on one page: read the generated
-- `Hello/Emitted.lean` (a pure forward over `BitVec`/`Result`),
-- state the property, prove it with the library lemmas
-- (`Circe.Base`), and check the executable `_spec_check` below
-- (the gate evaluates it to `true`).
import Hello.Emitted

/-- Small inputs add exactly (the `nsw` certificate discharges
    from the `toInt` bounds). -/
theorem hello_add_small (x y : BitVec 32)
    (hx0 : 0 ≤ x.toInt) (hx : x.toInt < 100)
    (hy0 : 0 ≤ y.toInt) (hy : y.toInt < 100) :
    add_fwd x y = .ok (x + y) := by
  unfold add_fwd
  apply checkedAddI32_ok
  rw [inInt32Range_iff]
  unfold int32Min int32Max
  constructor <;> omega

/-- Commutativity rides the library lemma. -/
theorem hello_add_comm (x y : BitVec 32) :
    add_fwd x y = add_fwd y x := by
  unfold add_fwd
  exact checkedAddI32_comm x y

/-- Executable check the gate evaluates (`true` required). -/
def hello_spec_check : Bool :=
  match add_fwd 2 3 with
  | .ok v => v == 5
  | .error _ => false
