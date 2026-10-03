/-
Circe.Scope — L1 scope/alloca evidence tracking (extract-only).

Raw CIRGen carries lexical lifetime evidence the pipeline currently drops
on the floor: `cir.scope` region nesting and named `cir.alloca` birth
points (true lifetime intrinsics do not exist at this pin — raw CIRGen
rejects `-flifetime-markers`, and no checked-in `.cir` mentions
`lifetime`). This module extracts that evidence as computed predicates
over `RawFunc.text` (the `derivedNoalias` precedent: no `RawFunc` churn,
no new trusted fields):

- `extractScopes`: per-line brace-depth fold (string literals stripped,
  so attribute dicts cannot disturb the count) recording each
  `cir.alloca "NAME"` with its normalized depth (function top level =
  0) plus the maximum decl depth. Scanning stops at the first
  return-to-zero (the function extent), so trailing module closes in a
  slice cannot pollute the count. `balanced = false` (never entered a
  body, went negative, or never closed) makes miscounts loud, never
  silent.

Proved: empty-text behavior (`extractScopes_empty`) and the depth-bound
invariant (`extractScopes_bound`: every recorded depth fits under
`maxDepth`). Per-corpus values are pinned by the `ScopeReport` runner.

Non-goals (extract-only slice): `validate`/`Emit`/transfer behavior is
unchanged — nothing consumes this yet (consumers arrive with later
slices, e.g. real region numbers for N4b moves). This module justifies
no admission on its own.
-/
import Circe.Parser

/-- A declared local: `cir.alloca` name + normalized scope depth
    (function top level = 0, one per enclosing `cir.scope`). -/
structure LocalDecl where
  name : String
  depth : Nat
  deriving DecidableEq, Repr

/-- Per-function scope evidence: locals in source order, the maximum
    recorded depth, and whether the scan was well-formed (entered a body,
    never went negative, closed back to zero). -/
structure ScopeInfo where
  locals : List LocalDecl
  maxDepth : Nat
  balanced : Bool
  deriving DecidableEq, Repr

/-- Fold state for the brace-depth scan. -/
structure ScopeState where
  cur : Int
  locals : List LocalDecl
  max : Nat
  ok : Bool
  started : Bool
  done : Bool

/-- Initial scan state (outside any body brace). -/
def scopeInit : ScopeState := ⟨0, [], 0, true, false, false⟩

/-- Drop `"..."` spans (attribute values, symbol names): brace counting
    must not see braces inside string literals. -/
def stripQuotes (s : String) : String :=
  String.ofList (go s.toList false [])
where
  go : List Char → Bool → List Char → List Char
  | [], _, acc => acc.reverse
  | '"' :: cs, q, acc => go cs (!q) acc
  | _ :: cs, true, acc => go cs true acc
  | c :: cs, false, acc => go cs false (c :: acc)

/-- Name declared by a `cir.alloca "NAME" ...` line, if well-formed. -/
def allocaOn (line : String) : Option String := do
  let k ← findSubstr? line "cir.alloca \"" 0
  let rest := (line.toList.drop (k + 12)).takeWhile (fun c => c != '"')
  if rest.isEmpty then none else some (String.ofList rest)

/-- One scan step: record an alloca at the current depth (normalized),
    then apply the line's brace delta. A `cir.alloca` line the
    name-extractor rejects, or any negative excursion, marks the scan
    bad (`balanced` will be `false`). -/
def scopeStep (st : ScopeState) (line : String) : ScopeState :=
  if st.done then st
  else
    let stripped := stripQuotes line
    let delta : Int :=
      (stripped.toList.count '{' : Int) - (stripped.toList.count '}' : Int)
    let cur' := st.cur + delta
    let started' := st.started || decide (0 < cur')
    let done' := started' && cur' == 0
    match allocaOn line with
    | some nm =>
      if st.cur < 1 then
        { cur := cur', locals := st.locals, max := st.max, ok := false,
          started := started', done := done' }
      else
        let d := (st.cur - 1).toNat
        { cur := cur', locals := ⟨nm, d⟩ :: st.locals,
          max := st.max.max d, ok := st.ok && decide (0 ≤ cur'),
          started := started', done := done' }
    | none =>
      { cur := cur', locals := st.locals, max := st.max,
        ok := st.ok && decide (0 ≤ cur') &&
          !containsSubstr line "cir.alloca",
        started := started', done := done' }

/-- Extract per-function scope evidence from a function text slice
    (e.g. `RawFunc.text`): locals in source order with normalized depths,
    the maximum recorded depth, and the well-formedness flag. -/
def extractScopes (text : String) : ScopeInfo :=
  let st := (text.splitOn "\n").foldl scopeStep scopeInit
  ⟨st.locals.reverse, st.max, st.done && st.ok⟩

/-! ## Extraction soundness -/

/-- Empty text extracts nothing and reports unbalanced (never entered). -/
theorem extractScopes_empty : extractScopes "" = ⟨[], 0, false⟩ := by
  native_decide

/-- One scan step preserves the depth bound: every recorded local fits
    under the running maximum. -/
theorem scopeStep_preserves_bound (st : ScopeState) (line : String)
    (h : ∀ d ∈ st.locals, d.depth ≤ st.max) :
    ∀ d ∈ (scopeStep st line).locals,
      d.depth ≤ (scopeStep st line).max := by
  by_cases hdone : st.done
  · have e : scopeStep st line = st := by
      unfold scopeStep
      simp [hdone]
    rw [e]
    exact h
  · cases hall : allocaOn line with
    | none =>
      have e : (scopeStep st line).locals = st.locals ∧
          (scopeStep st line).max = st.max := by
        unfold scopeStep
        simp [hdone, hall]
      obtain ⟨hl, hm⟩ := e
      rw [hl, hm]
      exact h
    | some nm =>
      by_cases hcur : st.cur < 1
      · have e : (scopeStep st line).locals = st.locals ∧
            (scopeStep st line).max = st.max := by
          unfold scopeStep
          simp [hdone, hall, hcur]
        obtain ⟨hl, hm⟩ := e
        rw [hl, hm]
        exact h
      · have e : ∀ d ∈ (scopeStep st line).locals,
            d.depth ≤ (scopeStep st line).max := by
          unfold scopeStep
          simp only [hdone, hall, hcur]
          show ∀ d_1 ∈ (⟨nm, (st.cur - 1).toNat⟩ :: st.locals),
            d_1.depth ≤ st.max.max (st.cur - 1).toNat
          intro d_1 hd
          rw [List.mem_cons] at hd
          cases hd with
          | inl heq =>
            subst heq
            exact Nat.le_max_right _ _
          | inr hmem =>
            exact Nat.le_trans (h _ hmem) (Nat.le_max_left _ _)
        exact e

/-- The bound survives a whole fold. -/
theorem foldl_scopeStep_bound (ls : List String) (st : ScopeState)
    (h : ∀ d ∈ st.locals, d.depth ≤ st.max) :
    ∀ d ∈ (ls.foldl scopeStep st).locals,
      d.depth ≤ (ls.foldl scopeStep st).max := by
  induction ls generalizing st with
  | nil => simpa using h
  | cons _ _ ih => exact ih _ (scopeStep_preserves_bound _ _ h)

/-- Every extracted local depth fits under the reported maximum. -/
theorem extractScopes_bound (t : String) :
    ∀ d ∈ (extractScopes t).locals,
      d.depth ≤ (extractScopes t).maxDepth := by
  unfold extractScopes
  show ∀ d ∈ ((t.splitOn "\n").foldl scopeStep scopeInit).locals.reverse,
    d.depth ≤ ((t.splitOn "\n").foldl scopeStep scopeInit).max
  intro d hd
  rw [List.mem_reverse] at hd
  exact foldl_scopeStep_bound _ _ (fun d' hd' => by simp [scopeInit] at hd') d hd
