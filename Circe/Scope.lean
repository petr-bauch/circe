/-
Circe.Scope — L1 scope/alloca evidence tracking + L2 live-range facts
(extract-only).

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
    (function top level = 0, one per enclosing `cir.scope`) + L2
    live-range facts (`firstUse`/`lastUse` are 1-based line indices
    within the function text; `(0, 0)` means no use observed). -/
structure LocalDecl where
  name : String
  depth : Nat
  firstUse : Nat := 0
  lastUse : Nat := 0
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
        { cur := cur', locals := ⟨nm, d, 0, 0⟩ :: st.locals,
          max := st.max.max d, ok := st.ok && decide (0 ≤ cur'),
          started := started', done := done' }
    | none =>
      { cur := cur', locals := st.locals, max := st.max,
        ok := st.ok && decide (0 ≤ cur') &&
          !containsSubstr line "cir.alloca",
        started := started', done := done' }

/-! ## L2 live-range facts (use-site scan) -/

/-- Leading SSA definition id: a line whose left-trimmed text is
    `%N = ...` defines SSA value `N` (`%arg0`-style params never
    match: the char after `%` must be a digit). -/
def ssaDefOn (line : String) : Option Nat := do
  let cs := line.toList.dropWhile (· == ' ')
  match cs with
  | '%' :: d :: ds =>
    if d.isDigit then
      let after := (ds.dropWhile (·.isDigit)).dropWhile (· == ' ')
      match after with
      | '=' :: _ => some (String.toNat! (String.ofList (d :: ds.takeWhile (·.isDigit))))
      | _ => none
    else none
  | _ => none

/-- `%N` occurs as an operand: the `%`-digits match with a non-digit
    boundary after the digits (so `%1` never matches `%10`, and
    `%arg0` never matches anything). -/
def mentionsSSA (s : String) (n : Nat) : Bool :=
  go s.toList
where
  needle : List Char := '%' :: (toString n).toList
  go : List Char → Bool
  | [] => false
  | h :: hs =>
    if isPrefixOfList needle (h :: hs) then
      match (h :: hs).drop needle.length with
      | [] => true
      | c :: _ => !c.isDigit || go hs
    else go hs

/-- Operand text: drops a leading `%M = ` definition prefix (the
    birth is never a use); non-definition lines pass through. -/
def defRest (line : String) : String :=
  match ssaDefOn line with
  | none => line
  | some _ =>
    match ((line.toList.dropWhile (· == ' ')).drop 1 |>.dropWhile (·.isDigit) |>.dropWhile (· == ' ')) with
    | '=' :: rest => String.ofList rest
    | _ => line

/-- Region path per line (outermost-first region ids; `[]` is the
    function top level). Opens: trailing `{`; closes: leading `}`
    (`} body {` closes one and opens one). Attribute dicts balance
    within their line and string literals are stripped first, so
    only region braces count. -/
structure RegFold where
  nextId : Nat
  stack : List Nat
  paths : List (List Nat)

def regStep (st : RegFold) (ln : String) : RegFold :=
  let bare := (stripQuotes ln).toList
  let nClose := ((bare.dropWhile (· == ' ')).takeWhile (· == '}')).length
  let stack' := st.stack.drop nClose
  let path := stack'.reverse
  let nOpen :=
    (((bare.reverse.dropWhile (· == ' ')).takeWhile (· == '{')).length)
  let ids := List.range nOpen |>.map (st.nextId + ·)
  ⟨st.nextId + nOpen, ids.reverse ++ stack', path :: st.paths⟩

/-- Region paths in line order. -/
def regionPaths (lines : List String) : List (List Nat) :=
  (lines.foldl regStep ⟨0, [], []⟩).paths.reverse

/-- Every SSA definition with its region: ((path, id)) in line order. -/
def allSsaDefs (lines : List String) (paths : List (List Nat)) :
    List (List Nat × Nat) :=
  (lines.zip paths).filterMap fun (ln, p) =>
    (ssaDefOn ln).map (p, ·)

/-- Nearest enclosing definition of SSA `n` visible at `path` (the
    path itself, then outward to the top level). -/
def resolveDef (defs : List (List Nat × Nat)) (path : List Nat)
    (n : Nat) : Option (List Nat) :=
  go (path.length + 1) path
where
  go : Nat → List Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, p =>
    if defs.any (fun d => d.1 == p && d.2 == n) then some p
    else go fuel p.dropLast

/-- Alloca definitions in line order: (name, ssa id, 1-based decl
    line, decl region path). -/
def allocaDefs (lines : List String) :
    List (String × Nat × Nat × List Nat) :=
  let paths := regionPaths lines
  (lines.zipIdx.zip paths).filterMap fun ((ln, i), p) =>
    match allocaOn ln, ssaDefOn ln with
    | some nm, some ssa => some (nm, ssa, i + 1, p)
    | _, _ => none

/-- One closure pass over the lines: a `cir.load` whose operand
    resolves to a tracked definition extends the set with its
    defined id (keyed by its own region). Unresolvable mentions
    count conservatively for every root tracking the id (sound
    direction: longer ranges admit less). Only `cir.load` copies
    are chased (the slice's stated op bound — stores to memory
    create no aliases; `ptr_stride` results are fresh values). -/
def closurePass (lines : List String) (paths : List (List Nat))
    (defs : List (List Nat × Nat))
    (sets : List (Nat × List (List Nat × Nat))) :
    List (Nat × List (List Nat × Nat)) :=
  ((lines.zip paths).foldl (fun acc (ln, p) =>
    match ssaDefOn ln with
    | none => acc
    | some m =>
      if containsSubstr ln "cir.load" then
        let ops := defRest (stripQuotes ln)
        acc.map fun (r, t) =>
          let hit := t.any fun (rd, n) =>
            mentionsSSA ops n &&
              (resolveDef defs p n == some rd ||
                resolveDef defs p n == none)
          if hit && !t.contains (p, m) then (r, (p, m) :: t)
          else (r, t)
      else acc) sets)

/-- Closure to fixpoint (fuel bounds the passes; each productive
    pass adds at least one SSA id, and ids are finite). -/
def closeTracked (fuel : Nat) (lines : List String) (paths : List (List Nat))
    (defs : List (List Nat × Nat))
    (sets : List (Nat × List (List Nat × Nat))) :
    List (Nat × List (List Nat × Nat)) :=
  match fuel with
  | 0 => sets
  | fuel + 1 =>
    let s' := closurePass lines paths defs sets
    if s' == sets then sets else closeTracked fuel lines paths defs s'

/-- 1-based use lines for one root: operand mentions resolving to a
    tracked definition (conservatively: unresolvable mentions of a
    tracked id), excluding the declaration line itself. -/
def rootUses (lines : List String) (paths : List (List Nat))
    (defs : List (List Nat × Nat)) (declLine : Nat)
    (tracked : List (List Nat × Nat)) : List Nat :=
  (lines.zipIdx.zip paths).filterMap fun ((ln, i), p) =>
    if i + 1 != declLine &&
        tracked.any fun (rd, n) =>
          mentionsSSA (defRest (stripQuotes ln)) n &&
            (resolveDef defs p n == some rd ||
              resolveDef defs p n == none) then
      some (i + 1)
    else none

/-- Fill one declaration's use facts from the (name, first, last) table
    (first table hit wins; corpus alloca names are unique). -/
def fillOne (uses : List (String × Nat × Nat)) (d : LocalDecl) : LocalDecl :=
  match uses.find? (fun u => u.1 == d.name) with
  | some (_, f, l) => ⟨d.name, d.depth, f, l⟩
  | none => d

/-- Use facts for every alloca: (name, first-use line, last-use line),
    `(0, 0)` when nothing is observed. Roots start at their own
    declaration region (entry-block allocas nest at most one
    `cir.scope` deep in the corpus). -/
def useFacts (lines : List String) : List (String × Nat × Nat) :=
  let paths := regionPaths lines
  let defs := allocaDefs lines
  let alldefs := allSsaDefs lines paths
  let closed :=
    closeTracked (lines.length + 1) lines paths alldefs
      (defs.map fun (_, ssa, _, dp) => (ssa, [(dp, ssa)]))
  defs.map fun (nm, ssa, dl, _) =>
    match closed.find? (fun p => p.1 == ssa) with
    | some (_, t) =>
      let us := rootUses lines paths alldefs dl t
      (nm, us.min?.getD 0, us.max?.getD 0)
    | none => (nm, 0, 0)

/-- Extract per-function scope evidence from a function text slice
    (e.g. `RawFunc.text`): locals in source order with normalized depths,
    the maximum recorded depth, and the well-formedness flag. -/
def extractScopes (text : String) : ScopeInfo :=
  let lines := text.splitOn "\n"
  let st := lines.foldl scopeStep scopeInit
  ⟨st.locals.reverse.map (fillOne (useFacts lines)), st.max,
    st.done && st.ok⟩

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
          show ∀ d_1 ∈ (⟨nm, (st.cur - 1).toNat, 0, 0⟩ :: st.locals),
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

/-- Fill preserves the declaration (name and depth are untouched). -/
theorem fillOne_mem {uses : List (String × Nat × Nat)} {d : LocalDecl}
    (h : d ∈ List.map (fillOne uses) l) :
    ∃ q ∈ l, d.depth = q.depth := by
  rw [List.mem_map] at h
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨q, hq, by unfold fillOne; split <;> rfl⟩

/-- Every extracted local depth fits under the reported maximum. -/
theorem extractScopes_bound (t : String) :
    ∀ d ∈ (extractScopes t).locals,
      d.depth ≤ (extractScopes t).maxDepth := by
  unfold extractScopes
  intro d hd
  dsimp only at hd ⊢
  obtain ⟨q, hq, hqd⟩ := fillOne_mem hd
  rw [List.mem_reverse] at hq
  have hqb := foldl_scopeStep_bound _ _
    (fun d' hd' => by simp [scopeInit] at hd') q hq
  rw [hqd]
  exact hqb


/-- First use never exceeds last use (both zero when unobserved). -/
theorem minD_le_maxD (us : List Nat) :
    us.min?.getD 0 ≤ us.max?.getD 0 := by
  cases us with
  | nil => simp
  | cons x xs =>
    have hx : x ∈ x :: xs := List.mem_cons_self ..
    have hne : (x :: xs) ≠ [] := List.ne_nil_of_mem hx
    rw [List.min?_eq_some_min hne, List.max?_eq_some_max hne]
    simp only [Option.getD_some]
    exact Nat.le_trans (List.min_le_of_mem hx) (List.le_max_of_mem hx)


/-- A recorded use line is a real line of the scanned text. -/
theorem rootUses_mem_bound (lines : List String) (paths : List (List Nat))
    (defs : List (List Nat × Nat)) (declLine : Nat)
    (tracked : List (List Nat × Nat)) (u : Nat)
    (hu : u ∈ rootUses lines paths defs declLine tracked) :
    u ≤ lines.length := by
  rw [rootUses, List.mem_filterMap] at hu
  obtain ⟨⟨⟨ln, i⟩, _⟩, hmem, heq⟩ := hu
  have hmem' : (ln, i) ∈ lines.zipIdx := (List.of_mem_zip hmem).left
  rw [List.mem_zipIdx_iff_getElem?] at hmem'
  simp only at hmem'
  have hilt : i < lines.length := by
    by_cases hcon : i < lines.length
    · exact hcon
    · exfalso
      have hle : lines.length ≤ i := by
        cases Nat.lt_or_ge i lines.length with
        | inl h => exact absurd h hcon
        | inr h => exact h
      have hnone : lines[i]? = none :=
        (List.getElem?_eq_none_iff).mpr hle
      rw [hnone] at hmem'
      cases hmem'
  have hu_eq : u = i + 1 := by
    simp only at heq
    revert heq
    split
    · intro h
      exact (Option.some_inj.mp h).symm
    · intro h
      cases h
  omega

/-- Folded `max` stays under a uniform element bound. -/
theorem foldl_max_le (ys : List Nat) (y N : Nat)
    (hy : y ≤ N) (h : ∀ a ∈ ys, a ≤ N) :
    List.foldl max y ys ≤ N := by
  induction ys generalizing y with
  | nil => simp only [List.foldl]; exact hy
  | cons z zs ih =>
    simp only [List.foldl]
    apply ih
    · exact Nat.max_le.mpr ⟨hy, h z (List.mem_cons.mpr (Or.inl rfl))⟩
    · intro a ha
      exact h a (List.mem_cons.mpr (Or.inr ha))

/-- A recorded maximum is bounded by a uniform element bound. -/
theorem maxD_le_of_mem_bound (us : List Nat) (N : Nat)
    (h : ∀ a ∈ us, a ≤ N) : us.max?.getD 0 ≤ N := by
  cases us with
  | nil => simp [List.max?]
  | cons y ys =>
    simp only [List.max?, Option.getD_some]
    exact foldl_max_le ys y N (h y (List.mem_cons_self ..))
      (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))

/-- First use never exceeds last use, for every recorded triple. -/
theorem useFacts_fst_le_last (lines : List String) (e : String × Nat × Nat)
    (h : e ∈ useFacts lines) : e.2.1 ≤ e.2.2 := by
  simp only [useFacts] at h
  rw [List.mem_map] at h
  obtain ⟨⟨nm, ssa, dl⟩, _, rfl⟩ := h
  split
  · next t ht => exact minD_le_maxD _
  · exact Nat.le_refl _

/-- Every recorded last-use line is a real line of the scanned text. -/
theorem useFacts_last_bound (lines : List String) (e : String × Nat × Nat)
    (h : e ∈ useFacts lines) : e.2.2 ≤ lines.length := by
  simp only [useFacts] at h
  rw [List.mem_map] at h
  obtain ⟨⟨nm, ssa, dl⟩, _, rfl⟩ := h
  split
  · next t ht =>
    exact maxD_le_of_mem_bound _ _
      (fun a ha => rootUses_mem_bound _ _ _ _ _ _ ha)
  · simp

