/-
Circe.Emit.Match — `matchFrag`: recognition of the admitted `Func`
shapes.

Sits after all fragment modules (it pattern-matches on every canonical
shape) with one `rfl` linkage theorem per shape. `emitFunc`/`emitSpec`
(in `Circe.Emit`) dispatch on exactly this function.
-/
import Circe.Emit.Fragment
import Circe.Emit.Add
import Circe.Emit.Choose
import Circe.Emit.Sum
import Circe.Emit.Vec
import Circe.Emit.Vec64
import Circe.Emit.Vec2
import Circe.Emit.VecRealloc
import Circe.Emit.Calls
import Circe.Emit.Struct
import Circe.Emit.Flow

/-- Recognize the admitted `Func` shapes. Anything else is `none`
    (and `emitFunc` rejects it loudly).

    Contract: everything semantically relevant is pinned (param names,
    types relevant to evaluation, borrow-region equality for `choose`,
    exact bodies including the `1`/`0` literals). Ignored fields (function
    name, return type, `let_` annotations, static array bounds, borrow
    region numbers up to single-region equality) are semantically inert:
    `Eval` never inspects them. The pipeline only feeds validator-produced
    canonical `Func`s; per-shape generalized `emit_correct` proofs are
    future work. -/
def matchFrag : Func → Option FragKind
  | ⟨_, [⟨"a", .i 32, .owned⟩, ⟨"b", .i 32, .owned⟩], _,
      .return_ (.add (.var "a") (.var "b"))⟩ => some .add
  | ⟨_, [⟨"a", .i 64, .owned⟩, ⟨"b", .i 64, .owned⟩], _,
      .return_ (.add (.var "a") (.var "b"))⟩ => some .add64
  | ⟨_, [⟨"a", .u 64, .owned⟩, ⟨"b", .u 64, .owned⟩], _,
      .return_ (.uadd (.var "a") (.var "b"))⟩ => some .addu64
  | ⟨_, [⟨"p", .i 32, .mutBorrow _⟩], _,
      .return_ (.add (.var "p") (.lit (.i32 one)))⟩ =>
    if one == 1 then some .incr else none
  | ⟨_, [⟨"b", .bool, .owned⟩, ⟨"x", .i 32, .mutBorrow r1⟩,
         ⟨"y", .i 32, .mutBorrow r2⟩], _,
      .if_ (.var "b") (.return_ (.var "x")) (.return_ (.var "y"))⟩ =>
    if r1 == r2 then some .choose else none
  | ⟨_, [⟨"a", .array (.u 32) _, .sharedBorrow⟩,
         ⟨"n", .u 32, .owned⟩], _,
      .seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.assign "s" (.uadd (.var "s") (.idx "a" (.var "i"))))
                    (.assign "i" (.uadd (.var "i") (.lit (.u32 one))))))
            (.return_ (.var "s"))))⟩ =>
    if s0 == 0 && i0 == 0 && one == 1 then some .sum else none
  | ⟨_, [⟨"n", .u 32, .owned⟩], _,
      .seq (.let_ "v" _ (.vnew (.var "n")))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "j" _ (.lit (.u32 j0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.vset "v" (.var "i") (.var "i"))
                    (.assign "i" (.uadd (.var "i") (.lit (.u32 one1))))))
      (.seq (.while_ (.ult (.var "j") (.var "n"))
              (.seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "j"))))
                    (.assign "j" (.uadd (.var "j") (.lit (.u32 one2))))))
      (.seq (.vfree "v")
            (.return_ (.var "s"))))))))⟩ =>
    if i0 == 0 && s0 == 0 && j0 == 0 && one1 == 1 && one2 == 1 then
      some .vec
    else none
  | ⟨_, [⟨"n", .u 64, .owned⟩], _,
      .seq (.let_ "v" _ (.vnew (.var "n")))
      (.seq (.let_ "i" _ (.lit (.u64 i0)))
      (.seq (.let_ "s" _ (.lit (.u64 s0)))
      (.seq (.let_ "j" _ (.lit (.u64 j0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.vset "v" (.var "i") (.var "i"))
                    (.assign "i" (.uadd (.var "i") (.lit (.u64 one1))))))
      (.seq (.while_ (.ult (.var "j") (.var "n"))
              (.seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "j"))))
                    (.assign "j" (.uadd (.var "j") (.lit (.u64 one2))))))
      (.seq (.vfree "v")
            (.return_ (.var "s"))))))))⟩ =>
    if i0 == 0 && s0 == 0 && j0 == 0 && one1 == 1 && one2 == 1 then
      some .vec64
    else none
  | ⟨_, [⟨"n", .u 32, .owned⟩], _,
      .seq (.let_ "a" _ (.vnew (.var "n")))
      (.seq (.let_ "b" _ (.vnew (.var "n")))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.let_ "j" _ (.lit (.u32 j0)))
      (.seq (.let_ "k" _ (.lit (.u32 k0)))
      (.seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.vset "a" (.var "i") (.var "i"))
                    (.assign "i" (.uadd (.var "i") (.lit (.u32 one1))))))
      (.seq (.while_ (.ult (.var "j") (.var "n"))
              (.seq (.vset "b" (.var "j") (.vget "a" (.var "j")))
                    (.assign "j" (.uadd (.var "j") (.lit (.u32 one2))))))
      (.seq (.while_ (.ult (.var "k") (.var "n"))
              (.seq (.assign "s" (.uadd (.var "s") (.vget "b" (.var "k"))))
                    (.assign "k" (.uadd (.var "k") (.lit (.u32 one3))))))
      (.seq (.vfree "a")
      (.seq (.vfree "b")
            (.return_ (.var "s"))))))))))))⟩ =>
    if i0 == 0 && j0 == 0 && k0 == 0 && s0 == 0 &&
        one1 == 1 && one2 == 1 && one3 == 1 then
      some .vec2
    else none
  | ⟨_, [⟨"n", .u 32, .owned⟩], _,
      .seq (.let_ "v" _ (.vnew (.var "n")))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.let_ "m" _ (.uadd (.var "n") (.var "n")))
      (.seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "j" _ (.var "n"))
      (.seq (.let_ "k" _ (.lit (.u32 k0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.vset "v" (.var "i") (.var "i"))
                    (.assign "i" (.uadd (.var "i") (.lit (.u32 one1))))))
      (.seq (.vrealloc "v" (.var "m"))
      (.seq (.while_ (.ult (.var "j") (.var "m"))
              (.seq (.vset "v" (.var "j") (.var "j"))
                    (.assign "j" (.uadd (.var "j") (.lit (.u32 one2))))))
      (.seq (.while_ (.ult (.var "k") (.var "m"))
              (.seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "k"))))
                    (.assign "k" (.uadd (.var "k") (.lit (.u32 one3))))))
      (.seq (.vfree "v")
            (.return_ (.var "s"))))))))))))⟩ =>
    if i0 == 0 && s0 == 0 && k0 == 0 &&
        one1 == 1 && one2 == 1 && one3 == 1 then
      some .vecRealloc
    else none
  | ⟨_, [⟨"x", .i 32, .owned⟩, ⟨"y", .i 32, .owned⟩,
         ⟨"z", .i 32, .owned⟩], _, body⟩ =>
    -- Body matched separately: list-literal patterns (`["x", "y"]`)
    -- nested inside a `⟨⟩` Func pattern hit a Lean parser quirk
    -- (unexpected `)`); matching `body` at `CStmt` level parses fine.
    match body with
    | .seq (.callRet "t" "add" ["x", "y"])
        (.seq (.callRet "r" "add" ["t", "z"])
              (.return_ (.var "r"))) => some .addCall
    | _ => none
  | ⟨_, [⟨"a", .array (.u 32) _, .sharedBorrow⟩,
         ⟨"n", .u 32, .owned⟩], _, body⟩ =>
    match body with
    | .seq (.callRet "s" "sum_array" ["a", "n"])
        (.return_ (.var "s")) => some .sumCall
    | _ => none
  | ⟨_, [⟨"p", .struct "Point" _, .owned⟩,
         ⟨"dx", .i 32, .owned⟩, ⟨"dy", .i 32, .owned⟩], _,
      .seq (.let_ "qx" _ (.add (.fget "p" "x") (.var "dx")))
      (.seq (.let_ "qy" _ (.add (.fget "p" "y") (.var "dy")))
            (.return_ (.pmk (.var "qx") (.var "qy"))))⟩ =>
    some .translate
  | ⟨_, [⟨"n", .u 32, .owned⟩, ⟨"m", .u 32, .owned⟩], _, body⟩ =>
    -- Nested loop bodies matched separately: deeply-nested `.seq`
    -- patterns inside `⟨⟩` Func patterns hit the same equation-compiler
    -- quirk as S1 list literals (cf. `addCall` note).
    match body with
    | .seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.let_ "j" _ (.lit (.u32 j0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.while_ (.ult (.var "j") (.var "m"))
                      (.seq (.assign "s" (.uadd (.var "s")
                        (.umul (.var "i") (.var "j"))))
                            (.assign "j" (.uadd (.var "j")
                              (.lit (.u32 one1))))))
                    (.seq (.assign "i" (.uadd (.var "i")
                            (.lit (.u32 one2))))
                          (.assign "j" (.lit (.u32 z0))))))
            (.return_ (.var "s"))))) =>
      if s0 == 0 && i0 == 0 && j0 == 0 && one1 == 1 && one2 == 1 && z0 == 0 then
        some .nested
      else none
    | _ => none
  | ⟨_, [⟨"n", .u 32, .owned⟩], _, body⟩ =>
    match body with
    | .seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.if_ (.ueq (.var "i") (.lit (.u32 c2)))
                      (.seq (.assign "i" (.uadd (.var "i")
                              (.lit (.u32 one1)))) .continue_) .skip)
                    (.seq (.if_ (.ueq (.var "i") (.lit (.u32 c8)))
                              .break_ .skip)
                          (.seq (.assign "s" (.uadd (.var "s") (.var "i")))
                                (.assign "i" (.uadd (.var "i")
                                  (.lit (.u32 one2))))))))
            (.return_ (.var "s")))) =>
      if s0 == 0 && i0 == 0 && c2 == 2 && c8 == 8 && one1 == 1 && one2 == 1 then
        some .skip
      else none
    | _ => none
  | ⟨_, [⟨"a", .array (.u 32) _, .sharedBorrow⟩,
         ⟨"n", .u 32, .owned⟩, ⟨"k", .u 32, .owned⟩], _, body⟩ =>
    -- Three-param shape: body matched separately (cf. `addCall` note).
    match body with
    | .seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.if_ (.ueq (.idx "a" (.var "i")) (.var "k"))
                      (.return_ (.var "i")) .skip)
                    (.assign "i" (.uadd (.var "i")
                      (.lit (.u32 one))))))
            (.return_ (.var "n"))) =>
      if i0 == 0 && one == 1 then some .findEq else none
    | _ => none
  | ⟨_, [⟨"x", .u 32, .owned⟩], _, body⟩ =>
    match body with
    | .if_ (.ueq (.var "x") (.lit (.u32 c0)))
        (.return_ (.lit (.u32 r0)))
        (.if_ (.ueq (.var "x") (.lit (.u32 c1)))
              (.return_ (.lit (.u32 r1)))
              (.return_ (.lit (.u32 r2)))) =>
      if c0 == 0 && c1 == 1 && r0 == 10 && r1 == 20 && r2 == 30 then
        some .cls
      else none
    | _ => none
  | _ => none

theorem matchFrag_add : matchFrag addFunc = some .add := rfl
theorem matchFrag_incr : matchFrag incrFunc = some .incr := rfl
theorem matchFrag_add64 : matchFrag add64Func = some .add64 := rfl
theorem matchFrag_addu64 : matchFrag addu64Func = some .addu64 := rfl
theorem matchFrag_choose : matchFrag chooseFunc = some .choose := rfl
theorem matchFrag_sum : matchFrag sumFunc = some .sum := rfl
theorem matchFrag_vec : matchFrag vecFunc = some .vec := rfl
theorem matchFrag_vec64 : matchFrag vec64Func = some .vec64 := rfl
theorem matchFrag_vec2 : matchFrag vec2Func = some .vec2 := rfl
theorem matchFrag_vecRealloc : matchFrag vecReallocFunc = some .vecRealloc := rfl
theorem matchFrag_addCaller : matchFrag addCallerFunc = some .addCall := rfl
theorem matchFrag_sumCaller : matchFrag sumCallerFunc = some .sumCall := rfl
theorem matchFrag_translate : matchFrag translateFunc = some .translate := rfl
theorem matchFrag_nested : matchFrag nestedFunc = some .nested := rfl
theorem matchFrag_skip : matchFrag skipFunc = some .skip := rfl
theorem matchFrag_findEq : matchFrag findEqFunc = some .findEq := rfl
theorem matchFrag_cls : matchFrag clsFunc = some .cls := rfl
