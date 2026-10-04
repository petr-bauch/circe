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
import Circe.Emit.Method
import Circe.Emit.Acc
import Circe.Emit.Move
import Circe.Emit.Array
import Circe.Emit.Optional
import Circe.Emit.Span
import Circe.Emit.VecRead
import Circe.Emit.Box
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
  | ⟨_, [⟨"a", .i 32, .owned⟩, ⟨"b", .i 32, .owned⟩,
         ⟨"c", .i 32, .owned⟩], _, body⟩ =>
    -- `let_`-bound SSA temporary: body matched separately (cf.
    -- `addCall` note).
    match body with
    | .seq (.let_ "t" _ (.add (.var "a") (.var "b")))
        (.return_ (.add (.var "t") (.var "c"))) => some .add3
    | _ => none
  | ⟨_, [⟨"x", .i 32, .owned⟩, ⟨"y", .i 32, .owned⟩], _, body⟩ =>
    -- Mangled callees: body matched separately (cf. `addCall` note).
    match body with
    | .seq (.callRet "s" "_Z3addii" ["x", "y"])
        (.return_ (.var "s")) => some .useAdd
    | .seq (.callRet "s" "_ZN2ns3addEii" ["x", "y"])
        (.return_ (.var "s")) => some .useNsAdd
    | .seq (.callRet "s" "_Z4taddIiET_S0_S0_" ["x", "y"])
        (.return_ (.var "s")) => some .useTadd32
    | _ => none
  | ⟨_, [⟨"x", .i 64, .owned⟩, ⟨"y", .i 64, .owned⟩], _, body⟩ =>
    -- 64-bit instantiation callee: body matched separately (cf.
    -- `addCall` note).
    match body with
    | .seq (.callRet "s" "_Z4taddIlET_S0_S0_" ["x", "y"])
        (.return_ (.var "s")) => some .useTadd64
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
  | ⟨_, [⟨"this", .struct "Point" _, .owned⟩], _,
      .return_ (.add (.fget "this" "x") (.fget "this" "y"))⟩ =>
    some .methodSum
  | ⟨_, [⟨"p", .struct "Point" _, .owned⟩], _, body⟩ =>
    -- Mangled callee + list literal: body matched separately (cf.
    -- `addCall` note).
    match body with
    | .seq (.callRet "s" "_ZNK5Point3sumEv" ["p"])
        (.return_ (.var "s")) => some .pointSumRef
    | _ => none
  | ⟨_, [], _, .return_ (.lit (.i32 z))⟩ =>
    if z == 0 then some .accCtor else none
  | ⟨_, [⟨"s", .i 32, .owned⟩, ⟨"v", .i 32, .owned⟩], _,
      .return_ (.add (.var "s") (.var "v"))⟩ =>
    some .accAdd
  | ⟨_, [⟨"s", .i 32, .owned⟩], _, .return_ (.var "s")⟩ =>
    some .accGet
  | ⟨_, [⟨"t", .i 32, .owned⟩], _, .return_ (.var "t")⟩ =>
    some .accDtor
  | ⟨_, [⟨"d", .i 32, .owned⟩, ⟨"s", .i 32, .owned⟩], _,
      .return_ (.var "s")⟩ =>
    some .accMoveCtor
  | ⟨_, [⟨"a", .i 32, .owned⟩, ⟨"b", .i 32, .owned⟩], _, .cleanup body⟩ =>
    -- Mangled callees + list literals + `cleanup` wrapper: body matched
    -- separately (cf. `addCall` note).
    match body with
    | .seq (.callRet "s0" "_ZN3AccC2Ev" [])
      (.seq (.callRet "s1" "_ZN3Acc3addEi" ["s0", "a"])
      (.seq (.callRet "s2" "_ZN3Acc3addEi" ["s1", "b"])
      (.seq (.callRet "s3" "_ZNK3Acc3getEv" ["s2"])
      (.seq (.callRet "u" "_ZN3AccD2Ev" ["s3"])
            (.return_ (.var "s3")))))) => some .accTwo
    | .seq (.callRet "s0" "_ZN3AccC2Ev" [])
      (.seq (.callRet "s1" "_ZN3Acc3addEi" ["s0", "a"])
      (.seq (.callRet "d1" "_ZN3AccC2EOS_" ["s0", "s1"])
      (.seq (.assign "s1" (.lit (.i32 0)))
      (.seq (.callRet "d2" "_ZN3Acc3addEi" ["d1", "b"])
      (.seq (.callRet "r" "_ZNK3Acc3getEv" ["d2"])
      (.seq (.callRet "u1" "_ZN3AccD2Ev" ["r"])
      (.seq (.callRet "u2" "_ZN3AccD2Ev" ["s1"])
            (.return_ (.var "r"))))))))) => some .moveAcc
    | .seq (.callRet "s0" "_ZN3AccC2Ev" [])
      (.seq (.callRet "s1" "_ZN3Acc3addEi" ["s0", "a"])
      (.seq (.if_ (.ueq (.var "a") (.var "b"))
              (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
                    (.return_ (.var "r1")))
              .skip)
      (.seq (.callRet "s2" "_ZN3Acc3addEi" ["s1", "b"])
      (.seq (.callRet "r" "_ZNK3Acc3getEv" ["s2"])
      (.seq (.callRet "u" "_ZN3AccD2Ev" ["r"])
            (.return_ (.var "r"))))))) => some .scopeEarly
    | _ => none
  | ⟨_, [⟨"x", .i 32, .owned⟩], _, body⟩ =>
    -- `let_`/`boxFree` chain: body matched separately (nested `.seq`
    -- patterns inside `⟨⟩` hit the parser quirk, cf. `addCall` note).
    match body with
    | .seq (.let_ "p" _ (.boxNew (.var "x")))
      (.seq (.let_ "r" _ (.boxGet "p"))
      (.seq (.boxFree "p")
            (.return_ (.var "r")))) => some .boxThrough
    | _ => none
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
  | ⟨_, [⟨"t", .array (.i 32) 4, .sharedBorrow⟩,
         ⟨"n", .u 64, .owned⟩], _,
      .return_ (.idxi "t" (.var "n"))⟩ =>
    some .arrayRef
  | ⟨_, [⟨"a", .array (.i 32) 4, .sharedBorrow⟩,
         ⟨"n", .u 64, .owned⟩], _,
      .return_ (.idxi "a" (.var "n"))⟩ =>
    some .arrayAt
  | ⟨_, [⟨"a", .array (.i 32) 4, .sharedBorrow⟩], _, body⟩ =>
    -- 8-deep `.seq` chain: body matched separately (nested `.seq`
    -- patterns inside `⟨⟩` hit the parser quirk, cf. `addCall` note).
    match body with
    | .seq (.let_ "i0" _ (.lit (.u64 l0)))
      (.seq (.callRet "e0" "_ZNKSt5arrayIiLm4EEixEm" ["a", "i0"])
      (.seq (.let_ "i1" _ (.lit (.u64 l1)))
      (.seq (.callRet "e1" "_ZNKSt5arrayIiLm4EEixEm" ["a", "i1"])
      (.seq (.let_ "i2" _ (.lit (.u64 l2)))
      (.seq (.callRet "e2" "_ZNKSt5arrayIiLm4EEixEm" ["a", "i2"])
      (.seq (.let_ "i3" _ (.lit (.u64 l3)))
      (.seq (.callRet "e3" "_ZNKSt5arrayIiLm4EEixEm" ["a", "i3"])
             (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
               (.var "e2")) (.var "e3")))))))))) =>
      if l0 == 0 && l1 == 1 && l2 == 2 && l3 == 3 then
        some .arraySum
      else none
    | _ => none
  | ⟨_, [⟨"b", .struct "std::optional<int>" [.i 32, .bool],
         .sharedBorrow⟩], _,
      .return_ (.optHas "b")⟩ =>
    some .optHas
  | ⟨_, [⟨"o", .struct "std::optional<int>" [.i 32, .bool],
         .sharedBorrow⟩], _,
      .return_ (.optHas "o")⟩ =>
    some .optHasValue
  | ⟨_, [⟨"p", .struct "std::optional<int>" [.i 32, .bool],
         .sharedBorrow⟩], _,
      .return_ (.optGet "p")⟩ =>
    some .optGet
  | ⟨_, [⟨"o", .struct "std::optional<int>" [.i 32, .bool],
         .sharedBorrow⟩], _,
      .return_ (.optGet "o")⟩ =>
    some .optDerefOp
  | ⟨_, [⟨"o", .struct "std::optional<int>" [.i 32, .bool],
         .sharedBorrow⟩], _, body⟩ =>
    -- Two prog shapes share the `[o]` params: matched on the body
    -- (nested `.seq`/`.if_` patterns inside `⟨⟩` hit the parser
    -- quirk, cf. the `arraySum` note above).
    match body with
    | .seq (.callRet "r"
        "_ZNKSt22_Optional_payload_baseIiE6_M_getEv" ["o"])
        (.return_ (.var "r")) =>
      some .optImplGet
    | .seq (.callRet "h" "_ZNKSt8optionalIiE9has_valueEv" ["o"])
        (.if_ (.var "h")
          (.seq (.callRet "v" "_ZNKRSt8optionalIiEdeEv" ["o"])
                (.return_ (.var "v")))
          (.return_ (.lit (.i32 neg1)))) =>
      if neg1 == (-1 : BitVec 32) then some .optDeref else none
    | _ => none
  | ⟨_, [⟨"e", .struct "std::__detail::__extent_storage" [.u 64],
         .sharedBorrow⟩], _,
      .return_ (.spanLen "e")⟩ =>
    some .spanExtent
  | ⟨_, [⟨"s", .struct "std::span<const int>" [.u 64, .u 64],
         .sharedBorrow⟩], _,
      .return_ (.spanLen "s")⟩ =>
    some .spanSize
  | ⟨_, [⟨"s", .struct "std::span<const int>" [.u 64, .u 64],
         .sharedBorrow⟩,
        ⟨"n", .u 64, .owned⟩], _,
      .return_ (.spanAt "s" (.var "n"))⟩ =>
    some .spanIndex
  | ⟨_, [⟨"s", .struct "std::span<const int>" [.u 64, .u 64],
         .sharedBorrow⟩], _, body⟩ =>
    -- The entry body nests three `.seq` plus the `while_` loop:
    -- matched on the body outside `⟨⟩` (cf. the `optDeref` quirk
    -- note above).
    match body with
    | .seq (.let_ "t" (.i 32) (.lit (.i32 t0)))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 i0)))
      (.seq (.while_ (.ult (.var "i") (.spanLen "s"))
              (.seq (.assign "t"
                      (.add (.var "t") (.spanAt "s" (.var "i"))))
                (.assign "i"
                  (.uadd (.var "i") (.lit (.u64 one))))))
            (.return_ (.var "t")))) =>
      if t0 == BitVec.ofNat 32 0 && i0 == BitVec.ofNat 64 0 &&
          one == BitVec.ofNat 64 1 then some .spanSum else none
    | _ => none
  | ⟨_, [⟨"s", .struct "std::vector<int>" [.u 64, .u 64, .u 64],
         .sharedBorrow⟩], _,
      .return_ (.stdVecLen "s")⟩ =>
    some .vecSize
  | ⟨_, [⟨"s", .struct "std::vector<int>" [.u 64, .u 64, .u 64],
         .sharedBorrow⟩,
        ⟨"n", .u 64, .owned⟩], _,
      .return_ (.stdVecAt "s" (.var "n"))⟩ =>
    some .vecIndex
  | ⟨_, [⟨"s", .struct "std::vector<int>" [.u 64, .u 64, .u 64],
         .sharedBorrow⟩], _, body⟩ =>
    match body with
    | .seq (.let_ "t" (.i 32) (.lit (.i32 t0)))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 i0)))
      (.seq (.while_ (.ult (.var "i") (.stdVecLen "s"))
              (.seq (.assign "t"
                      (.add (.var "t") (.stdVecAt "s" (.var "i"))))
                (.assign "i"
                  (.uadd (.var "i") (.lit (.u64 one))))))
            (.return_ (.var "t")))) =>
      if t0 == BitVec.ofNat 32 0 && i0 == BitVec.ofNat 64 0 &&
          one == BitVec.ofNat 64 1 then some .vecReadSum else none
    | _ => none
  | _ => none

theorem matchFrag_add : matchFrag addFunc = some .add := rfl
theorem matchFrag_add3 : matchFrag add3Func = some .add3 := rfl
theorem matchFrag_useAdd : matchFrag useAddFunc = some .useAdd := rfl
theorem matchFrag_useNsAdd : matchFrag useNsAddFunc = some .useNsAdd := rfl
theorem matchFrag_useTadd32 : matchFrag useTadd32Func = some .useTadd32 := rfl
theorem matchFrag_useTadd64 : matchFrag useTadd64Func = some .useTadd64 := rfl
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
theorem matchFrag_methodSum : matchFrag methodSumFunc = some .methodSum := rfl
theorem matchFrag_pointSumRef : matchFrag pointSumRefFunc = some .pointSumRef := rfl
theorem matchFrag_accCtor : matchFrag accCtorFunc = some .accCtor := rfl
theorem matchFrag_accAdd : matchFrag accAddFunc = some .accAdd := rfl
theorem matchFrag_accGet : matchFrag accGetFunc = some .accGet := rfl
theorem matchFrag_accDtor : matchFrag accDtorFunc = some .accDtor := rfl
theorem matchFrag_accTwo : matchFrag accTwoFunc = some .accTwo := rfl
theorem matchFrag_accMoveCtor : matchFrag accMoveCtorFunc = some .accMoveCtor := rfl
theorem matchFrag_moveAcc : matchFrag moveAccFunc = some .moveAcc := rfl
theorem matchFrag_scopeEarly : matchFrag scopeEarlyFunc = some .scopeEarly := rfl
theorem matchFrag_boxThrough : matchFrag boxThroughFunc = some .boxThrough := rfl
theorem matchFrag_nested : matchFrag nestedFunc = some .nested := rfl
theorem matchFrag_skip : matchFrag skipFunc = some .skip := rfl
theorem matchFrag_findEq : matchFrag findEqFunc = some .findEq := rfl
theorem matchFrag_cls : matchFrag clsFunc = some .cls := rfl
theorem matchFrag_arrayRef : matchFrag arrayRefFunc = some .arrayRef := rfl
theorem matchFrag_arrayAt : matchFrag arrayAtFunc = some .arrayAt := rfl
theorem matchFrag_arraySum : matchFrag arraySumFunc = some .arraySum := rfl
theorem matchFrag_optHas : matchFrag optHasFunc = some .optHas := rfl
theorem matchFrag_optHasValue : matchFrag optHasValueFunc = some .optHasValue := rfl
theorem matchFrag_optGet : matchFrag optGetFunc = some .optGet := rfl
theorem matchFrag_optDerefOp : matchFrag optDerefOpFunc = some .optDerefOp := rfl
theorem matchFrag_optImplGet : matchFrag optImplGetFunc = some .optImplGet := rfl
theorem matchFrag_optDeref : matchFrag optDerefFunc = some .optDeref := rfl
theorem matchFrag_spanExtent : matchFrag spanExtentFunc = some .spanExtent := rfl
theorem matchFrag_spanSize : matchFrag spanSizeFunc = some .spanSize := rfl
theorem matchFrag_spanIndex : matchFrag spanIndexFunc = some .spanIndex := rfl
theorem matchFrag_spanSum : matchFrag spanSumFunc = some .spanSum := rfl
theorem matchFrag_stdVecSize : matchFrag stdVecSizeFunc = some .vecSize := rfl
theorem matchFrag_stdVecIndex : matchFrag stdVecIndexFunc = some .vecIndex := rfl
theorem matchFrag_stdVecReadSum : matchFrag stdVecReadSumFunc = some .vecReadSum := rfl
