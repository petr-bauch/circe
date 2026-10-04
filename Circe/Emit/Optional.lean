/-
Circe.Emit.Optional — N4d-ii `std::optional<int32_t>` guarded `operator*`:
the `_M_is_engaged` engaged-bit leaf + payload `_M_get` leaf +
`has_value` / impl `_M_get` single-delegation entries + the fused
`operator*` leaf + the `opt_deref` guarded-deref entry.

The C++ call chain is depth-3 (`opt_deref` → `operator*` →
impl `_M_get` → payload `_M_get`) but `evalProgStmt` dispatches
callees via `evalFuncFuel`, which only evaluates call-free bodies
(the S1 DAG discipline). So functionalization fuses edges, exactly
like the N4d-i leaf fusions (`arrayAtFunc` fuses `operator[]` →
`_S_ref`): `has_value` fuses the `base_class_addr [0]` projection +
`_M_is_engaged` call into the `optHas` read; `operator*` fuses
`operator*` → impl `_M_get` → payload `_M_get` plus the caller-side
load into the `optGet` read. `has_value` still validates separately
to `optHasValueFunc` (same value story as `_M_is_engaged`), and
impl `_M_get` still validates separately to `optImplGetFunc`
(delegation over the payload leaf), so misshapen variants of every
def reject loudly.

The impl `_M_get` assert scope (`cir.ternary` over a `false` const +
one-sided `cir.if` + `cir.unreachable` in a do-while-false scope, the
disabled-`__glibcxx_assert` skeleton — cf. `__glibcxx_assert` in
`bits/c++config.h`, which without `_GLIBCXX_ASSERTIONS` is just
`do { ... } while (false)`) is dead code: the ternary condition is
the literal `false`, so the `_M_is_engaged` call in the untaken arm
never evaluates and the `unreachable` never fires. It is dropped
from `optImplGetFunc`; the gate (`isOptImplGetShape`) pins the dead
skeleton textually, so a live-assert variant (e.g. compiled with
`_GLIBCXX_ASSERTIONS`) rejects loudly instead of being silently
modeled. The stray dead `cir.const 1` in `opt_deref` is likewise
dropped and pinned by the gate's const count.
-/
import Circe.Emit.Fragment

/-! ## N4d-ii: `std::optional` engaged-bit leaf, payload leaf, entries -/

/-- The 2-word `std::optional<int32_t>` object model: the payload word
    plus the engaged bit (padding, the storage union, and the
    base/derived `[0]` projections all erase). -/
def optObjTy : CType := .struct "std::optional<int>" [.i 32, .bool]

/-- Mangled callee names in `tests/cpp/opt_deref.cpp`. -/
def optHasName : String :=
  "_ZNKSt19_Optional_base_implIiSt14_Optional_baseIiLb1ELb1EEE13_M_is_engagedEv"
def optGetName : String :=
  "_ZNKSt22_Optional_payload_baseIiE6_M_getEv"
def optImplGetName : String :=
  "_ZNKSt19_Optional_base_implIiSt14_Optional_baseIiLb1ELb1EEE6_M_getEv"
def optHasValueName : String := "_ZNKSt8optionalIiE9has_valueEv"
def optDerefOpName : String := "_ZNKRSt8optionalIiEdeEv"
def optDerefName : String := "_Z9opt_derefRKSt8optionalIiE"

/-- Canonical CoreIR for `_M_is_engaged`: the `_M_engaged` bit load
    (`derived [0]` + `get_member [0]` + `base [0]` + `get_member [1]`
    projections fused) as the `optHas` read. -/
def optHasFunc : Func :=
  ⟨optHasName,
   [{ name := "b", ty := optObjTy, role := .sharedBorrow }],
   .bool,
   .return_ (.optHas "b")⟩

/-- Canonical CoreIR for `has_value`: the `base_class_addr [0]`
    projection + `_M_is_engaged` call fused into the `optHas` read
    (cf. `arrayAtFunc`). -/
def optHasValueFunc : Func :=
  ⟨optHasValueName,
   [{ name := "o", ty := optObjTy, role := .sharedBorrow }],
   .bool,
   .return_ (.optHas "o")⟩

/-- Canonical CoreIR for payload `_M_get`: the `_M_payload [0]` +
    `_M_value [1]` projections and the retval load fused into the
    `optGet` read (disengaged is `AssertFail`; the payload word of a
    disengaged optional is unobservable when guarded). -/
def optGetFunc : Func :=
  ⟨optGetName,
   [{ name := "p", ty := optObjTy, role := .sharedBorrow }],
   .i 32,
   .return_ (.optGet "p")⟩

/-- Canonical CoreIR for impl `_M_get`: pure delegation to payload
    `_M_get` (the dead assert scope is dropped, cf. the module
    docstring; the caller-side pointer load is fused downstream). -/
def optImplGetFunc : Func :=
  ⟨optImplGetName,
   [{ name := "o", ty := optObjTy, role := .sharedBorrow }],
   .i 32,
   .seq (.callRet "r" optGetName ["o"])
        (.return_ (.var "r"))⟩

/-- Canonical CoreIR for `operator*`: the `base_class_addr [0]` +
    impl `_M_get` call + caller-side load fused into the `optGet`
    read (two edges fused; impl `_M_get` still validates separately
    as `optImplGetFunc` with the same value story). -/
def optDerefOpFunc : Func :=
  ⟨optDerefOpName,
   [{ name := "o", ty := optObjTy, role := .sharedBorrow }],
   .i 32,
   .return_ (.optGet "o")⟩

/-- Canonical CoreIR for `opt_deref`: the `has_value` call, the
    engaged branch (deref call + return, the pointer load fused into
    the callee), and the `-1` sentinel on disengaged (the dead
    `const 1` is dropped). -/
def optDerefFunc : Func :=
  ⟨optDerefName,
   [{ name := "o", ty := optObjTy, role := .sharedBorrow }],
   .i 32,
   .seq (.callRet "h" optHasValueName ["o"])
   (.if_ (.var "h")
     (.seq (.callRet "v" optDerefOpName ["o"])
           (.return_ (.var "v")))
     (.return_ (.lit (.i32 (-1 : BitVec 32)))))⟩

/-- Program over which the `opt_deref` entry evaluates (both callees
    are call-free leaves). -/
abbrev optDerefProg : Prog := [optHasValueFunc, optDerefOpFunc]

/-- Value-level forward for `_M_is_engaged`: the engaged bit. -/
def optHasFwd (v : Option (BitVec 32)) : Result Value :=
  .ok (.b v.isSome)

/-- Value-level forward for `has_value`: the same read (the call edge
    is fused, so the forward is the leaf forward by definition). -/
def optHasValueFwd (v : Option (BitVec 32)) : Result Value :=
  optHasFwd v

theorem optHasValueFwd_is_call (v : Option (BitVec 32)) :
    optHasValueFwd v = optHasFwd v := rfl

/-- Value-level forward for payload `_M_get`: the payload word, or
    `AssertFail` when disengaged (the `unreachable` assert made
    loud). -/
def optGetFwd (v : Option (BitVec 32)) : Result Value :=
  match v with
  | some x => .ok (.i32 x)
  | none => .error .AssertFail

/-- Value-level forward for `operator*`: the same read (two call
    edges fused, so the forward is the leaf forward by definition). -/
def optDerefOpFwd (v : Option (BitVec 32)) : Result Value :=
  optGetFwd v

theorem optDerefOpFwd_is_call (v : Option (BitVec 32)) :
    optDerefOpFwd v = optGetFwd v := rfl

/-- Value-level forward for `opt_deref`: the payload word on engaged,
    the `-1` sentinel on disengaged. -/
def optDerefFwd (v : Option (BitVec 32)) : Result Value :=
  match v with
  | some x => .ok (.i32 x)
  | none => .ok (.i32 (-1 : BitVec 32))

/-- Env fact for the single-optional shapes (name-parametrized: the
    fused pairs share bodies but pin distinct param names, cf.
    `arrayRefFunc`/`arrayAtFunc` `t` vs `a`). -/
theorem envLookup_opt_o (nm : String) (v : Option (BitVec 32)) :
    envLookup [(nm, .optVal v)] nm = some (.optVal v) := by
  simp [envLookup]

/-- `emit_correct` for `_M_is_engaged` (engaged and disengaged). -/
theorem evalFuncFuel_optHas (F : Nat) (v : Option (BitVec 32)) :
    evalFuncFuel F optHasFunc [.optVal v] = optHasFwd v := by
  have hbind : bindArgs optHasFunc.args [.optVal v] =
      some [("b", .optVal v)] := rfl
  have hbody : optHasFunc.body = .return_ (.optHas "b") := rfl
  have ho := envLookup_opt_o "b" v
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, optHasFwd, ho]

/-- `emit_correct` for `has_value` (same read, fused call edge). -/
theorem evalFuncFuel_optHasValue (F : Nat) (v : Option (BitVec 32)) :
    evalFuncFuel F optHasValueFunc [.optVal v] = optHasValueFwd v := by
  have hbind : bindArgs optHasValueFunc.args [.optVal v] =
      some [("o", .optVal v)] := rfl
  have hbody : optHasValueFunc.body = .return_ (.optHas "o") := rfl
  have ho := envLookup_opt_o "o" v
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, optHasValueFwd, optHasFwd, ho]

/-- `emit_correct` for payload `_M_get` (payload word on engaged,
    `AssertFail` on disengaged). -/
theorem evalFuncFuel_optGet (F : Nat) (v : Option (BitVec 32)) :
    evalFuncFuel F optGetFunc [.optVal v] = optGetFwd v := by
  have hbind : bindArgs optGetFunc.args [.optVal v] =
      some [("p", .optVal v)] := rfl
  have hbody : optGetFunc.body = .return_ (.optGet "p") := rfl
  have ho := envLookup_opt_o "p" v
  cases v <;> cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, optGetFwd, ho]

/-- `emit_correct` for `operator*` (same read, fused call edges). -/
theorem evalFuncFuel_optDerefOp (F : Nat) (v : Option (BitVec 32)) :
    evalFuncFuel F optDerefOpFunc [.optVal v] = optDerefOpFwd v := by
  have hbind : bindArgs optDerefOpFunc.args [.optVal v] =
      some [("o", .optVal v)] := rfl
  have hbody : optDerefOpFunc.body = .return_ (.optGet "o") := rfl
  have ho := envLookup_opt_o "o" v
  cases v <;> cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, optDerefOpFwd, optGetFwd, ho]

/-- `emit_correct` for impl `_M_get`: program evaluation over the
    payload leaf agrees with the delegating forward (both the engaged
    word and the disengaged `AssertFail` propagate through the
    single `callRet`). -/
theorem evalProgFunc_optImplGet (F : Nat) (v : Option (BitVec 32)) :
    evalProgFunc [optGetFunc] F optImplGetFunc [.optVal v] =
      optGetFwd v := by
  have hbind : bindArgs optImplGetFunc.args [.optVal v] =
      some [("o", .optVal v)] := rfl
  have hbody : optImplGetFunc.body =
      .seq (.callRet "r" optGetName ["o"])
           (.return_ (.var "r")) := rfl
  have hfind : findFunc [optGetFunc] optGetName = some optGetFunc := rfl
  have hargs : lookupArgs [("o", .optVal v)] ["o"] =
      some [.optVal v] := rfl
  have hcall : evalFuncFuel F optGetFunc [.optVal v] = optGetFwd v :=
    evalFuncFuel_optGet F v
  cases hv : optGetFwd v with
  | error e =>
    have hcallE : evalFuncFuel F optGetFunc [.optVal v] = .error e := by
      rw [hcall, hv]
    have hstep := evalProgStmt_callRet_err [optGetFunc] F "r" optGetName
      ["o"] [("o", .optVal v)] [.optVal v] optGetFunc e hargs hfind hcallE
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstep]
  | ok w =>
    have hcallO : evalFuncFuel F optGetFunc [.optVal v] = .ok w := by
      rw [hcall, hv]
    have hstep := evalProgStmt_callRet_ok [optGetFunc] F "r" optGetName
      ["o"] [("o", .optVal v)] [.optVal v] optGetFunc w hargs hfind hcallO
    have hexpr : evalExpr (.var "r")
        (envExtend [("o", .optVal v)] "r" w) = .ok w := by
      simp [evalExpr, envExtend, envLookup]
    have hret := evalProgStmt_return [optGetFunc] F (.var "r")
      (envExtend [("o", .optVal v)] "r" w) w hexpr
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep, hret]

/-- `emit_correct` for `opt_deref`: program evaluation over the two
    leaves agrees with the sentinel forward (the engaged branch
    dereferences through `operator*`; the disengaged branch returns
    `-1`). -/
theorem evalProgFunc_optDeref (F : Nat) (v : Option (BitVec 32)) :
    evalProgFunc optDerefProg F optDerefFunc [.optVal v] =
      optDerefFwd v := by
  have hbind : bindArgs optDerefFunc.args [.optVal v] =
      some [("o", .optVal v)] := rfl
  have hbody : optDerefFunc.body =
      .seq (.callRet "h" optHasValueName ["o"])
      (.if_ (.var "h")
        (.seq (.callRet "v" optDerefOpName ["o"])
              (.return_ (.var "v")))
        (.return_ (.lit (.i32 (-1 : BitVec 32))))) := rfl
  have hfindH : findFunc optDerefProg optHasValueName =
      some optHasValueFunc := rfl
  have hfindD : findFunc optDerefProg optDerefOpName =
      some optDerefOpFunc := rfl
  have hargsH : lookupArgs [("o", .optVal v)] ["o"] =
      some [.optVal v] := rfl
  cases v with
  | none =>
    have hcallH : evalFuncFuel F optHasValueFunc [.optVal none] =
        .ok (.b false) := by
      rw [evalFuncFuel_optHasValue]
      rfl
    have hstepH := evalProgStmt_callRet_ok optDerefProg F "h"
      optHasValueName ["o"] [("o", .optVal none)] [.optVal none]
      optHasValueFunc (.b false) hargsH hfindH hcallH
    have hcondF : evalExpr (.var "h")
        (envExtend [("o", .optVal none)] "h" (.b false)) =
        .ok (.b false) := by
      simp [evalExpr, envExtend, envLookup]
    have hifF : evalProgStmt optDerefProg F
        (.if_ (.var "h")
          (.seq (.callRet "v" optDerefOpName ["o"])
                (.return_ (.var "v")))
          (.return_ (.lit (.i32 (-1 : BitVec 32)))))
        (envExtend [("o", .optVal none)] "h" (.b false)) =
        evalProgStmt optDerefProg F
          (.return_ (.lit (.i32 (-1 : BitVec 32))))
          (envExtend [("o", .optVal none)] "h" (.b false)) :=
      evalProgStmt_if_false _ _ _ _ _ _ hcondF
    have hexprE : evalExpr (.lit (.i32 (-1 : BitVec 32)))
        (envExtend [("o", .optVal none)] "h" (.b false)) =
        .ok (.i32 (-1 : BitVec 32)) := by
      simp [evalExpr, litVal]
    have helse := evalProgStmt_return optDerefProg F
      (.lit (.i32 (-1 : BitVec 32)))
      (envExtend [("o", .optVal none)] "h" (.b false))
      (.i32 (-1 : BitVec 32)) hexprE
    have hifF' : evalProgStmt optDerefProg F
        (.if_ (.var "h")
          (.seq (.callRet "v" optDerefOpName ["o"])
                (.return_ (.var "v")))
          (.return_ (.lit (.i32 (-1 : BitVec 32)))))
        (envExtend [("o", .optVal none)] "h" (.b false)) =
        .ok ((envExtend [("o", .optVal none)] "h" (.b false)),
          .returned (.i32 (-1 : BitVec 32))) :=
      Eq.trans hifF helse
    have hsum : optDerefFwd none = .ok (.i32 (-1 : BitVec 32)) := rfl
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepH, hifF']
    simp [hsum]
  | some x =>
    have hcallH : evalFuncFuel F optHasValueFunc [.optVal (some x)] =
        .ok (.b true) := by
      rw [evalFuncFuel_optHasValue]
      rfl
    have hstepH := evalProgStmt_callRet_ok optDerefProg F "h"
      optHasValueName ["o"] [("o", .optVal (some x))] [.optVal (some x)]
      optHasValueFunc (.b true) hargsH hfindH hcallH
    have hcondT : evalExpr (.var "h")
        (envExtend [("o", .optVal (some x))] "h" (.b true)) =
        .ok (.b true) := by
      simp [evalExpr, envExtend, envLookup]
    have hargsV : lookupArgs
        (envExtend [("o", .optVal (some x))] "h" (.b true)) ["o"] =
        some [.optVal (some x)] := by
      simp [lookupArgs, envExtend, envLookup,
        show ("o" : String) ≠ "h" by decide]
    have hcallV : evalFuncFuel F optDerefOpFunc [.optVal (some x)] =
        .ok (.i32 x) := by
      rw [evalFuncFuel_optDerefOp]
      rfl
    have hstepV := evalProgStmt_callRet_ok optDerefProg F "v"
      optDerefOpName ["o"]
      (envExtend [("o", .optVal (some x))] "h" (.b true))
      [.optVal (some x)] optDerefOpFunc (.i32 x)
      hargsV hfindD hcallV
    have hexprV : evalExpr (.var "v")
        (envExtend (envExtend [("o", .optVal (some x))] "h" (.b true))
          "v" (.i32 x)) = .ok (.i32 x) := by
      simp [evalExpr, envExtend, envLookup]
    have hretV := evalProgStmt_return optDerefProg F (.var "v")
      (envExtend (envExtend [("o", .optVal (some x))] "h" (.b true))
        "v" (.i32 x)) (.i32 x) hexprV
    have hthen : evalProgStmt optDerefProg F
        (.seq (.callRet "v" optDerefOpName ["o"])
              (.return_ (.var "v")))
        (envExtend [("o", .optVal (some x))] "h" (.b true)) =
        .ok ((envExtend (envExtend [("o", .optVal (some x))] "h" (.b true))
          "v" (.i32 x)), .returned (.i32 x)) :=
      Eq.trans (evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV) hretV
    have hifT : evalProgStmt optDerefProg F
        (.if_ (.var "h")
          (.seq (.callRet "v" optDerefOpName ["o"])
                (.return_ (.var "v")))
          (.return_ (.lit (.i32 (-1 : BitVec 32)))))
        (envExtend [("o", .optVal (some x))] "h" (.b true)) =
        .ok ((envExtend (envExtend [("o", .optVal (some x))] "h" (.b true))
          "v" (.i32 x)), .returned (.i32 x)) :=
      Eq.trans (evalProgStmt_if_true _ _ _ _ _ _ hcondT) hthen
    have hsum : optDerefFwd (some x) = .ok (.i32 x) := rfl
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepH, hifT]
    simp [hsum]
