/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Mathlib.Lean.Meta.Simp

/-! # `congr%` term elaborator

This module defines a term elaborator for generating congruence lemmas according to a pattern.
Rather than using `congr_arg` or `congr_fun`, one can write `congr% c(hf) c(hx)` with
`hf : f = f'` and `hx : x = x'` to get `f x = f' x'`. This is also more general, since
`f` could have implicit arguments and complicated dependent types.
-/

namespace Mathlib.Tactic
open Lean Elab Meta

initialize registerTraceClass `Tactic.congr

/--
`congr% expr` generates an congruence where `expr` is an expression containing
congruence holes of the form `c(h)`. In these congruence holes, `h : a = b` indicates
that, in the generated congruence, on the left-hand side `a` is substituted for `c(h)`
and on the right-hand side `b` is substituted.

For example, if `h : a = b` then `congr% 1 + c(h) : 1 + a = 1 + b`.
-/
syntax (name := termCongr) "congr% " term : term

/--
`c(h)` is a hole in a `congr%` expression, where `h` is an equality or iff.
-/
-- Copying the `paren` parser but with `c` in front.
syntax (name := termCongrEq)
  "c(" withoutPosition(withoutForbidden(ppDedentIfGrouped(term))) ")" : term

elab_rules : term
  | `(c($_)) =>
    throwError "invalid occurrence of `c(...)` notation; it must appear in a `congr%` expression"

/-- Extracts the LHS of an equality while holding onto the equality for later use.
The `c(..)` notation is replaced by this during elaboration of `congr%`. -/
@[reducible] def c_lhs {α : Sort _} {x y : α} (_ : x = y) : α := x

/-- Ensures the expected type is an equality. Returns the equality along with the type
being equated, the lhs, and the rhs. -/
private def mkEqForExpectedType (expectedType? : Option Expr) :
    Term.TermElabM (Expr × Expr × Expr × Expr) := do
  let ty ← Meta.mkFreshTypeMVar
  let a ← Meta.mkFreshExprMVar ty
  let b ← Meta.mkFreshExprMVar ty
  let eq ← Meta.mkEq a b
  if let some expectedType := expectedType? then
    unless ← Meta.isDefEq expectedType eq do
      throwError m!"Term {← Meta.mkHasTypeButIsExpectedMsg eq expectedType}"
  return (eq, ty, a, b)

/-- `ensure_eq% h` ensures that `h : x = y`. If `h : x ↔ y` then uses `propext`. -/
syntax (name := ensureEq) "ensure_eq% " term : term

@[term_elab ensureEq]
def elabEnsureEq : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(ensure_eq% $eStx) =>
    let (eq, _) ← mkEqForExpectedType expectedType?
    let mut e ← Term.elabTerm eStx none
    if let some .. := (← whnfR (← inferType e)).iff? then
      e ← mkPropExt e
    Term.ensureHasType eq e
  | _ => throwUnsupportedSyntax

/-- (Internal for `congr%`)
Helper to expand `c(..)` into a `c_lhs` expression. Produces an annotated term
to ensure `c_lhs` always regarded as having exactly four arguments. -/
syntax (name := congrCExpand) "congr_c_expand% " term : term

@[term_elab congrCExpand]
def elabCongrCExpand : Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(congr_c_expand% $e) => do
    let e ← Term.elabTerm (← `(c_lhs (ensure_eq% $e))) expectedType?
    return mkAnnotation ``congrCExpand e
  | _ => throwUnsupportedSyntax

/-- Gives the un-annotated expression for expressions elaborated by `congr_c_expand%`. -/
def congrCExpand? (e : Expr) : Option Expr := annotation? ``congrCExpand e

/-- Elaborates to the LHS of the type of an equality proof -/
syntax (name := eq_lhs_term) "eq_lhs% " term:max : term

/-- Elaborates to the RHS of the type of an equality proof -/
syntax (name := eq_rhs_term) "eq_rhs% " term:max : term

@[term_elab eq_lhs_term, term_elab eq_rhs_term]
def elabEqLhsRhsTerm : Term.TermElab := fun stx expectedType? => do
  let (isLhs, term) ←
    match stx with
    | `(eq_lhs% $t) => pure (true, t)
    | `(eq_rhs% $t) => pure (false, t)
    | _ => throwUnsupportedSyntax
  let (eq, _) ← mkEqForExpectedType expectedType?
  let h ← Term.elabTerm term eq
  let some (_, lhs, rhs) := (← whnfR (← inferType h)).eq?
    | throwError "Term {← mkHasTypeButIsExpectedMsg (← inferType h) eq}"
  if isLhs then
    return lhs
  else
    return rhs

@[term_elab termCongr]
def elabTermCongr : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(congr% $t) =>
    let (expEq, expTy, _) ← mkEqForExpectedType expectedType?
    -- Use `c_lhs` to store the equalities in the terms. Makes sure to annotate the
    -- terms to ensure that if `c(h)` is used as a function, `simp` still sees `c_lhs`
    -- as a four-argument function.
    let left ← t.raw.replaceM fun
      | `(c($h)) => ``(congr_c_expand% $h)
      | _ => pure none
    let preLeft ← Term.withoutErrToSorry do
      try
        Term.elabTermEnsuringType left expTy
      catch ex =>
        -- Failed, so let's re-elaborate with
        let left ← t.raw.replaceM fun
          | `(c($h)) => ``(eq_lhs% $h)
          | _ => pure none
        discard <| Term.elabTermEnsuringType left expTy
        -- That should fail, but if it didn't we at least can throw the original exception:
        throw ex
    Term.synthesizeSyntheticMVarsUsingDefault
    trace[Tactic.congr] "preLeft = {preLeft}"
    trace[Tactic.congr] "raw preLeft = {toString preLeft}"
    -- Unfold the `c_lhs` terms and remove annotations to get the true LHS
    let left := preLeft.replace (fun e =>
      if let some (_α, lhs, _rhs, _eq) := e.app4? ``c_lhs then lhs else none)
    let left := left.replace congrCExpand?
    trace[Tactic.congr] "left = {left}"
    -- Rewrite the `c_lhs` terms to get the RHS. `c_lhs` is reducible, which makes using
    -- a simp lemma not work reliably, so using a pre-transform instead.
    let simpCtx : Simp.Context :=
      { config := Simp.neutralConfig,
        simpTheorems := #[]
        congrTheorems := (← getSimpCongrTheorems) }
    let preTrans (e : Expr) : SimpM Simp.Step := do
      if let some (_α, _lhs, rhs, eq) := e.app4? ``c_lhs then
        return .visit {expr := rhs, proof? := eq}
      else
        return .visit {expr := e}
    let (res, _) ← Simp.main preLeft simpCtx (methods := { pre := preTrans })
    -- Remove the annotations
    let right := res.expr.replace congrCExpand?
    trace[Tactic.congr] "right = {right}"
    -- Make sure there are no `c_lhs` expressions remaining in the term
    if right.find? (·.isConstOf ``c_lhs) matches some .. then
      throwError m!"Could not rewrite all occurrences of c(..) holes. There are still `c_lhs`{
        ""} expressions in{indentExpr right}"
    -- Check the expected type
    let eq' ← mkEq left right
    unless ← Meta.isDefEq eq' expEq do
      throwError m!"Generated congruence {← Meta.mkHasTypeButIsExpectedMsg eq' expEq}"
    -- Create a type hint to lock in the `c_lhs`-free version of the equality.
    mkExpectedTypeHint (← res.getProof) eq'
  | _ => throwUnsupportedSyntax
