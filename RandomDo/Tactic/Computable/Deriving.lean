/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Tactic.Computable.Counterparts
public import RandomDo.Monad.MeasurableSpace
public meta import Lean.Elab.Tactic.Basic

/-!
# The `@[computable]` attribute

`@[computable]` reads an `rdo` program and adds the program that samples from it:

```
@[computable]
noncomputable def shifted : Measure ℝ := rdo
  let x ← gaussianReal 0 1
  return x + 1
```

adds `shiftedComputable : RandPCG IO Float`, which draws from `NumLean.normal' 0 1` and adds one.

The Giry monad and its two operations become `RandPCG IO`, `pure` and `bind`. Anything else is
rebuilt from the counterpart `@[computable_as]` records for its head, with its arguments translated
in turn and its instances synthesized anew. A term translates into a term of the translation of its
type; where the rebuilt one does not, its head is a definition nothing is known about, and its body
is read in its place. `@[computable]` records the program it writes, so a program drawing from
another translates into one calling that other's translation.

Two things extend the attribute: an `@[computable_as]` entry, and an alternative of `translate` for
a construct of `rdo` it has not been taught.

`set_option trace.computable true` prints what each piece became.
-/

public meta section

open Lean Meta NumLean

namespace RDo.Tactic

initialize registerTraceClass `computable

/-- The monad the translated programs live in. -/
def computableMonad : MetaM Expr := mkAppM ``RandPCG #[mkConst ``IO]

mutual

/-- Translate a piece of an `rdo` program. `σ` maps the variables the program binds to the ones the
translated program binds in their place. -/
partial def translate (σ : FVarSubst) (e : Expr) : MetaM Expr :=
  withTraceNode `computable (fun
      | .ok e' => return m!"{e} ↦ {e'}"
      | .error _ => return m!"{e}: not translated") do
    match_expr e with
    | MeasurableSpacePure.mPure _ _ _ _ a =>
      mkAppOptM ``Pure.pure #[← computableMonad, none, none, ← translate σ a]
    | MeasurableSpaceBind.mBind _ _ _ _ _ _ p k =>
      mkAppOptM ``Bind.bind #[← computableMonad, none, none, none,
        ← translate σ p, ← translate σ k]
    | MeasureTheory.Measure α _ => return mkApp (← computableMonad) (← translate σ α)
    | _ => match e with
      | .fvar x => return σ.get x
      | .sort .. | .lit .. => return e
      | .mdata _ b => translate σ b
      | .lam .. => lambdaBoundedTelescope e 1 fun xs body ↦ do
        let x := xs[0]!.fvarId!
        withLocalDeclD (← x.getUserName) (← translate σ (← x.getType)) fun y ↦ do
          mkLambdaFVars #[y] (← translate (σ.insert x y) body)
      | _ => translateApp σ e

/-- Rebuild an application from the counterpart of its head; where nothing known about that head
fits, look through it and read its body in its place. -/
partial def translateApp (σ : FVarSubst) (e : Expr) : MetaM Expr := do
  if e.getAppFn.isLambda then return ← translate σ e.headBeta
  let .const declName _ := e.getAppFn | throwError "`computable`: cannot translate{indentExpr e}"
  let counterpart? ← computableAs? declName
  let head := counterpart?.getD declName
  /- We save the state of metavariables, so that a failed rebuild does not leave them in a
  half-built state. -/
  let s ← saveState
  try
    /- A term translates into a term of the translation of its type. A head nothing is known about
    rebuilds into itself, of the type it had, and might fail. We check that the rebuilt term has
    the translation of the type, and if not, we look through it. -/
    let f ← rebuild σ head e
    -- Useless for a type, whose type is a sort either way.
    if (← inferType f).isSort then return f
    let expected ← translate σ (← inferType e)
    unless ← isDefEq (← inferType f) expected do
      throwError "`computable`: {f} is of type{indentExpr (← inferType f)}\n\
        where the translation asks for{indentExpr expected}"
    return f
  catch ex =>
    restoreState s
    /- The rebuild failed, we try to look through the head, and read its body in its place. -/
    if counterpart?.isNone then
      if let some e' ← unfoldDefinition? e then
        trace[computable] "nothing known about {declName}, looking through it"
        return ← translate σ e'
    throw ex

/-- Apply `head` to the arguments of `e`, translated in turn, and check that the result has the
translation of the type of `e`. -/
partial def rebuild (σ : FVarSubst) (head : Name) (e : Expr) : MetaM Expr := do
  let mut f ← mkConstWithFreshMVarLevels head
  for arg in e.getAppArgs do
    let .forallE _ t _ bi ← whnf (← inferType f)
      | throwError "`computable`: {f} does not take the argument{indentExpr arg}"
    let arg ←
      if bi.isInstImplicit then do
        -- An instance is not translated: it is asked for anew, at the translated types.
        let inst ← synthInstance t
        trace[computable] "instance: {inst}"
        pure inst
      else
        translate σ arg
    unless ← isDefEq (← inferType arg) t do
      throwError "`computable`: {arg} does not fit the argument of {f}, of type{indentExpr t}"
    f := mkApp f arg
  return f

end

/-- Translate the `rdo` program `declName` and add the translation to the environment, under the
name `declName` followed by `Computable`. -/
def addComputableDecl (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let some value := info.value?
    | throwError "`computable` can only be derived for a definition, but {declName} has no value"
  let value ← instantiateMVars (← translate {} value)
  let type ← instantiateMVars (← inferType value)
  let translated := declName.appendAfter "Computable"
  addAndCompile <| .defnDecl <| ← mkDefinitionValInferringUnsafe translated info.levelParams type
    value (.regular (getMaxHeight (← getEnv) value + 1))
  addDocStringCore translated s!"The computable program that samples from `{declName}` \
    (automatically generated by the `@[computable]` attribute)."
  computableAsExt.add declName translated
  trace[computable] "wrote {translated}:{indentExpr type}"

@[inherit_doc addComputableDecl]
initialize registerBuiltinAttribute {
  name := `computable
  descr := "translate this `rdo` program into the program that samples from it"
  applicationTime := .afterCompilation
  add := fun declName _stx kind ↦ do
    unless kind == AttributeKind.global do
      throwError "`computable` must be a global attribute"
    (addComputableDecl declName).run'
}

end RDo.Tactic

end
