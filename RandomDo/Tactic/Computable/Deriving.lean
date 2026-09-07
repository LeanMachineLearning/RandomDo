/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Tactic.Computable.Counterparts
public import RandomDo.Monad.MeasurableSpace
public meta import Lean.Elab.Tactic.Basic
public meta import Batteries.Tactic.Lint.Basic

/-!
# The `@[computable]` attribute

Writing an `rdo` program and writing the program that samples from it are two separate steps, and
the second is mechanical: every construct of the first has a counterpart in the second. This
attribute walks the program and writes that counterpart down, so a program carries the sampler it
denotes:

```
@[computable]
noncomputable def shifted : Measure ℝ := rdo
  let x ← gaussianReal 0 1
  return x + 1
```

adds `shifted_computable : RandPCG IO Float`, which draws from `NumLean.normal 0 1` and adds one.

## How the program is read

The two constructs `rdo` is made of become the two of `do`: `return e` becomes `pure e`, and
`let x ← p; q` becomes `p >>= q`, at `RandPCG IO`. Everything else — a distribution, a numeral, an
operation on the values the program computes with — is rebuilt from the counterpart
`@[computable_as]` records for its head, applied to the translation of its arguments; the
instances it asks for are synthesized anew, for the translated types.
-/

public meta section

open Lean Meta NumLean

namespace RDo.Tactic

/-- The monad a translated program lives in, `RandPCG IO`: the counterpart of the Giry monad an
`rdo` program is written over. -/
def computableMonad : MetaM Expr := mkAppM ``RandPCG #[mkConst ``IO]

/-- Translate `e`, a piece of an `rdo` program, into its computable counterpart. `σ` sends the
variables the program binds to the ones the translated program binds in their place, which the
change of types makes necessary. -/
partial def translate (σ : FVarSubst) (e : Expr) : MetaM Expr := do
  -- `MeasurableSpacePure.mPure` takes five arguments, the last of which is the value returned.
  if e.isAppOfArity ``MeasurableSpacePure.mPure 5 then
    mkAppOptM ``Pure.pure #[← computableMonad, none, none, ← translate σ (e.getArg! 4)]
  -- `MeasurableSpaceBind.mBind` takes eight, the last two being the program and the continuation.
  else if e.isAppOfArity ``MeasurableSpaceBind.mBind 8 then
    mkAppOptM ``Bind.bind #[← computableMonad, none, none, none,
      ← translate σ (e.getArg! 6), ← translate σ (e.getArg! 7)]
  else match e with
  | .fvar fvarId => return σ.get fvarId
  | .sort .. | .lit .. => return e
  | .mdata _ b => translate σ b
  | .lam .. =>
    lambdaBoundedTelescope e 1 fun xs body ↦ do
      let x := xs[0]!
      let t ← translate σ (← x.fvarId!.getType)
      withLocalDeclD (← x.fvarId!.getUserName) t fun y ↦ do
        mkLambdaFVars #[y] (← translate (σ.insert x.fvarId! y) body)
  | _ =>
    let .const declName _ := e.getAppFn
      | throwError "`computable`: cannot translate{indentExpr e}"
    let counterpart := (← computableAs? declName).getD declName
    let mut f ← mkConstWithFreshMVarLevels counterpart
    for arg in e.getAppArgs do
      let .forallE _ t _ bi ← whnf (← inferType f)
        | throwError "`computable`: {f} does not take the argument{indentExpr arg}"
      let arg ← if bi.isInstImplicit then synthInstance t else translate σ arg
      unless ← isDefEq (← inferType arg) t do
        throwError "`computable`: {arg} does not fit the argument of {f}, of type{indentExpr t}"
      f := mkApp f arg
    return f

/-- Translate the `rdo` program `declName` and add the translation to the environment, under the
name `declName` followed by `_computable`. -/
def addComputableDecl (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let some value := info.value?
    | throwError "`computable` can only be derived for a definition, but {declName} has no value"
  let value ← instantiateMVars (← translate {} value)
  let type ← instantiateMVars (← inferType value)
  let translated := declName.appendAfter "_computable"
  addAndCompile <| .defnDecl <| ← mkDefinitionValInferringUnsafe translated info.levelParams type
    value (.regular (getMaxHeight (← getEnv) value + 1))
  addDocStringCore translated s!"The program that samples from `{declName}`, written by the \
    `@[computable]` attribute."
  /- The name is one the attribute picks and not one the user wrote, so the underscore in it is
  reported for every program translated unless it is exempted here. -/
  setEnv (← ofExcept (Batteries.Tactic.Lint.nolintAttr.setParam (← getEnv) translated
    #[`defsWithUnderscore]))

/-- The `@[computable]` attribute. -/
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
