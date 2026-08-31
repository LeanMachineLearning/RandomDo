/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.Tactic.Elab

/-!
# The `@[is_markov]` attribute

Writing an `rdo` program and then stating that it is a Markov kernel are two separate steps, and
the second is mechanical: it is what `is_markov` does. This attribute runs it at the declaration,
so a program carries its own instance:

```
@[is_markov]
noncomputable def centred (c : ℝ) : Measure ℝ := rdo
  let x ← gaussianReal c 1
  return x
```

## Which statement is generated

A program's *last* argument is read as the kernel's parameter when it is explicit, giving
`IsMarkov`. Otherwise the program denotes one fixed distribution and the statement is
`IsProbabilityMeasure`. So `centred` above yields `IsMarkov centred`, while a parameterless program
yields `IsProbabilityMeasure` of it, and a program whose trailing arguments are instance-implicit —
`(μ : Measure ℝ) [IsProbabilityMeasure μ]` — yields `IsProbabilityMeasure` of it too, with those
arguments bound.
-/

public meta section

open Lean Meta Elab Term MeasureTheory

namespace RDo.Tactic

/-- The statement to prove for `declName`, as described in the module docstring. -/
def isMarkovStatement (declName : Name) : MetaM Expr := do
  let info ← getConstInfo declName
  forallTelescope info.type fun args body ↦ do
    unless body.isAppOfArity ``MeasureTheory.Measure 2 do
      throwError "`IsMarkov` can only be derived for a declaration valued in `Measure`, but \
        {declName} is valued in{indentExpr body}"
    let f := mkAppN (mkConst declName (info.levelParams.map .param)) args
    if h : 0 < args.size then
      let last := args[args.size - 1]
      if (← last.fvarId!.getDecl).binderInfo.isExplicit then
        return ← mkForallFVars args.pop (← mkAppM ``IsMarkov #[← mkLambdaFVars #[last] f])
    mkForallFVars args (← mkAppM ``MeasureTheory.IsProbabilityMeasure #[f])

/-- Prove `isMarkovStatement declName` with the `is_markov` tactic and register it as an
instance. -/
def addIsMarkovInstance (declName : Name) : TermElabM Unit := do
  let goal ← isMarkovStatement declName
  let proof ← Term.elabTerm (← `(by intros; is_markov)) (some goal)
  Term.synthesizeSyntheticMVarsNoPostponing
  let info ← getConstInfo declName
  let instName := declName ++ `isMarkov
  addDecl (.thmDecl { name := instName, levelParams := info.levelParams, type := goal,
                      value := ← instantiateMVars proof })
  Meta.addInstance instName .global 1000

/-- The `@[is_markov]` attribute. -/
initialize registerBuiltinAttribute {
  name := `is_markov
  descr := "prove that this `rdo` program is a Markov kernel, and register it as an instance"
  applicationTime := .afterCompilation
  add := fun declName _stx kind ↦ do
    unless kind == AttributeKind.global do
      throwError "`is_markov` must be a global attribute"
    (addIsMarkovInstance declName).run'.run'
}

end RDo.Tactic

end
