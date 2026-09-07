/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public meta import Batteries.Lean.NameMapAttribute
public meta import Lean.ReservedNameAction

/-!
# The `@[computable_as]` attribute

An `rdo` program is written over the Giry monad: it draws from measures on `ℝ`, which no machine
samples. Turning it into a program that runs, which the `@[computable]` attribute of
`RandomDo.Tactic.Computable.Deriving` does, asks for a counterpart of each piece the program is
built from: `Float` for `ℝ`, `NumLean.normal` for `gaussianReal`. This file holds the attribute
recording them; `RandomDo.Tactic.Computable.Counterparts` holds the counterparts themselves.

`@[computable_as f]` on a declaration `d` reads: `f` is what `d` becomes in a translated program.
Only the pieces denoting something the program computes with need one. The scaffolding around
them — numerals, arithmetic — is polymorphic, and the translation keeps it as it is, at the
translated types.
-/

public meta section

open Lean

namespace RDo.Tactic

/-- The counterparts recorded by `@[computable_as]`, keyed by the declaration they translate. -/
initialize computableAsExt : NameMapExtension Name ←
  registerNameMapAttribute {
    name := `computable_as
    descr := "record the computable counterpart of this declaration"
    /- `@[computable_as f]` is read by `Lean.Parser.Attr.simple`, the parser an attribute that
    declares no syntax of its own gets: `f` is the single child of `stx[1]`. -/
    add := fun _ stx ↦ do
      let f := stx[1][0]
      unless f.isIdent do
        throwError "`computable_as` takes the name of one declaration"
      realizeGlobalConstNoOverload f
  }

/-- The computable counterpart of `declName`, when `@[computable_as]` recorded one. -/
def computableAs? (declName : Name) : CoreM (Option Name) :=
  return computableAsExt.find? (← getEnv) declName

end RDo.Tactic

end
