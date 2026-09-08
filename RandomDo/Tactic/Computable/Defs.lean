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

An `rdo` program is written over the Giry monad: it draws from measures on a measurable space, which no machine samples. Turning it into a program that runs, which the `@[computable]` attribute of `RandomDo.Tactic.Computable.Deriving` does, asks for a counterpart of each piece the program is
built from, e.g, `NumLean.normal'` for `gaussianReal`. This file holds the attribute
recording them; `RandomDo.Tactic.Computable.Counterparts` holds the counterparts themselves.

`@[computable_as f]` on a declaration `d` reads: `f` is what `d` becomes in a translated program.
-/

public meta section

open Lean

namespace RDo.Tactic

/-- The counterparts recorded by `@[computable_as]`, keyed by the declaration they translate. -/
initialize computableAsExt : NameMapExtension Name ←
  registerNameMapAttribute {
    name := `computable_as
    descr := "record the computable counterpart of this declaration"
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
