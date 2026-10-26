/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Lean.Elab.Command

/-!
# Tracking adaptations of Lean core

`@[analogue decl₁ decl₂]` records the Lean core declarations from which a declaration was adapted.
It checks that the names exist and stores them as metadata, without changing the declaration or
its docstring. `scripts/ExportUpstream.lean` exports this metadata for the upstream change checker.
See `docs/upstream-tracking.md` for the review and baseline update workflow.
-/

public meta section

namespace RandomDo.Analogue

open Lean

/-- Mark a declaration as an adaptation of one or more declarations in Lean core. -/
syntax (name := analogue) "analogue " ident+ : attr

/-- The upstream declarations associated with each adapted declaration. -/
initialize analogueAttr : ParametricAttribute (Array Name) ← registerParametricAttribute {
  name := `analogue
  descr := "Record the Lean core declarations from which this declaration was adapted."
  getParam := fun _ stx => do
    let names ← stx[1].getArgs.mapM resolveGlobalConstNoOverload
    let env ← getEnv
    for name in names do
      let some idx := env.getModuleIdxFor? name
        | throwErrorAt stx "Analogue declaration `{name}` must be imported from Lean core"
      let mod := env.header.moduleNames[idx.toNat]!
      unless [`Init, `Lean, `Std].any (·.isPrefixOf mod) do
        throwErrorAt stx "Analogue declaration `{name}` belongs to `{mod}`, not Lean core"
    unless names.toList.eraseDups.length == names.size do
      throwErrorAt stx "Duplicate analogue declarations"
    return names
}

end RandomDo.Analogue
