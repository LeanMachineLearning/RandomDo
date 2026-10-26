/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Lean.Attributes

/-!
# Analogous declarations

`@[analogue f g]` records declarations that a local declaration adapts.
The names are resolved when the attribute is applied and stored as metadata.
-/

public meta section

namespace RandomDo.Analogue

open Lean

/-- Record declarations that a local declaration adapts. -/
syntax (name := analogue) "analogue " ident+ : attr

/-- The declarations associated with each analogue. -/
initialize analogueAttr : ParametricAttribute (Array Name) ← registerParametricAttribute {
  name := `analogue
  descr := "Record declarations that this declaration adapts."
  getParam := fun _ stx => stx[1].getArgs.mapM resolveGlobalConstNoOverload
}

end RandomDo.Analogue
