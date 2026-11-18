/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Data.Erased
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# The measurable space on `Erased`

Equip `Erased α` with the measurable space transported along `Erased.mk`. The maps `Erased.mk` and
`Erased.out` are measurable, so hiding a value from compiled code preserves its measurable
structure. This supports the state carried by `erased mut` variables in `rdo` loops.
-/

@[expose] public section

namespace Erased

-- Proof-valued erased variables also occur in core's loop state. They have at most one
-- value, hence a unique measurable space; there is no measurable-space declaration in core.
#check Erased

instance instMeasurableSpaceProp {p : Prop} : MeasurableSpace (Erased p) := ⊤

variable {α : Type*} [mα : MeasurableSpace α]

-- Core has no measurable-space counterpart. Using the computable `mk`, rather than
-- the noncomputable `out`, keeps this instance usable in compiled polymorphic programs.
-- The inverse equations `Erased.out_mk` and `Erased.mk_out` identify this with the given space.
#check Erased.mk

instance instMeasurableSpace : MeasurableSpace (Erased α) :=
  MeasurableSpace.map mk mα

-- Measurability is additional to core's `Erased.out` API.
#check Erased.out

@[fun_prop] theorem measurable_out : Measurable (out : Erased α → α) :=
by
  intro s hs
  rw [MeasurableSpace.map_def]
  simpa [Set.preimage_preimage, Function.comp_def] using hs

-- Measurability is additional to core's `Erased.mk` API.
#check Erased.mk

@[fun_prop] theorem measurable_mk : Measurable (mk : α → Erased α) :=
  fun _ hs => hs

end Erased
