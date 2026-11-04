/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# The measurable space on `Option`

Equip `Option α` with the largest σ-algebra making `some` measurable. This is the disjoint-union
measurable structure, with `none` as the additional point.
-/

@[expose] public section

namespace Option

variable {α : Type*} [MeasurableSpace α]

instance instMeasurableSpace : MeasurableSpace (Option α) :=
  MeasurableSpace.map some inferInstance

@[simp] theorem measurableSet_iff {s : Set (Option α)} :
    MeasurableSet s ↔ MeasurableSet (some ⁻¹' s) := Iff.rfl

@[fun_prop] theorem measurable_some : Measurable (some : α → Option α) := fun _ hs => hs

end Option
