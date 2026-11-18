/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable space constructions

This file adds measurability of `Id.run`, measurable singletons for `ULift`, and joint
measurability of function-valued maps when the second argument ranges over a countable
space with measurable singletons. It also provides `Measurable.congr` for replacing a measurable
function by a pointwise equal function.
-/

@[expose] public section

/-- A function pointwise equal to a measurable function is measurable. -/
theorem Measurable.congr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f g : α → β} (hf : Measurable f) (h : ∀ a, f a = g a) : Measurable g :=
  funext h ▸ hf

variable {α : Type*} [MeasurableSpace α]

@[fun_prop]
theorem measurable_id_run : Measurable (fun x : α => Id.run x) := measurable_id

instance ULift.instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (ULift α) where
  measurableSet_singleton x := by
    convert measurable_down (measurableSet_singleton x.down) using 1
    rw [← Set.image_singleton, Set.preimage_image_eq _ ULift.down_bijective.injective]

variable {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]

/-- A measurable function-valued map is jointly measurable when its second argument ranges over
a countable space with measurable singletons. -/
theorem Measurable.uncurry [Countable β] [MeasurableSingletonClass β]
    {f : α → β → γ} (hf : Measurable f) : Measurable (Function.uncurry f) :=
  measurable_from_prod_countable_left fun _ => hf.eval
