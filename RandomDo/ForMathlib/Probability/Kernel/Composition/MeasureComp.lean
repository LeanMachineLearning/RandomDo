/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Pushforwards of the composition-product of a measure and a kernel

## Main results

* `Measure.map_compProd_eq_bind`: mapping `μ ⊗ₘ κ` along `g` is binding `κ a` mapped along the
  section `g (a, ·)`.
-/

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Mapping a composition-product is binding the kernel, mapped along the section. -/
lemma map_compProd_eq_bind (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {g : α × β → γ} (hg : Measurable g) :
    (μ ⊗ₘ κ).map g = μ.bind fun a ↦ (κ a).map fun b ↦ g (a, b) := by
  rw [compProd_eq_comp_prod, map_comp _ _ hg]
  refine bind_congr_right (.of_forall fun a ↦ ?_)
  rw [Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.id_apply, dirac_prod,
    map_map hg measurable_prodMk_left]
  rfl

end MeasureTheory.Measure
