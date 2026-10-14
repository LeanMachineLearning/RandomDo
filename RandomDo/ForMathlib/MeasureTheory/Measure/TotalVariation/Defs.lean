/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

/-!
# Total variation distance of measures with a common part

## Main statements

* `etvDist_add_left_le`: `etvDist (ξ + μ) (ξ + ν) ≤ μ univ + ν univ`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- If two measures have a common part `ξ`, their total variation distance is at most the sum of
the masses of the remaining parts. -/
lemma etvDist_add_left_le (ξ μ ν : Measure 𝓧) [IsFiniteMeasure ξ] :
    etvDist (ξ + μ) (ξ + ν) ≤ μ Set.univ + ν Set.univ := by
  calc etvDist (ξ + μ) (ξ + ν)
  _ ≤ etvDist (ξ + μ) ξ + etvDist ξ (ξ + ν) := etvDist_triangle _ _ _
  _ = μ Set.univ + ν Set.univ := by
    rw [etvDist_of_ge (Measure.le_add_right le_rfl), etvDist_of_le (Measure.le_add_right le_rfl),
      Measure.add_apply, Measure.add_apply, ENNReal.add_sub_cancel_left (measure_ne_top _ _),
      ENNReal.add_sub_cancel_left (measure_ne_top _ _)]

end MeasureTheory
