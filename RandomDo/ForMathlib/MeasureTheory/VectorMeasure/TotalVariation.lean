/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.TotalVariation

/-!
# Translation invariance of the total variation distance of vector measures

## Main statements

* `VectorMeasure.etvDist_add_left`, `VectorMeasure.etvDist_add_right`:
  `etvDist (ξ + μ) (ξ + ν) = etvDist μ ν`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.VectorMeasure

variable {𝓧 M : Type*} {m𝓧 : MeasurableSpace 𝓧} [NormedAddCommGroup M]

/-- The total variation distance is invariant by translation. -/
lemma etvDist_add_left (ξ μ ν : VectorMeasure 𝓧 M) : etvDist (ξ + μ) (ξ + ν) = etvDist μ ν := by
  rw [etvDist, etvDist, add_sub_add_left_eq_sub]

/-- The total variation distance is invariant by translation. -/
lemma etvDist_add_right (μ ν ξ : VectorMeasure 𝓧 M) : etvDist (μ + ξ) (ν + ξ) = etvDist μ ν := by
  rw [etvDist, etvDist, add_sub_add_right_eq_sub]

end MeasureTheory.VectorMeasure
