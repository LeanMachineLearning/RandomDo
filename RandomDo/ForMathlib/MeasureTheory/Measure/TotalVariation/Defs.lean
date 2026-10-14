/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

/-!
# Translation invariance of the total variation distance

## Main statements

* `etvDist_add_left`, `etvDist_add_right`: `etvDist (ξ + μ) (ξ + ν) = etvDist μ ν` for a finite
  measure `ξ`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The total variation distance is invariant by translation: adding a common finite part `ξ`
to two measures does not change their distance. -/
lemma etvDist_add_left (ξ μ ν : Measure 𝓧) [IsFiniteMeasure ξ] :
    etvDist (ξ + μ) (ξ + ν) = etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    rw [etvDist_eq_etvDist_toSignedMeasure, etvDist_eq_etvDist_toSignedMeasure,
      Measure.toSignedMeasure_add, Measure.toSignedMeasure_add, VectorMeasure.etvDist,
      VectorMeasure.etvDist, add_sub_add_left_eq_sub]
  · have h' : ¬ (IsFiniteMeasure (ξ + μ) ∧ IsFiniteMeasure (ξ + ν)) := by
      rintro ⟨hμ, hν⟩
      exact h ⟨isFiniteMeasure_of_le (ξ + μ) (Measure.le_add_left le_rfl),
        isFiniteMeasure_of_le (ξ + ν) (Measure.le_add_left le_rfl)⟩
    rw [etvDist_of_not_isFiniteMeasure h', etvDist_of_not_isFiniteMeasure h]

/-- The total variation distance is invariant by translation: adding a common finite part `ξ`
to two measures does not change their distance. -/
lemma etvDist_add_right (μ ν ξ : Measure 𝓧) [IsFiniteMeasure ξ] :
    etvDist (μ + ξ) (ν + ξ) = etvDist μ ν := by
  rw [add_comm μ, add_comm ν, etvDist_add_left]

end MeasureTheory
