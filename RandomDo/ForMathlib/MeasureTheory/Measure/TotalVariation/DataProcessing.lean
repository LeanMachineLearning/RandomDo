/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import RandomDo.ForMathlib.MeasureTheory.Measure.TotalVariation.Defs

/-!
# Data-processing inequality for the total variation distance

## Main statements

* `etvDist_comp_le`, `tvDist_comp_le`: **data-processing inequality** for the total variation
  distance, `etvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ etvDist μ ν` for a Markov kernel `κ`.
-/

@[expose] public section

open ProbabilityTheory

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}

/-- **Data-processing inequality** for the total variation distance: composition with a Markov
kernel does not increase the distance. -/
lemma etvDist_comp_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (μ ν : Measure 𝓧) :
    etvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  swap; · simp [etvDist_of_not_isFiniteMeasure h]
  obtain ⟨_, _⟩ := h
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hμ : μ = μ.restrict s + ν.restrict sᶜ + (μ.restrict sᶜ - ν.restrict sᶜ) := by
    rw [add_assoc, add_comm (ν.restrict sᶜ), Measure.sub_add_cancel_of_le hs.ge_on_compl,
      Measure.restrict_add_restrict_compl hs.measurableSet]
  have hν : ν = μ.restrict s + ν.restrict sᶜ + (ν.restrict s - μ.restrict s) := by
    rw [add_comm (μ.restrict s), add_assoc, add_comm (μ.restrict s),
      Measure.sub_add_cancel_of_le hs.le_on, add_comm,
      Measure.restrict_add_restrict_compl hs.measurableSet]
  calc etvDist (κ ∘ₘ μ) (κ ∘ₘ ν)
  _ = etvDist (κ ∘ₘ (μ.restrict s + ν.restrict sᶜ) + κ ∘ₘ (μ.restrict sᶜ - ν.restrict sᶜ))
      (κ ∘ₘ (μ.restrict s + ν.restrict sᶜ) + κ ∘ₘ (ν.restrict s - μ.restrict s)) := by
    rw [← Measure.comp_add, ← Measure.comp_add, ← hμ, ← hν]
  _ ≤ (κ ∘ₘ (μ.restrict sᶜ - ν.restrict sᶜ)) Set.univ
      + (κ ∘ₘ (ν.restrict s - μ.restrict s)) Set.univ :=
    (etvDist_add_left _ _ _).trans_le etvDist_le_add
  _ = ν s - μ s + (μ sᶜ - ν sᶜ) := by
    rw [Measure.comp_apply_univ, Measure.comp_apply_univ,
      Measure.sub_apply .univ hs.ge_on_compl, Measure.sub_apply .univ hs.le_on, add_comm]
    simp
  _ = etvDist μ ν := hs.etvDist_eq.symm

/-- **Data-processing inequality** for the total variation distance: composition with a Markov
kernel does not increase the distance. -/
lemma tvDist_comp_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (μ ν : Measure 𝓧) :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    exact ENNReal.toReal_mono (etvDist_ne_top μ ν) (etvDist_comp_le κ μ ν)
  -- if `μ` or `ν` is not finite, neither is its image, and both distances are `(∞).toReal = 0`
  · have h' : ¬ (IsFiniteMeasure (κ ∘ₘ μ) ∧ IsFiniteMeasure (κ ∘ₘ ν)) := by
      rintro ⟨hμ, hν⟩
      refine h ⟨⟨?_⟩, ⟨?_⟩⟩
      · rw [← Measure.comp_apply_univ (κ := κ)]
        exact measure_lt_top _ _
      · rw [← Measure.comp_apply_univ (κ := κ)]
        exact measure_lt_top _ _
    rw [tvDist, etvDist_of_not_isFiniteMeasure h', ENNReal.toReal_top]
    exact tvDist_nonneg

end MeasureTheory
