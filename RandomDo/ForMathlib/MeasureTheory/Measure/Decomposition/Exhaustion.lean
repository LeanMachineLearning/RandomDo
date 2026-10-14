/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Exhaustion

/-!
# A Lebesgue-type decomposition with respect to an arbitrary measure

## Main statements

* `Measure.exists_null_restrict_compl_absolutelyContinuous`: for an s-finite measure `π` and an
  arbitrary measure `φ`, there is a measurable `φ`-null set `N` such that `π.restrict Nᶜ ≪ φ`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α}

/-- For an s-finite measure `π` and an arbitrary measure `φ`, there is a measurable `φ`-null set
`N` such that the restriction of `π` to `Nᶜ` is absolutely continuous with respect to `φ`. No
finiteness assumption is made on `φ`. -/
lemma exists_null_restrict_compl_absolutelyContinuous (φ π : Measure α) [SFinite π] :
    ∃ N, MeasurableSet N ∧ φ N = 0 ∧ π.restrict Nᶜ ≪ φ := by
  -- we apply the exhaustion method to the measure `∞ • φ`, which takes values in `{0, ∞}`
  let N := ((∞ : ℝ≥0∞) • φ).sigmaFiniteSetWRT π
  have hN : MeasurableSet N := measurableSet_sigmaFiniteSetWRT
  refine ⟨N, hN, ?_, AbsolutelyContinuous.mk fun t ht hφt ↦ ?_⟩
  · have : SigmaFinite (((∞ : ℝ≥0∞) • φ).restrict N) := inferInstance
    let S := spanningSets (((∞ : ℝ≥0∞) • φ).restrict N)
    have hS : ∀ i, φ (S i ∩ N) = 0 := by
      intro i
      have h_lt := measure_spanningSets_lt_top (((∞ : ℝ≥0∞) • φ).restrict N) i
      rw [restrict_apply (measurableSet_spanningSets _ i), smul_apply, smul_eq_mul] at h_lt
      by_contra h0
      rw [ENNReal.top_mul h0] at h_lt
      exact lt_irrefl _ h_lt
    have h_eq : N = ⋃ i, S i ∩ N := by
      rw [← Set.iUnion_inter, iUnion_spanningSets, Set.univ_inter]
    rw [h_eq]
    exact measure_iUnion_null hS
  · rw [restrict_apply ht]
    by_contra h0
    have h_top : ((∞ : ℝ≥0∞) • φ) (t ∩ Nᶜ) = ∞ :=
      measure_eq_top_of_subset_compl_sigmaFiniteSetWRT Set.inter_subset_right h0
    rw [measure_mono_null Set.inter_subset_left (by simp [hφt])] at h_top
    exact ENNReal.zero_ne_top h_top

end MeasureTheory.Measure
