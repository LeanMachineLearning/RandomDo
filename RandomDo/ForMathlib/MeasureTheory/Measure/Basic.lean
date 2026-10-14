/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Measure of an intersection and symmetric differences

## Main statements

* `measure_inter_le_measure_inter_add_symmDiff`: the measure of `s ∩ t` is at most the measure
  of `s' ∩ t'` plus the measures of the symmetric differences of `s`, `s'` with a common set `u`
  and of `t`, `t'` with a common set `v`.
-/

@[expose] public section

open Set

open scoped symmDiff

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- If `s` is close to `s'` and `t` is close to `t'`, in the sense that they are close to common
sets `u` and `v` respectively, then the measure of `s ∩ t` is not much larger than the measure
of `s' ∩ t'`. -/
lemma measure_inter_le_measure_inter_add_symmDiff (μ : Measure α) (s s' t t' u v : Set α) :
    μ (s ∩ t) ≤ μ (s' ∩ t') + (μ (s ∆ u) + μ (s' ∆ u)) + (μ (t ∆ v) + μ (t' ∆ v)) := by
  have hsub : s ∩ t ⊆ (s' ∩ t') ∪ (s ∆ u ∪ s' ∆ u) ∪ (t ∆ v ∪ t' ∆ v) := by
    intro y hy
    simp only [mem_union, mem_inter_iff, mem_symmDiff] at hy ⊢
    tauto
  exact (measure_mono hsub).trans <| (measure_union_le _ _).trans <| add_le_add
    ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))
    (measure_union_le _ _)

end MeasureTheory
