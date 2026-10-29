/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Superlevel sets and the Lebesgue integral

## Main statements

* `exists_pos_measure_lt_of_lintegral_pos`: if a function has positive integral, then one of its
  strict superlevel sets has positive measure.
* `mul_measure_inter_lt_le_lintegral_mul`: Markov's inequality for a product of two functions.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- If a function has positive integral, then one of its strict superlevel sets has positive
measure. -/
lemma exists_pos_measure_lt_of_lintegral_pos {f : α → ℝ≥0∞} (hf : 0 < ∫⁻ a, f a ∂μ) :
    ∃ ε : ℝ≥0, 0 < ε ∧ 0 < μ {a | (ε : ℝ≥0∞) < f a} := by
  by_contra! h
  refine hf.ne' (lintegral_eq_zero_of_ae_eq_zero ?_)
  have h' : ∀ᵐ a ∂μ, ∀ n : ℕ, f a ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    rw [ae_all_iff]
    intro n
    have hn0 : ((n : ℝ≥0) + 1) ≠ 0 := by positivity
    have hn := h ((n : ℝ≥0) + 1)⁻¹ (by positivity)
    rw [nonpos_iff_eq_zero, measure_eq_zero_iff_ae_notMem] at hn
    filter_upwards [hn] with a ha
    simpa [ENNReal.coe_inv hn0] using ha
  filter_upwards [h'] with a ha
  by_contra h0
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h0
  exact (ha n).not_gt ((ENNReal.inv_le_inv.mpr le_self_add).trans_lt hn)

/-- Markov's inequality for a product of two functions. -/
lemma mul_measure_inter_lt_le_lintegral_mul {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (a b : ℝ≥0∞) :
    a * b * μ ({x | a < f x} ∩ {x | b < g x}) ≤ ∫⁻ x, f x * g x ∂μ :=
  calc a * b * μ ({x | a < f x} ∩ {x | b < g x})
    _ ≤ a * b * μ {x | a * b ≤ f x * g x} := by
      gcongr
      exact fun x hx ↦ Set.mem_ofPred.mpr (mul_le_mul' hx.1.le hx.2.le)
    _ ≤ ∫⁻ x, f x * g x ∂μ := mul_meas_ge_le_lintegral₀ (hf.mul hg) _

end MeasureTheory
