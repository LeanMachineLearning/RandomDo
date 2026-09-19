/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Gaussian distributions are sub-Gaussian

## Main results

* `hasSubgaussianMGF_gaussianReal`: centered, a Gaussian is sub-Gaussian with variance proxy its
  variance.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Centered, a Gaussian is sub-Gaussian with variance proxy its variance. -/
lemma hasSubgaussianMGF_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    HasSubgaussianMGF (fun x ↦ x - μ) v (gaussianReal μ v) := by
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · have := (integrable_exp_mul_gaussianReal (μ := μ) (v := v) t).const_mul (Real.exp (-(t * μ)))
    refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [← Real.exp_add]
    ring_nf
  · rw [mgf_gaussianReal ⟨by fun_prop, gaussianReal_map_sub_const μ⟩ t]
    simp

end ProbabilityTheory
