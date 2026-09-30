/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import RandomDo.ForMathlib.MeasureTheory.Measure.GiryMonad

/-!
# Binding a Bernoulli distribution

-/

@[expose] public section

open MeasureTheory Measure unitInterval
open scoped ENNReal

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Binding a Bernoulli distribution on a space whose points are measurable: the continuation needs
no measurability, and the two weights are real numbers, so that `simp` can use it and `norm_num`
can compute with the result. -/
@[simp]
lemma bernoulliMeasure_bind [MeasurableSingletonClass X] (x y : X) (p : I) (g : X → Measure Y) :
    Ber(x, y, p).bind g = ENNReal.ofReal p • g x + ENNReal.ofReal (1 - p) • g y := by
  have h (q : I) : ((toNNReal q : NNReal) : ℝ≥0∞) = ENNReal.ofReal q := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg q.2.1]
    rfl
  rw [bernoulliMeasure_def, bind_add ((aemeasurable_dirac.smul_measure _).add_measure
    (aemeasurable_dirac.smul_measure _)), bind_smul, bind_smul, dirac_bind', dirac_bind']
  change (toNNReal p : ℝ≥0∞) • g x + (toNNReal (σ p) : ℝ≥0∞) • g y = _
  rw [h, h, coe_symm_eq]

end ProbabilityTheory
