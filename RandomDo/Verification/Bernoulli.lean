/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Verification.Measure
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Verification rules for Bernoulli sampling

The weakest preexpectation of a Bernoulli sample is a weighted sum of its two postexpectations.
This specification is registered with Lean's stock `vcgen` tactic.
-/

@[expose] public section

open MeasureTheory Std.Internal.Do
open scoped ENNReal unitInterval ProbabilityTheory

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

@[simp] theorem wp_bernoulliMeasure (x y : α) (p : I) (Q : α → ℝ≥0∞) (E : EPost.Nil) :
    wp Ber(x, y, p) Q E =
      (unitInterval.toNNReal p : ℝ≥0∞) * Q x +
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) * Q y := by
  change (∫⁻ a, Q a ∂Ber(x, y, p)) = _
  simp only [bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  rfl

/-- Quantitative Hoare specification of a Bernoulli draw. -/
@[spec] theorem bernoulliMeasure_spec (x y : α) (p : I) (Q : α → ℝ≥0∞) (E : EPost.Nil) :
    Triple Ber(x, y, p)
      ((unitInterval.toNNReal p : ℝ≥0∞) * Q x +
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) * Q y) Q E :=
  ⟨(wp_bernoulliMeasure x y p Q E).ge⟩

end ProbabilityTheory
