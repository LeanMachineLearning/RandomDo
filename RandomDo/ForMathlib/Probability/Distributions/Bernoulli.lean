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

lemma bernoulliMeasure_bind (x y : X) (p : I) {g : X → Measure Y} (hg : Measurable g) :
    Ber(x, y, p).bind g = (toNNReal p : ℝ≥0∞) • g x + (toNNReal (σ p) : ℝ≥0∞) • g y := by
  rw [bernoulliMeasure_def, bind_add hg.aemeasurable, bind_smul, bind_smul, dirac_bind hg,
    dirac_bind hg]
  rfl

end ProbabilityTheory
