/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.Instances.Measure
public import RandomDo.Sampling.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# The measure interpretation of sampling

Bernoulli sampling uses `ProbabilityTheory.bernoulliMeasure`. Real probability parameters are
clamped to `[0, 1]`; parameters in `unitInterval` are used directly. Uniform sampling is Lebesgue
measure on `[0, 1)`, which has total mass one without an additional normalization factor.
-/

@[expose] public section

namespace MeasureTheory

open ProbabilityTheory HasBernoulli HasUniform

noncomputable instance : HasBernoulli Measure ℝ where
  bernoulli p := bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)

noncomputable instance : HasBernoulli Measure unitInterval where
  bernoulli p := bernoulliMeasure true false p

noncomputable instance : HasUniform Measure ℝ where
  uniform := volume.restrict (Set.Ico 0 1)

instance (p : ℝ) : IsProbabilityMeasure (bernoulli (m := Measure) p) :=
  inferInstanceAs (IsProbabilityMeasure
    (bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)))

instance (p : unitInterval) : IsProbabilityMeasure (bernoulli (m := Measure) p) :=
  inferInstanceAs (IsProbabilityMeasure (bernoulliMeasure true false p))

instance : IsProbabilityMeasure (uniform (m := Measure) : Measure ℝ) := ⟨by
  simp [uniform]⟩

/-- The Bernoulli measure depends measurably on its real probability parameter. -/
@[fun_prop] theorem measurable_bernoulli_real :
    Measurable (bernoulli (m := Measure) (P := ℝ)) := by
  dsimp [bernoulli, bernoulliMeasure]
  fun_prop

/-- The Bernoulli measure depends measurably on its unit-interval probability parameter. -/
@[fun_prop] theorem measurable_bernoulli_unitInterval :
    Measurable (bernoulli (m := Measure) (P := unitInterval)) := by
  dsimp [bernoulli, bernoulliMeasure]
  fun_prop

end MeasureTheory
