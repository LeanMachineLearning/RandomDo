/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import RandomDo.Monad.Instances
public import RandomDo.NumLean.Distributions

/-!
# Polymorphic `rdo` programs

A program written over an arbitrary `MeasurableSpaceMonad` `m`, drawing through the classes of this
file, is read at `m := Measure` to prove things about it and run at `m := RandM` to sample from it.
Each class has an instance of each kind: the distribution of Mathlib on `ℝ`, and the sampler of
`NumLean` on `Float`. The scalar classes `HasExp`, `HasLog` and `HasSqrt` do the same for the
functions a program computes with.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory NumLean

universe v

/-- A typeclass for monads that can draw from a Gaussian distribution. -/
class HasGaussian (m : (α : Type) → [MeasurableSpace α] → Type v)
   (α β : Type*) (R : Type) [MeasurableSpace R] where
  /-- Draw a sample from a Gaussian distribution with mean `μ` and variance `v`. -/
  gaussian : α → β → m R

noncomputable instance : HasGaussian Measure ℝ NNReal ℝ where
  gaussian μ v := gaussianReal μ v

/-- The monad that samples, seen as a `MeasurableSpaceMonad`. -/
abbrev RandM := Monad.toMeasurableSpaceMonad (RandPCG IO)

instance instMeasurableSpaceFloat : MeasurableSpace Float := ⊤

instance : HasGaussian RandM Float Float Float where
  gaussian μ v := normal' μ v

/-- A typeclass for monads that can draw from a uniform distribution on a real interval. -/
class HasUniform (m : (α : Type) → [MeasurableSpace α] → Type v)
    (R : Type) [MeasurableSpace R] where
  /-- Draw uniformly between `low` and `high`. For `low < high`, the interval is `[low, high)`;
  equal bounds return that value. The bounds must satisfy `low ≤ high`. -/
  uniform : R → R → m R

/-- Normalized Lebesgue measure on `[low, high)`, or a point mass when the bounds coincide.
Reversed bounds give the zero measure. -/
noncomputable instance : HasUniform Measure ℝ where
  uniform low high := if low = high then Measure.dirac low else cond volume (Set.Ico low high)

/-- Sample using `NumLean.uniform`, which raises an error for reversed bounds. -/
instance : HasUniform RandM Float where
  uniform low high := NumLean.uniform low high

/-- A uniform distribution with ordered bounds is a probability measure, including equal bounds. -/
lemma HasUniform.isProbabilityMeasure_uniform_real {low high : ℝ} (h : low ≤ high) :
    IsProbabilityMeasure (HasUniform.uniform (m := Measure) low high) := by
  by_cases heq : low = high
  · simp only [HasUniform.uniform, heq, ite_true]
    infer_instance
  · simp only [HasUniform.uniform, heq, ite_false]
    apply cond_isProbabilityMeasure_of_finite
    · simpa only [Real.volume_Ico, ne_eq, ENNReal.ofReal_eq_zero, not_le] using
        sub_pos.mpr (lt_of_le_of_ne h heq)
    · rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top

instance (low high : ℝ) [Fact (low ≤ high)] :
    IsProbabilityMeasure (HasUniform.uniform (m := Measure) low high) :=
  HasUniform.isProbabilityMeasure_uniform_real Fact.out

/-- A typeclass for monads that can draw from a Bernoulli distribution. -/
class HasBernoulli (m : (α : Type) → [MeasurableSpace α] → Type v) (P : Type) where
  /-- Draw `true` with probability `p`, and `false` otherwise. -/
  bernoulli : P → m Bool

/-- A probability outside `[0, 1]` is clamped to it. -/
noncomputable instance : HasBernoulli Measure ℝ where
  bernoulli p := bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)

/-- A probability outside `[0, 1]` is clamped to it, as in the instance on `Measure`.
`NaN` raises an error. -/
instance : HasBernoulli RandM Float where
  bernoulli p := do
    let p := if p < 0.0 then 0.0 else if 1.0 < p then 1.0 else p
    return (← NumLean.bernoulli p) == 1

/-- A typeclass for scalars with an exponential. -/
class HasExp (R : Type) where
  /-- The exponential. -/
  exp : R → R

noncomputable instance : HasExp ℝ := ⟨Real.exp⟩

@[fun_prop]
lemma HasExp.measurable_exp_real : Measurable (HasExp.exp : ℝ → ℝ) := Real.measurable_exp

instance : HasExp Float := ⟨Float.exp⟩

/-- A typeclass for scalars with a logarithm. -/
class HasLog (R : Type) where
  /-- The logarithm. -/
  log : R → R

noncomputable instance : HasLog ℝ := ⟨Real.log⟩

@[fun_prop]
lemma HasLog.measurable_log_real : Measurable (HasLog.log : ℝ → ℝ) := Real.measurable_log

instance : HasLog Float := ⟨Float.log⟩

/-- A typeclass for scalars with a square root. -/
class HasSqrt (R : Type) where
  /-- The square root. -/
  sqrt : R → R

noncomputable instance : HasSqrt ℝ := ⟨Real.sqrt⟩

@[fun_prop]
lemma HasSqrt.measurable_sqrt_real : Measurable (HasSqrt.sqrt : ℝ → ℝ) :=
  Real.continuous_sqrt.measurable

instance : HasSqrt Float := ⟨Float.sqrt⟩

/-- A natural number as a `Float`, so that programs polymorphic in the scalars can cast counts. -/
instance instNatCastFloat : NatCast Float := ⟨Nat.toFloat⟩
