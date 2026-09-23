/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Bernoulli
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

/-- A typeclass for monads that can draw from a Bernoulli distribution. -/
class HasBernoulli (m : (α : Type) → [MeasurableSpace α] → Type v) (P : Type) where
  /-- Draw `true` with probability `p`, and `false` otherwise. -/
  bernoulli : P → m Bool

/-- A probability outside `[0, 1]` is clamped to it. -/
noncomputable instance : HasBernoulli Measure ℝ where
  bernoulli p := bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)

/-- A probability outside `[0, 1]` is clamped to it, as in the instance on `Measure`. -/
instance : HasBernoulli RandM Float where
  bernoulli p := return (← NumLean.bernoulli p) == 1

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
