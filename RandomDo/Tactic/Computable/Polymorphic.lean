/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import RandomDo.Monad.Instances
public import RandomDo.NumLean.Distributions

/-!

-/

@[expose] public section

open MeasureTheory ProbabilityTheory NumLean

universe v

/-- A typeclass for monads that can draw from a Gaussian distribution. -/
class HasGaussian (m : (α : Type) → [MeasurableSpace α] → Type v)
   (α β : Type*) (R : Type) [MeasurableSpace R] where
  gaussian : α → β → m R

noncomputable instance : HasGaussian Measure ℝ NNReal ℝ where
  gaussian μ v := gaussianReal μ v

/-- The monad that samples, seen as a `MeasurableSpaceMonad`. -/
abbrev RandM := Monad.toMeasurableSpaceMonad (RandPCG IO)

instance : MeasurableSpace Float := ⊤

instance : HasGaussian RandM Float Float Float where
  gaussian μ v := normal' μ v
