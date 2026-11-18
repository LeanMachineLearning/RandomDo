/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Interfaces for polymorphic sampling

## Main definitions

* `HasBernoulli`: Bernoulli sampling with a probability parameter of type `P`.
* `HasUniform`: uniform sampling on the unit interval, with scalar type `R`.

These classes specify operations, without requiring monad laws or fixing a random generator.
A polymorphic `rdo` program requests only the operations it uses. Interpretation modules supply
the mathematical distributions for `Measure` and executable approximations for named samplers.
The classes do not assert that a pseudorandom implementation has the exact mathematical law.

`HasUniform` determines its scalar type from the interpretation. Bernoulli's parameter type is
an input: for example, the measure interpretation accepts both `ℝ` and `unitInterval`.
-/

@[expose] public section

namespace MeasureTheory

universe v

/-- Bernoulli sampling with probabilities represented by `P`.

For a probability in `[0, 1]`, `bernoulli p` samples a Boolean with success probability `p`,
subject to the numerical approximation of an executable interpretation. Each interpretation
specifies its behavior for parameters outside this interval.
-/
class HasBernoulli (m : (α : Type) → [MeasurableSpace α] → Type v) (P : Type) where
  /-- Draw a Boolean with success probability `p`. -/
  bernoulli : P → m Bool

/-- Uniform sampling on the unit interval, with scalar type determined by the interpretation.

The real interpretation is Lebesgue measure restricted to `[0, 1)`. Executable interpretations
sample a finite grid in this interval; their documentation specifies the generator and conversion.
-/
class HasUniform (m : (α : Type) → [MeasurableSpace α] → Type v)
    (R : outParam Type) [MeasurableSpace R] where
  /-- Draw a scalar uniformly on the unit interval. -/
  uniform : m R

end MeasureTheory
