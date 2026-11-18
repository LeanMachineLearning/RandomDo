/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Float
public import RandomDo.MeasurableSpaceMonad.Defs
public import RandomDo.Sampling.Defs

/-!
# Shared floating-point sampling algorithms

`bernoulliOfUniform` constructs Bernoulli sampling from a unit-interval uniform action. It is
an ordinary function, so each named interpretation explicitly chooses whether to use it.
-/

@[expose] public section

namespace MeasureTheory

universe v

/-- Sample a Bernoulli by comparing a uniform draw in `[0, 1)` with `p`.

This consumes one uniform draw, including at probabilities zero and one. Parameters below zero
always return `false`, parameters above one always return `true`, and `NaN` returns `false`.
Finite-grid uniform sampling approximates the corresponding real Bernoulli distribution.
-/
@[inline] def bernoulliOfUniform
    {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    [HasUniform m Float] (p : Float) : m Bool :=
  mMap (fun x => Float.lt x p) HasUniform.uniform

end MeasureTheory
