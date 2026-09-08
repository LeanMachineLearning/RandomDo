/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Tactic.Computable.Defs
public import RandomDo.NumLean.Distributions
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Computable counterparts of the pieces an `rdo` program is made of

The `@[computable]` attribute translates a program by replacing each piece it is made of by the
counterpart recorded here through `@[computable_as]`. There is one entry per piece the programs of
`RandomDo.Tactic.Computable.Example` are built from: the two types their values live in, and the
one distribution they draw from.
-/

@[expose] public section

/-! ## Types -/

attribute [computable_as Float] Real
attribute [computable_as Float] NNReal

/-! ## Distributions -/

attribute [computable_as NumLean.normal'] ProbabilityTheory.gaussianReal

def bernoulliChoice (α : Type) [MeasurableSpace α] (x y : α) (p : Float) :
    NumLean.RandPCG IO α := do
  return if (← NumLean.bernoulli p) == 1 then x else y

attribute [computable_as bernoulliChoice] ProbabilityTheory.bernoulliMeasure

/-! ## Classical functions -/

attribute [computable_as Float.sqrt] Real.sqrt

attribute [computable_as Float.log] Real.log

attribute [computable_as Float.exp] Real.exp
