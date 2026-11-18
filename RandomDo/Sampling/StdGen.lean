/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.Sampling.Float
public import RandomDo.Sampling.WithSampling

/-!
# Sampling with `StdGenM`

## Main definitions

* `StdGenM`: a pure state sampler with its own primitive instances.
* `StdGenM.run`: run from an explicit generator state and return the value and final state.
* `StdGenM.runWithSeed`: sample from a fresh generator initialized with a given seed.

`StdGenM` is an abbreviation for `WithSampling StdGenM.Tag (PseudoRand StdGen)`.
The shared wrapper supplies the measurable monad structure and laws, while the tag selects this
interpretation's sampling primitives. The runners are aliases of the shared implementations;
`runWithSeed` selects `mkStdGen` to initialize the generator.

Uniform sampling uses core's `randNat` through `Random.rand (Fin (2 ^ 53))`, then scales by
`2⁻⁵³` to obtain a `Float` in `[0, 1)`. It inherits core's approximate bounded sampling algorithm,
including its small modulo bias; it is not an exact continuous uniform distribution. Bernoulli
sampling uses `bernoulliOfUniform`. Both primitives thread the state without splitting it.
-/

@[expose] public section

namespace MeasureTheory

universe u

/-- Type-level label for the standard StdGen sampling primitives. -/
inductive StdGenM.Tag

/-- A pure `StdGen` sampler with independently selected primitive instances. -/
abbrev StdGenM := WithSampling StdGenM.Tag (PseudoRand StdGen)

instance : HasUniform StdGenM Float where
  uniform := (do
    let x ← Random.rand (Fin (2 ^ 53))
    return x.val.toFloat * (Float.ofBits <| 0x3CA <<< (52 : UInt64)) : Rand Float)

instance : HasBernoulli StdGenM Float where
  bernoulli := bernoulliOfUniform

namespace StdGenM

@[inherit_doc WithSampling.run]
abbrev run {α : Type u} [MeasurableSpace α] : StdGenM α → StdGen → α × StdGen :=
  WithSampling.run

/-- Run a sampler from a fresh seeded generator, returning only its result. -/
abbrev runWithSeed {α : Type u} [MeasurableSpace α] : Nat → StdGenM α → α :=
  WithSampling.runWithSeed @mkStdGen

end StdGenM

end MeasureTheory
