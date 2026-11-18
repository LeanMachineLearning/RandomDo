/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.NumLean.PCG64.MeasurableSpace
public import RandomDo.Sampling.Float
public import RandomDo.Sampling.WithSampling

/-!
# Sampling with `PCG64M`

## Main definitions

* `PCG64M`: a pure state sampler with its own primitive instances.
* `PCG64M.run`: run from an explicit generator state and return the value and final state.
* `PCG64M.runWithSeed`: sample from a fresh generator initialized with a given seed.

`PCG64M` is an abbreviation for `WithSampling PCG64M.Tag (PseudoRand NumLean.PCG64)`.
The shared wrapper supplies the measurable monad structure and laws, while the tag selects this
interpretation's sampling primitives. The runners are aliases of the shared implementations;
`runWithSeed` selects `mkPCG64` to initialize the generator.

Uniform sampling uses NumLean's PCG64 conversion: the top 53 bits of one 64-bit output are scaled
by `2⁻⁵³`. This preserves NumLean's uniform stream for the same seed. Bernoulli sampling uses
`bernoulliOfUniform`; it does not use NumLean's binomial algorithm or promise the same Bernoulli
stream. Both primitives thread the state and do not split the generator.
-/

@[expose] public section

namespace MeasureTheory

open NumLean

universe u

/-- Type-level label for the standard PCG64 sampling primitives. -/
inductive PCG64M.Tag

/-- A pure `PCG64` sampler with independently selected primitive instances. -/
abbrev PCG64M := WithSampling PCG64M.Tag (PseudoRand PCG64)

instance : HasUniform PCG64M Float where
  uniform := NumLean.random (m := Id)

instance : HasBernoulli PCG64M Float where
  bernoulli := bernoulliOfUniform

namespace PCG64M

@[inherit_doc WithSampling.run]
abbrev run {α : Type u} [MeasurableSpace α] : PCG64M α → PCG64 → α × PCG64 :=
  WithSampling.run

/-- Run a sampler from a fresh seeded generator, returning only its result. -/
abbrev runWithSeed {α : Type u} [MeasurableSpace α] : Nat → PCG64M α → α :=
  WithSampling.runWithSeed @mkPCG64

end PCG64M

end MeasureTheory
