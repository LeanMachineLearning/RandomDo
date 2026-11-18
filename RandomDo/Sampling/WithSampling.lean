/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom
public import RandomDo.MeasurableSpaceMonad.ForIn

/-!
# Named sampling interpretations

`WithSampling tag m` gives the measurable space monad `m` a separate choice of sampling
instances. It inherits `MeasurableSpaceMonad`, measurable spaces on computations, and
`LawfulMeasurableSpaceMonad` from `m`. It also inherits the unbounded-loop implementation
and its unfolding law when supplied by `m`. Sampling primitives are supplied explicitly for
each tag.

Define a new interpretation as an abbreviation for `WithSampling` with a fresh tag type.
Different tags allow different algorithms to use the same underlying state and monad without
sharing their primitive instances. The tag is only a type parameter: computations have exactly
the representation of `m`, with no additional state or runtime wrapper.

For interpretations over `PseudoRand`, `WithSampling.run` and `WithSampling.runWithSeed` provide
shared runners. The seeded runner takes the generator's initialization function explicitly.
-/

@[expose] public section

namespace MeasureTheory

universe u v

/-- A measurable space monad with sampling instances selected independently by `tag`. -/
def WithSampling (_tag : Type) (m : (α : Type u) → [MeasurableSpace α] → Type v)
    (α : Type u) [MeasurableSpace α] : Type v := m α

variable {tag : Type} {m : (α : Type u) → [MeasurableSpace α] → Type v}

instance [MeasurableSpaceMonad m] : MeasurableSpaceMonad (WithSampling tag m) :=
  inferInstanceAs (MeasurableSpaceMonad m)

instance {α : Type u} [MeasurableSpace α] [MeasurableSpace (m α)] :
    MeasurableSpace (WithSampling tag m α) := inferInstanceAs (MeasurableSpace (m α))

instance [MeasurableSpaceMonad m] [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    [LawfulMeasurableSpaceMonad m] : LawfulMeasurableSpaceMonad (WithSampling tag m) :=
  inferInstanceAs (LawfulMeasurableSpaceMonad m)

-- No separate core analogue: this forwards an existing implementation through our sampling
-- tag. It neither selects a new loop nor changes the runtime representation.
instance [MeasurableSpaceForIn m Lean.Loop Unit] :
    MeasurableSpaceForIn (WithSampling tag m) Lean.Loop Unit :=
  inferInstanceAs (MeasurableSpaceForIn m Lean.Loop Unit)

instance [MeasurableSpaceMonad m] [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    [MeasurableSpaceForIn m Lean.Loop Unit] [LawfulMeasurableSpaceLoop m] :
    LawfulMeasurableSpaceLoop (WithSampling tag m) :=
  inferInstanceAs (LawfulMeasurableSpaceLoop m)

namespace WithSampling

variable {σ : Type} {α : Type u} [MeasurableSpace α]

/-- Run a sampler from `s`, returning its result and the final generator state. -/
@[inline] def run (x : WithSampling tag (PseudoRand σ) α) (s : σ) : α × σ :=
  let (a, s) := StateT.run (x : PseudoRand σ α) ⟨s⟩
  (a, s.down)

/-- Run a sampler from a fresh generator initialized by `mkState seed`, returning only its
result. -/
@[inline] def runWithSeed (mkState : Nat → σ) (seed : Nat)
    (x : WithSampling tag (PseudoRand σ) α) : α :=
  (x.run (mkState seed)).1

end WithSampling

end MeasureTheory
