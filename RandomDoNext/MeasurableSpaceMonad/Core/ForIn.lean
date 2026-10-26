/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDoNext.MeasurableSpaceMonad.Core.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Polymorphic iteration interfaces

`MeasurableSpaceForIn` and `MeasurableSpaceForIn'` are the measurable-space counterparts of
Lean's iteration classes. The accumulator has a measurable space, and each step either yields
an updated accumulator or stops the loop.

The measurable spaces on `ForInStep` and `Option`, and the adapter from membership-aware
iteration, are generic in the monad. Implementations for particular collections or monads belong
in separate modules.
No unbounded-loop operation or semantics is chosen here.

Adapted from `RandomDo/Monad/MeasurableSpace.lean` and the optional-value instance in
`RandomDo/Measurable.lean` at main commit `150ecab`.
-/

@[expose] public section

namespace RandomDo

universe uρ uα u v

variable {α : Type u} [mα : MeasurableSpace α] (m : (α : Type u) → [MeasurableSpace α] → Type v)

/-- The measurable space on optional results used to carry an early return.
A set of optional values is measurable exactly when its `some` preimage is measurable. -/
instance instMeasurableSpaceOption : MeasurableSpace (Option α) := mα.map some

/-- The disjoint-union measurable space on the two possible loop-step outcomes. -/
instance instMeasurableSpaceForInStep {β : Type u} [mβ : MeasurableSpace β] :
    MeasurableSpace (ForInStep β) := mβ.map ForInStep.yield ⊓ mβ.map ForInStep.done

/--
Monadic iteration in `rdo`-blocks, using the `for x in xs` notation.
-/
class MeasurableSpaceForIn (ρ : Type uρ) (α : outParam (Type uα)) where
  /--
  Monadically iterates over the contents of a collection `xs`, with a local state `b` and the
  possibility of early termination.
  -/
  forIn {β : Type u} [MeasurableSpace β] (xs : ρ) (b : β)
    (f : α → β → m (ForInStep β)) : m β

/--
Monadic iteration in `rdo`-blocks with a membership proof, using the `for h : x in xs` notation.
-/
class MeasurableSpaceForIn' (ρ : Type uρ) (α : outParam (Type uα))
    (d : outParam (Membership α ρ)) where
  /--
  Monadically iterates over the contents of a collection `xs`, with a local state `b` and the
  possibility of early termination. At each iteration, the body of the loop is provided with a proof
  that the current element is in the collection.
  -/
  forIn' {β : Type u} [MeasurableSpace β] (xs : ρ) (b : β)
    (f : (a : α) → a ∈ xs → β → m (ForInStep β)) : m β

@[simps]
instance (priority := 500) instMeasurableSpaceForInOfForIn'
    {ρ : Type uρ} {α : Type uα} {d : Membership α ρ} [MeasurableSpaceForIn' m ρ α d] :
    MeasurableSpaceForIn m ρ α where
  forIn x b f := MeasurableSpaceForIn'.forIn' x b fun a _ s => f a s

end RandomDo
