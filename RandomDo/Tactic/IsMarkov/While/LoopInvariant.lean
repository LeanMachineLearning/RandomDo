/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Monad.While

/-!
# Invariants of `while` loops

An invariant of a `while` loop is a property of the states it carries on from and one of the states
it stops at, kept by almost every step of the loop.

## Main definitions

* `LoopInvariant f`: an invariant of the loop whose step is `f`.
-/

@[expose] public section

open MeasureTheory

namespace MeasurableSpaceMonadWhile

universe u

variable {σ : Type u} [MeasurableSpace σ] {f : σ → Measure (ForInStep σ)}

/-- An invariant of the loop whose step is `f`: a property `running` of the states the loop carries
on from, and a property `stopped` of the states it stops at, such that from a state satisfying
`running`, almost every step carries on from a state satisfying `running` or stops at a state
satisfying `stopped`. -/
structure LoopInvariant (f : σ → Measure (ForInStep σ)) where
  /-- The property of the states the loop carries on from. -/
  running : σ → Prop
  /-- The property of the states the loop stops at. -/
  stopped : σ → Prop := fun _ ↦ True
  /-- Almost every step from a state satisfying `running` stays in the invariant. -/
  step : ∀ s, running s → ∀ᵐ t ∂f s, ForInStep.casesOn (motive := fun _ ↦ Prop) t stopped running

namespace LoopInvariant

instance : CoeFun (LoopInvariant f) fun _ ↦ ForInStep σ → Prop where
  coe I t := ForInStep.casesOn t I.stopped I.running

end LoopInvariant

end MeasurableSpaceMonadWhile
