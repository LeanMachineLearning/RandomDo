/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.MeasurableSpaceMonad.Instances.Measure
import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom
import RandomDo.RDo.Core

/-!
# Integration of the supported monads with `rdo`

These tests check the meaning of a measure program, state threading in a sampler, and
measurability automation through the sampler's lawful instance.
-/

open MeasureTheory

universe u v

-- Returning a measurable function of a draw denotes its pushforward measure.
example {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f) :
    (rdo
      let a ← μ
      return f a : Measure β) = μ.map f :=
  Measure.bind_dirac_eq_map μ hf

-- The transformer preserves both draws, the final state, and the base monad's effects.
-- No measurable space or countability assumption is needed on the generator for execution.
example {σ : Type} [RandomGen σ] {m : Type → Type v} [Monad m] (s : ULift σ) :
    (rdo
      let a ← Rand.next
      let b ← Rand.next
      return (a, b) : PseudoRandT σ m (Nat × Nat)) s =
    (do
      let a ← Rand.next
      let b ← Rand.next
      return (a, b) : RandGT σ m (Nat × Nat)) s := rfl

-- Measurability automation works for any countable state type with measurable singletons.
example {σ : Type} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (f : α → PseudoRand σ β) (g : β → γ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x : PseudoRand σ α => (rdo
      let a ← x
      let b ← f a
      return g b : PseudoRand σ γ)) := by
  fun_prop

-- The transformer uses the measurable laws of its base, without requiring core LawfulMonad.
example {σ : Type} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    {m : Type u → Type v} [Monad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (Monad.toMeasurableSpaceMonad m α)]
    [LawfulMeasurableSpaceMonad (Monad.toMeasurableSpaceMonad m)]
    {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (f : α → PseudoRandT σ m β) (g : β → γ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x : PseudoRandT σ m α => (rdo
      let a ← x
      let b ← f a
      return g b : PseudoRandT σ m γ)) := by
  fun_prop

-- Instance inference also works with a non-Id base: another state transformer.
example : LawfulMeasurableSpaceMonad (PseudoRandT Nat (RandGT Bool Id)) := inferInstance
