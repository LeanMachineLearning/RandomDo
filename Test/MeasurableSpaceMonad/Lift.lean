/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.MeasurableSpaceMonad.Lift

/-!
# Regression tests for measurable monad lifting

These tests check direct-lift measurability, inference through composed lifts, and the precedence
of native measurable lifts over the fallback to core's `MonadLiftT`.
-/

set_option linter.privateModule false

open MeasureTheory

namespace Test.MeasurableSpaceMonad.Lift

universe u v w z

section Measurability

variable {m : (α : Type u) → [MeasurableSpace α] → Type v}
  {n : (α : Type u) → [MeasurableSpace α] → Type w}
  [MeasurableSpaceMonad m] [MeasurableSpaceMonad n]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
  [direct : MeasurableSpaceMonadLift m n] [LawfulMeasurableSpaceMonadLift m n]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

-- Regression: stating the direct measurability law using the transitive projection made
-- `fun_prop` unable to find a theorem for the direct projection.
example (f : α → m β) (hf : Measurable f) :
    Measurable (fun a => direct.mMonadLift (f a)) := by
  fun_prop

variable {o : (α : Type u) → [MeasurableSpace α] → Type z}
  [MeasurableSpaceMonad o] [∀ α, [MeasurableSpace α] → MeasurableSpace (o α)]
  [MeasurableSpaceMonadLift n o] [LawfulMeasurableSpaceMonadLift n o]

-- Infer the intermediate monad and the lawful composite from direct instances; `fun_prop`
-- must also recognize the public `mLiftM` alias.
example (f : α → m β) (hf : Measurable f) :
    Measurable (fun a => mLiftM (n := o) (f a)) := by
  fun_prop

end Measurability

section CoreBridge

variable {m : Type u → Type v} {n : Type u → Type w}
  {α : Type u} [MeasurableSpace α]

-- A supplied core self-lift need not be identity. Measurable self-lifting must still use
-- the native identity instance, so these are not two definitionally identical candidates.
example [MonadLiftT m m] (x : Monad.toMeasurableSpaceMonad m α) :
    mMonadLift (n := Monad.toMeasurableSpaceMonad m) x = x := rfl

-- Native composition must also win when a core lift is available for the same endpoints.
example [MonadLiftT m n]
    [native : MeasurableSpaceMonadLift (Monad.toMeasurableSpaceMonad m)
      (Monad.toMeasurableSpaceMonad n)]
    (x : Monad.toMeasurableSpaceMonad m α) :
    mMonadLift (n := Monad.toMeasurableSpaceMonad n) x = native.mMonadLift x := rfl

-- If there is no native route, the bridge must use the supplied core lift.
example [MonadLiftT m n] (x : Monad.toMeasurableSpaceMonad m α) :
    mMonadLift (n := Monad.toMeasurableSpaceMonad n) x = monadLift (n := n) x := rfl

end CoreBridge

end Test.MeasurableSpaceMonad.Lift
