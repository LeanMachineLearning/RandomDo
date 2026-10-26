/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.MeasurableSpaceMonad.Core

/-!
# Polymorphic reasoning checks

Exercise the public simplifier and measurability interfaces with an abstract monad and
independent result/computation universes. No concrete interpretation is installed.
-/

open RandomDo MeasurableSpacePure MeasurableSpaceBind MeasurableSpaceFunctor

universe u v

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] [LawfulMeasurableSpaceMonad m]
  {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

-- This uses the registered measurable-space simp rules, not ordinary monad laws.
example (a : α) {f : α → m β} {g : β → m γ}
    (hf : Measurable f) :
    ((mPure a : m α) >>=ₘ f) >>=ₘ g = f a >>=ₘ g := by
  simp [hf]

example (x : m α) : x >>=ₘ mPure = x := by simp

example (x : m α) {f : α → β} {g : β → γ}
    (hf : Measurable f) (hg : Measurable g) :
    x >>=ₘ (fun a => mPure (g (f a))) = g <$>ₘ (f <$>ₘ x) := by
  simp (disch := fun_prop) only [LawfulMeasurableSpaceMonad.mBind_mPure_comp, mMap_mMap]

example {f : α → m β} {g : β → γ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x : m α => g <$>ₘ (x >>=ₘ f)) := by
  fun_prop

example {f : α → β} (hf : Measurable f) :
    Measurable (fun a : α => (mPure (f a) : m β)) := by
  fun_prop
