/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.MeasurableSpaceMonad.Defs

/-!
# Automation for measurable monads

These examples use an abstract monad so concrete instances cannot hide missing attributes.
They check the public `simp` and `fun_prop` interfaces, rather than restating the monad laws.
-/

open MeasureTheory

universe u v

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] [LawfulMeasurableSpaceMonad m]
  {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

-- Regression: registering core's `pure_bind` instead of `mPure_mBind` breaks this simplification.
example (a : α) {f : α → m β} {g : β → m γ} (hf : Measurable f) :
    ((mPure a : m α) >>=ₘ f) >>=ₘ g = f a >>=ₘ g := by
  simp [hf]

-- A trailing `return` is eliminated without naming the corresponding lemma.
example (x : m α) : x >>=ₘ mPure = x := by simp

-- Mapping after binding must use the registered measurability rules for both operations.
example {f : α → m β} {g : β → γ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x : m α => g <$>ₘ (x >>=ₘ f)) := by
  fun_prop

-- Composing `mPure` with a measurable function must also be handled automatically.
example {f : α → β} (hf : Measurable f) :
    Measurable (fun a : α => (mPure (f a) : m β)) := by
  fun_prop
