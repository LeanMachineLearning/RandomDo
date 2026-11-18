/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.MeasurableSpaceMonad.ForIn

/-!
# Inference and simplification for measurable iteration

A membership-aware instance must supply ordinary iteration, even when the collection, element,
state, and computation universes differ. No measurable structure on the collection or its
individual elements is assumed.
-/

open MeasureTheory

universe uρ uι u v

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} {ρ : Type uρ} {ι : Type uι}
  [d : Membership ι ρ] [MeasurableSpaceForIn' m ρ ι d] {β : Type u} [MeasurableSpace β]

example : MeasurableSpaceForIn m ρ ι := inferInstance

-- `simp` removes an unused membership proof without explicitly invoking the conversion lemma.
example (xs : ρ) (init : β) (f : (a : ι) → a ∈ xs → β → m (ForInStep β))
    (g : ι → β → m (ForInStep β)) (h : ∀ a ha b, f a ha b = g a b) :
    mForIn' xs init f = mForIn xs init g := by
  simp [h]

-- A fresh matcher in an importing module must be handled by `fun_prop`.
example {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {g : α → ForInStep β} {done yield : β → γ}
    (hg : Measurable g) (hd : Measurable done) (hy : Measurable yield) :
    Measurable (fun a => match g a with | .done b => done b | .yield b => yield b) := by
  fun_prop
