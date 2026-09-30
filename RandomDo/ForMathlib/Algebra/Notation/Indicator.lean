/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Algebra.Notation.Indicator

/-!
# The indicator of a set given by a predicate

-/

@[expose] public section

namespace Set

variable {α M : Type*} [Zero M]

@[simp]
lemma indicator_setOf_apply (p : α → Prop) (f : α → M) (a : α) [Decidable (p a)] :
    {x | p x}.indicator f a = if p a then f a else 0 := by
  simp [indicator_apply]

end Set
