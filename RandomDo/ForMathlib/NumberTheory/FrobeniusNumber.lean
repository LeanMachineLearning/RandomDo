/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Sets of natural numbers closed under addition

## Main statements

* `Nat.exists_forall_ge_mem_of_setGcd_eq_one`: a set of natural numbers which is closed under
  addition and whose greatest common divisor is 1 contains all large enough natural numbers.
-/

@[expose] public section

namespace Nat

/-- A set of natural numbers which is closed under addition and whose greatest common divisor
is 1 contains all large enough natural numbers. -/
lemma exists_forall_ge_mem_of_setGcd_eq_one {s : Set ℕ}
    (hadd : ∀ a ∈ s, ∀ b ∈ s, a + b ∈ s) (hs : Nat.setGcd s = 1) : ∃ N, ∀ n ≥ N, n ∈ s := by
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge s
  have hsub : ∀ m ∈ AddSubmonoid.closure s, m = 0 ∨ m ∈ s := by
    intro m hm
    induction hm using AddSubmonoid.closure_induction with
    | mem m hm => exact .inr hm
    | zero => exact .inl rfl
    | add a b _ _ ha hb =>
      rcases ha with rfl | ha
      · simpa using hb
      · rcases hb with rfl | hb
        · simpa using Or.inr ha
        · exact .inr (hadd a ha b hb)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  rcases hsub n (hN n (le_of_max_le_left hn) (by simp [hs])) with rfl | h
  · simp at hn
  · exact h

end Nat
