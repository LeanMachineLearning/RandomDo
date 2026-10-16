/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# The monoid of kernels

Lemmas about the monoid structure on `Kernel α α` given by composition, and about the powers
`κ ^ n` of a kernel `κ : Kernel α α`.

## Main statements

* `Kernel.one_eq_id`, `Kernel.mul_eq_comp`: the unit of the monoid is `Kernel.id` and its
  multiplication is the composition `∘ₖ`.
* Instances: `κ ^ n` is a Markov kernel (resp. a zero or Markov kernel, a finite kernel,
  an s-finite kernel) if `κ` is.
* `Kernel.pow_add_one`, `Kernel.pow_add_one'`: `κ ^ (n + 1) = κ ^ n ∘ₖ κ = κ ∘ₖ κ ^ n`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α}

@[simp] lemma one_eq_id : (1 : Kernel α α) = Kernel.id := rfl

@[simp] lemma mul_eq_comp (η κ : Kernel α α) : η * κ = η ∘ₖ κ := rfl

instance IsMarkovKernel.pow (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero, one_eq_id]; infer_instance
  | succ n ih => rw [pow_succ, mul_eq_comp]; infer_instance

instance IsZeroOrMarkovKernel.pow (κ : Kernel α α) [IsZeroOrMarkovKernel κ] (n : ℕ) :
    IsZeroOrMarkovKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero, one_eq_id]; infer_instance
  | succ n ih => rw [pow_succ, mul_eq_comp]; infer_instance

instance IsFiniteKernel.pow (κ : Kernel α α) [IsFiniteKernel κ] (n : ℕ) :
    IsFiniteKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero, one_eq_id]; infer_instance
  | succ n ih => rw [pow_succ, mul_eq_comp]; infer_instance

instance IsSFiniteKernel.pow (κ : Kernel α α) [IsSFiniteKernel κ] (n : ℕ) :
    IsSFiniteKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero, one_eq_id]; infer_instance
  | succ n ih => rw [pow_succ, mul_eq_comp]; infer_instance

lemma pow_add_one (κ : Kernel α α) (n : ℕ) : κ ^ (n + 1) = (κ ^ n) ∘ₖ κ := by
  rw [pow_add, pow_one]

lemma pow_add_one' (κ : Kernel α α) (n : ℕ) : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
  rw [add_comm, pow_add, pow_one]

end ProbabilityTheory.Kernel
