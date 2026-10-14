/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.ForMathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Powers of kernels

Lemmas about the powers `κ ^ n` of a kernel `κ : Kernel α α` for the monoid structure given by
composition.

## Main statements

* `Kernel.pow_add_apply`: `(κ ^ (m + n)) a = (κ ^ m) ∘ₘ (κ ^ n) a`.
* `Kernel.pow_add_comp`: `(κ ^ (m + n)) ∘ₘ μ = (κ ^ m) ∘ₘ ((κ ^ n) ∘ₘ μ)`.
* `Kernel.pow_succ_apply_pos_iff`: a point reaches a set with positive probability in `n + 1`
  steps iff its first step goes with positive probability to the set of points which reach it
  with positive probability in `n` steps.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {μ : Measure α}

instance [IsMarkovKernel κ] (n : ℕ) : IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((κ ^ n) ∘ₖ κ))

instance [IsFiniteKernel κ] (n : ℕ) : IsFiniteKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsFiniteKernel Kernel.id)
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsFiniteKernel ((κ ^ n) ∘ₖ κ))

instance [IsSFiniteKernel κ] (n : ℕ) : IsSFiniteKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsSFiniteKernel Kernel.id)
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsSFiniteKernel ((κ ^ n) ∘ₖ κ))

lemma pow_zero_apply (κ : Kernel α α) (a : α) : (κ ^ 0) a = Measure.dirac a := by
  rw [pow_zero]; exact Kernel.id_apply a

lemma pow_add_apply (κ : Kernel α α) (m n : ℕ) (a : α) :
    (κ ^ (m + n)) a = (κ ^ m) ∘ₘ (κ ^ n) a := by
  rw [pow_add, comp_apply]

lemma pow_succ_apply (κ : Kernel α α) (n : ℕ) (a : α) : (κ ^ (n + 1)) a = (κ ^ n) ∘ₘ κ a := by
  rw [pow_add_apply, pow_one]

lemma pow_succ_apply' (κ : Kernel α α) (n : ℕ) (a : α) : (κ ^ (n + 1)) a = κ ∘ₘ (κ ^ n) a := by
  rw [add_comm, pow_add_apply, pow_one]

lemma pow_add_comp (κ : Kernel α α) (m n : ℕ) (μ : Measure α) :
    (κ ^ (m + n)) ∘ₘ μ = (κ ^ m) ∘ₘ ((κ ^ n) ∘ₘ μ) := by
  rw [pow_add, Measure.comp_assoc]

lemma pow_succ_comp (κ : Kernel α α) (n : ℕ) (μ : Measure α) :
    (κ ^ (n + 1)) ∘ₘ μ = (κ ^ n) ∘ₘ (κ ∘ₘ μ) := by
  rw [pow_add_comp, pow_one]

lemma pow_succ_comp' (κ : Kernel α α) (n : ℕ) (μ : Measure α) :
    (κ ^ (n + 1)) ∘ₘ μ = κ ∘ₘ ((κ ^ n) ∘ₘ μ) := by
  rw [add_comm, pow_add_comp, pow_one]

lemma pow_zero_comp (κ : Kernel α α) (μ : Measure α) : (κ ^ 0 : Kernel α α) ∘ₘ μ = μ := by
  rw [pow_zero]; exact Measure.id_comp

/-- A point `y` reaches the measurable set `C` with positive probability in `n + 1` steps iff
its first step goes with positive probability to the set of points which reach `C` with positive
probability in `n` steps. -/
lemma pow_succ_apply_pos_iff {C : Set α} (hC : MeasurableSet C) {n : ℕ} {y : α} :
    0 < (κ ^ (n + 1)) y C ↔ 0 < κ y {z | 0 < (κ ^ n) z C} := by
  rw [pow_succ_apply, Measure.comp_apply_pos_iff hC]

/-- The measurable set `C` is reached from the measure `μ` with positive probability in `n + m`
steps iff after `m` steps, the set of points which reach `C` with positive probability in `n`
steps has positive measure. -/
lemma pow_add_comp_apply_pos_iff {C : Set α} (hC : MeasurableSet C) {m n : ℕ} :
    0 < ((κ ^ (n + m)) ∘ₘ μ) C ↔ 0 < ((κ ^ m) ∘ₘ μ) {y | 0 < (κ ^ n) y C} := by
  rw [pow_add_comp, Measure.comp_apply_pos_iff hC]

end ProbabilityTheory.Kernel
