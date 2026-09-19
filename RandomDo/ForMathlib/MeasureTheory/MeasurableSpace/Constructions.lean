/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of `Fin.snoc`

## Main results

* `Measurable.finSnoc`: appending an element to a tuple is measurable, the measurable counterpart
  of `Continuous.finSnoc`.
-/

@[expose] public section

variable {α : Type*} [MeasurableSpace α] {n : ℕ} {X : Fin (n + 1) → Type*}
  [∀ i, MeasurableSpace (X i)]

@[fun_prop]
lemma Measurable.finSnoc {f : α → ∀ j : Fin n, X j.castSucc} {g : α → X (Fin.last n)}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a ↦ Fin.snoc (f a) (g a) := by
  refine measurable_pi_iff.2 fun i ↦ ?_
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.snoc_last] using hg
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp hf
