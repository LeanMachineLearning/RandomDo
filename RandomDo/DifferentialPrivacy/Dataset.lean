/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Datasets, adjacency, and sensitivity

Datasets are finite sequences of arbitrary length; order and repeated records are retained.
Insertion/removal may occur at any position. Replacement adjacency has a separate name, since
its sensitivity and sample-size assumptions differ from insertion/removal adjacency.
-/

@[expose] public section

namespace DifferentialPrivacy

universe u v

/-- A finite sequence of records with no fixed bound on its size. -/
abbrev Dataset (α : Type u) := List α

namespace Dataset

variable {α : Type u}

/-- One record was inserted at an arbitrary position. -/
def InsertOne (x y : Dataset α) : Prop :=
  ∃ l r a, x = l ++ r ∧ y = l ++ a :: r

/-- Unbounded adjacency: insert or delete exactly one record. -/
def AddRemove (x y : Dataset α) : Prop := InsertOne x y ∨ InsertOne y x

/-- Bounded adjacency: replace one record at an arbitrary position. It is harmless to allow
the replacement record to equal the original record. -/
def ReplaceOne (x y : Dataset α) : Prop :=
  ∃ l r a b, x = l ++ a :: r ∧ y = l ++ b :: r

theorem AddRemove.symm {x y : Dataset α} (h : AddRemove x y) : AddRemove y x := Or.symm h

theorem ReplaceOne.symm {x y : Dataset α} (h : ReplaceOne x y) : ReplaceOne y x := by
  obtain ⟨l, r, a, b, rfl, rfl⟩ := h
  exact ⟨l, r, b, a, rfl, rfl⟩

theorem InsertOne.length {x y : Dataset α} (h : InsertOne x y) : y.length = x.length + 1 := by
  obtain ⟨l, r, a, rfl, rfl⟩ := h
  simp [Nat.add_assoc]

theorem AddRemove.length {x y : Dataset α} (h : AddRemove x y) :
    y.length = x.length + 1 ∨ x.length = y.length + 1 :=
  h.elim (fun h ↦ Or.inl h.length) (fun h ↦ Or.inr h.length)

theorem AddRemove.irrefl (x : Dataset α) : ¬ AddRemove x x := by
  intro h
  rcases h.length with h | h <;> omega

theorem ReplaceOne.length {x y : Dataset α} (h : ReplaceOne x y) : x.length = y.length := by
  obtain ⟨l, r, a, b, rfl, rfl⟩ := h
  simp

/-- Restrict an adjacency relation by a public lower bound on both dataset sizes. -/
def AtLeast (n : ℕ) (adj : Dataset α → Dataset α → Prop) (x y : Dataset α) : Prop :=
  n ≤ x.length ∧ n ≤ y.length ∧ adj x y

end Dataset

variable {X : Type u} {E : Type v} [SeminormedAddCommGroup E]

/-- A global sensitivity bound for a query. With `E = EuclideanSpace ℝ (Fin d)`, this uses
the Euclidean (ℓ₂) norm, not the sup norm on a function space. -/
def HasSensitivity (adj : X → X → Prop) (f : X → E) (Δ : ℝ) : Prop :=
  ∀ ⦃x y⦄, adj x y → ‖f x - f y‖ ≤ Δ

theorem HasSensitivity.mono {adj : X → X → Prop} {f : X → E} {Δ Δ' : ℝ}
    (h : HasSensitivity adj f Δ) (hΔ : Δ ≤ Δ') : HasSensitivity adj f Δ' :=
  fun _ _ hxy ↦ (h hxy).trans hΔ

/-- An upper bound on the diameter of an embedded record domain. -/
def HasDiameter {α : Type*} (f : α → E) (D : ℝ) : Prop := ∀ a b, ‖f a - f b‖ ≤ D

end DifferentialPrivacy
