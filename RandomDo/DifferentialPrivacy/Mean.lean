/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.DifferentialPrivacy.Dataset
import Mathlib.Tactic

/-!
# Sensitivity of the empirical mean

The query is defined on lists of records mapped into a real normed space. Its sensitivity
theorems apply to nonempty datasets with a public lower bound on size. The value at the empty
dataset is zero by convention; a diameter bound alone does not control its distance to the
domain. In particular, the theorems deliberately do not cover empty/nonempty adjacency.
-/

@[expose] public section

namespace DifferentialPrivacy

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Arithmetic mean of the embedded records, with value zero on the empty dataset. -/
noncomputable def empiricalMean (f : α → E) (x : Dataset α) : E :=
  (x.length : ℝ)⁻¹ • (x.map f).sum

@[simp] theorem empiricalMean_nil (f : α → E) : empiricalMean f [] = 0 := by
  simp [empiricalMean]

@[simp] theorem empiricalMean_singleton (f : α → E) (a : α) :
    empiricalMean f [a] = f a := by
  simp [empiricalMean]

theorem empiricalMean_perm (f : α → E) {x y : Dataset α} (h : x.Perm y) :
    empiricalMean f x = empiricalMean f y := by
  rw [empiricalMean, empiricalMean, h.length_eq, (h.map f).sum_eq]

private theorem sum_sub_const (f : α → E) (x : List α) (c : E) :
    (x.map (fun a ↦ f a - c)).sum = (x.map f).sum - (x.length : ℝ) • c := by
  induction x with
  | nil => simp
  | cons a x ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    module

omit [NormedSpace ℝ E] in
private theorem norm_sum_le_length (g : α → E) (x : List α) (D : ℝ)
    (h : ∀ a ∈ x, ‖g a‖ ≤ D) : ‖(x.map g).sum‖ ≤ x.length * D := by
  induction x with
  | nil => simp
  | cons a x ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      ‖g a + (x.map g).sum‖ ≤ ‖g a‖ + ‖(x.map g).sum‖ := norm_add_le _ _
      _ ≤ D + x.length * D := add_le_add (h a (by simp)) (ih (by
        intro b hb
        exact h b (by simp [hb])))
      _ = (x.length + 1) * D := by ring

/-- Every point of a bounded domain is within its diameter of the mean of a nonempty dataset. -/
theorem norm_empiricalMean_sub_le {f : α → E} {D : ℝ} (hD : HasDiameter f D)
    (x : Dataset α) (hx : x ≠ []) (a : α) : ‖empiricalMean f x - f a‖ ≤ D := by
  have hn : (x.length : ℝ) ≠ 0 := by simpa using hx
  have heq : empiricalMean f x - f a =
      (x.length : ℝ)⁻¹ • (x.map (fun b ↦ f b - f a)).sum := by
    rw [sum_sub_const, smul_sub, inv_smul_smul₀ hn]
    rfl
  rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    (x.length : ℝ)⁻¹ * ‖(x.map (fun b ↦ f b - f a)).sum‖ ≤
        (x.length : ℝ)⁻¹ * (x.length * D) :=
      mul_le_mul_of_nonneg_left (norm_sum_le_length _ _ _ (fun b _ ↦ hD b a))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = D := by field_simp

/-- Inserting one record changes the mean by at most `D / (size + 1)`. -/
theorem norm_empiricalMean_insert_le {f : α → E} {D : ℝ} (hD : HasDiameter f D)
    {x y : Dataset α} (hxy : Dataset.InsertOne x y) (hx : x ≠ []) :
    ‖empiricalMean f x - empiricalMean f y‖ ≤ D / y.length := by
  obtain ⟨l, r, a, rfl, rfl⟩ := hxy
  have hn : ((l ++ r).length : ℝ) ≠ 0 := by
    simpa only [ne_eq, Nat.cast_eq_zero, List.length_eq_zero_iff] using hx
  have hn1 : ((l ++ r).length : ℝ) + 1 ≠ 0 := by positivity
  have hlen : (l ++ a :: r).length = (l ++ r).length + 1 := by simp [Nat.add_assoc]
  have hsum : ((l ++ a :: r).map f).sum = ((l ++ r).map f).sum + f a := by
    simp [add_comm, add_left_comm]
  have heq : empiricalMean f (l ++ r) - empiricalMean f (l ++ a :: r) =
      (((l ++ r).length : ℝ) + 1)⁻¹ • (empiricalMean f (l ++ r) - f a) := by
    simp only [empiricalMean, hlen, Nat.cast_add, Nat.cast_one, hsum]
    match_scalars <;> field_simp
    ring
  rw [heq, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (((l ++ r).length : ℝ) + 1)⁻¹ * D :=
      mul_le_mul_of_nonneg_left (norm_empiricalMean_sub_le hD _ hx a) (by positivity)
    _ = D / (l ++ a :: r).length := by rw [hlen]; push_cast; ring

/-- Replacing one record changes the mean by at most `D / size`. -/
theorem norm_empiricalMean_replace_le {f : α → E} {D : ℝ} (hD : HasDiameter f D)
    {x y : Dataset α} (hxy : Dataset.ReplaceOne x y) :
    ‖empiricalMean f x - empiricalMean f y‖ ≤ D / x.length := by
  obtain ⟨l, r, a, b, rfl, rfl⟩ := hxy
  have heq : empiricalMean f (l ++ a :: r) - empiricalMean f (l ++ b :: r) =
      ((l ++ a :: r).length : ℝ)⁻¹ • (f a - f b) := by
    simp only [empiricalMean, List.length_append, List.length_cons, List.map_append,
      List.map_cons, List.sum_append, List.sum_cons]
    module
  rw [heq, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (hD a b) (by positivity)).trans_eq (by rw [div_eq_mul_inv]; ring)

/-- `D / n` is a global sensitivity bound for insertion/removal when both datasets have at
least the public, positive size `n`. The noise scale must use this public bound, not the actual
private length. -/
theorem sensitivity_empiricalMean_addRemove {f : α → E} {D : ℝ} (hD : HasDiameter f D)
    {n : ℕ} (hn : 0 < n) :
    HasSensitivity (Dataset.AtLeast n Dataset.AddRemove) (empiricalMean f) (D / n) := by
  intro x y ⟨hx, hy, hxy⟩
  have hx0 : x ≠ [] := by intro h; simp [h] at hx; omega
  have hy0 : y ≠ [] := by intro h; simp [h] at hy; omega
  have hD0 : 0 ≤ D := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil x hx0
    simpa using hD a a
  rcases hxy with hxy | hyx
  · exact (norm_empiricalMean_insert_le hD hxy hx0).trans
      (div_le_div_of_nonneg_left hD0 (by exact_mod_cast hn) (by exact_mod_cast hy))
  · rw [norm_sub_rev]
    exact (norm_empiricalMean_insert_le hD hyx hy0).trans
      (div_le_div_of_nonneg_left hD0 (by exact_mod_cast hn) (by exact_mod_cast hx))

/-- The same public `D / n` bound applies to replacement adjacency. -/
theorem sensitivity_empiricalMean_replaceOne {f : α → E} {D : ℝ} (hD : HasDiameter f D)
    {n : ℕ} (hn : 0 < n) :
    HasSensitivity (Dataset.AtLeast n Dataset.ReplaceOne) (empiricalMean f) (D / n) := by
  intro x y ⟨hx, _, hxy⟩
  have hD0 : 0 ≤ D := by
    obtain ⟨l, r, a, b, _, _⟩ := hxy
    simpa using hD a a
  exact (norm_empiricalMean_replace_le hD hxy).trans
    (div_le_div_of_nonneg_left hD0 (by exact_mod_cast hn) (by exact_mod_cast hx))

end DifferentialPrivacy
