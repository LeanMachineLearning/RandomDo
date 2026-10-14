/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.RadonNikodym
public import RandomDo.ForMathlib.MeasureTheory.Measure.SeparableMeasure
public import RandomDo.ForMathlib.Probability.Kernel.Irreducible
public import RandomDo.ForMathlib.Probability.Kernel.SmallSet.Basic

/-!
# Existence of small sets

For a `φ`-irreducible Markov kernel on a countably generated measurable space, every set of
positive `φ`-measure contains a small set of positive `φ`-measure.

## Main statements

* `ProbabilityTheory.Kernel.exists_isSmallSet`: existence of small sets.

## Proof sketch

Let `p n x` be the density of the absolutely continuous part of `(κ ^ (n + 1)) x` with respect to
`φ`, which is jointly measurable in `(x, y)` since the space is countably generated.

* By irreducibility, for all `x`, for `φ`-almost every `y` there is `n` with `0 < p n x y`
  (`IsIrreducible.ae_exists_rnDeriv_pow_succ_pos`).
* For `V x = {y | ε < p m x y}` and `W z = {y | ε' < p n y z}`, the previous point implies that we
  can choose `m`, `n`, `ε`, `ε'` such that `∫⁻ x in A, ∫⁻ z, φ (V x ∩ W z) ∂φ ∂φ` is positive
  (`exists_lintegral_measure_inter_pos`).
* Since `φ` is a finite measure on a countably generated space, there is a countable family of
  sets which approximates every measurable set up to an arbitrarily small `φ`-measure. Sorting
  the points `x` and `z` according to the sets of the family which approximate `V x` and `W z`, we
  get sets `C ⊆ A` and `D` of positive measure and `δ > 0` such that `δ ≤ φ (V x ∩ W z)` for all
  `x ∈ C` and `z ∈ D` (`exists_measurableSet_forall_le_measure_inter`). This replaces the use of a
  differentiation theorem for measures in the classical proof.
* By the Chapman-Kolmogorov equation, `(κ ^ ((n + 1) + (m + 1))) x` dominates the measure with
  density `z ↦ ∫⁻ y, p m x y * p n y z ∂φ` with respect to `φ`
  (`Measure.withDensity_lintegral_mul_le_comp`), and that density is at least `ε * ε' * δ` for
  `x ∈ C` and `z ∈ D` (`isSmallSet_of_le_lintegral_mul`).

## References

* [Meyn, S.P. and Tweedie, R.L., *Markov Chains and Stochastic Stability*][meyntweedie1993]
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {φ : Measure α}

/-- If the measures `(κ ^ m) x` and `(κ ^ n) y` dominate the measures with densities `p x` and
`q y` with respect to `φ`, and if `∫⁻ y, p x y * q y z ∂φ` is bounded from below by `c` for
`x ∈ C` and `z ∈ D`, then `C` is a small set for `κ`. -/
lemma isSmallSet_of_le_lintegral_mul [SFinite φ] {p q : α → α → ℝ≥0∞} {m n : ℕ} {C D : Set α}
    {c : ℝ≥0} (hp : Measurable (Function.uncurry p)) (hq : Measurable (Function.uncurry q))
    (hpκ : ∀ x, φ.withDensity (p x) ≤ (κ ^ m) x) (hqκ : ∀ y, φ.withDensity (q y) ≤ (κ ^ n) y)
    (hD : MeasurableSet D) (h : ∀ x ∈ C, ∀ z ∈ D, (c : ℝ≥0∞) ≤ ∫⁻ y, p x y * q y z ∂φ) :
    IsSmallSet κ C (n + m) (c • φ.restrict D) := by
  intro x hx
  rw [pow_add_apply]
  refine le_trans (Measure.le_iff.mpr fun B hB ↦ ?_)
    (Measure.withDensity_lintegral_mul_le_comp hp.of_uncurry_left hq (hpκ x) hqκ)
  rw [withDensity_apply _ hB, Measure.smul_apply, Measure.restrict_apply hB,
    Measure.nnreal_smul_coe_apply]
  calc c * φ (B ∩ D)
    _ = ∫⁻ _ in B ∩ D, c ∂φ := by rw [MeasureTheory.setLIntegral_const]
    _ ≤ ∫⁻ z in B ∩ D, ∫⁻ y, p x y * q y z ∂φ ∂φ :=
      setLIntegral_mono' (hB.inter hD) fun z hz ↦ h x hx z hz.2
    _ ≤ ∫⁻ z in B, ∫⁻ y, p x y * q y z ∂φ ∂φ := lintegral_mono_set inter_subset_left

/-- For a `φ`-irreducible Markov kernel `κ` and all `x`, for `φ`-almost every `y`, one of the
densities of the measures `(κ ^ (n + 1)) x` with respect to `φ` is positive at `y`. -/
lemma IsIrreducible.ae_exists_rnDeriv_pow_succ_pos [MeasurableSpace.CountablyGenerated α]
    [IsMarkovKernel κ] [IsFiniteMeasure φ] [IsIrreducible φ κ] (x : α) :
    ∀ᵐ y ∂φ, ∃ n, 0 < rnDeriv (κ ^ (n + 1)) (const α φ) x y := by
  -- `N n` is a `φ`-null set outside of which `(κ ^ (n + 1)) x` has no singular part
  let N : ℕ → Set α := fun n ↦ mutuallySingularSetSlice (κ ^ (n + 1)) (const α φ) x
  have hN : MeasurableSet (⋃ n, N n) :=
    MeasurableSet.iUnion fun n ↦ measurableSet_mutuallySingularSetSlice _ _ _
  have hφN : φ (⋃ n, N n) = 0 := measure_iUnion_null fun n ↦ by
    simpa using measure_mutuallySingularSetSlice (κ ^ (n + 1)) (const α φ) x
  let B : Set α := {y | ∀ n, rnDeriv (κ ^ (n + 1)) (const α φ) x y = 0}
  have hB : MeasurableSet B := by
    simp only [B, ofPred_forall]
    exact MeasurableSet.iInter fun n ↦
      measurableSet_eq_fun (measurable_rnDeriv_right _ _ _) measurable_const
  suffices φ B = 0 by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with y hy
    simpa [B, pos_iff_ne_zero] using hy
  -- otherwise, by irreducibility `B \ ⋃ n, N n` would be charged by some `(κ ^ (n + 1)) x`
  by_contra hB0
  have hB' : 0 < φ (B \ ⋃ n, N n) := by
    rw [measure_sdiff_null hφN]
    exact pos_iff_ne_zero.mpr hB0
  obtain ⟨n, hn⟩ := IsIrreducible.exists_pow_succ_pos (κ := κ) (hB.diff hN) hB'
    (IsProbabilityMeasure.ne_zero (κ x))
  refine hn.ne' ?_
  rw [← withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice (η := const α φ)
    (hB.diff hN) fun y hy hyN ↦ hy.2 (mem_iUnion.2 ⟨n, hyN⟩),
    Kernel.withDensity_apply' _ (measurable_rnDeriv _ _),
    setLIntegral_congr_fun (hB.diff hN) fun y hy ↦ hy.1 n, lintegral_zero]

/-- **Existence of small sets**. For a `φ`-irreducible Markov kernel `κ` on a countably generated
measurable space, every set `A` of positive `φ`-measure contains a set `C` of positive
`φ`-measure which is small: there are `n > 0`, `c > 0` and a set `D` of positive `φ`-measure
such that `c • φ.restrict D ≤ (κ ^ n) x` for all `x ∈ C`.
Ref. *Meyn-Tweedie* Theorem 5.2.2. -/
theorem exists_isSmallSet [MeasurableSpace.CountablyGenerated α] [IsMarkovKernel κ]
    [IsFiniteMeasure φ] [IsIrreducible φ κ] {A : Set α} (hA : MeasurableSet A) (hφA : 0 < φ A) :
    ∃ (C D : Set α) (n : ℕ) (c : ℝ≥0), MeasurableSet C ∧ MeasurableSet D ∧ C ⊆ A ∧
      0 < φ C ∧ 0 < φ D ∧ 0 < n ∧ 0 < c ∧ IsSmallSet κ C n (c • φ.restrict D) := by
  -- `p n x` is the density of the absolutely continuous part of `(κ ^ (n + 1)) x` w.r.t. `φ`
  let p : ℕ → α → α → ℝ≥0∞ := fun n ↦ rnDeriv (κ ^ (n + 1)) (const α φ)
  have hp (n : ℕ) : Measurable (Function.uncurry (p n)) := measurable_rnDeriv _ _
  have hpκ (n : ℕ) (x : α) : φ.withDensity (p n x) ≤ (κ ^ (n + 1)) x := by
    have h := withDensity_rnDeriv_le (κ ^ (n + 1)) (const α φ) x
    rwa [Kernel.withDensity_apply _ (hp n), const_apply] at h
  -- `V (m, j) x` and `W (n, j) z` are the sets of `y` where `p m x y` and `p n y z` exceed `ε j`
  let ε : ℕ → ℝ≥0 := fun j ↦ ((j : ℝ≥0) + 1)⁻¹
  have hε (j : ℕ) : 0 < ε j := by positivity
  have hε_le (j : ℕ) : (ε j : ℝ≥0∞) ≤ (j : ℝ≥0∞)⁻¹ := by
    have hj : ((j : ℝ≥0) + 1) ≠ 0 := by positivity
    simp only [ε, ENNReal.coe_inv hj, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one]
    exact ENNReal.inv_le_inv.mpr le_self_add
  let V : ℕ × ℕ → α → Set α := fun i x ↦ {y | (ε i.2 : ℝ≥0∞) < p i.1 x y}
  let W : ℕ × ℕ → α → Set α := fun i z ↦ {y | (ε i.2 : ℝ≥0∞) < p i.1 y z}
  have hV (i : ℕ × ℕ) : MeasurableSet {q : α × α | q.2 ∈ V i q.1} :=
    measurableSet_lt measurable_const (hp i.1)
  have hW (i : ℕ × ℕ) : MeasurableSet {q : α × α | q.2 ∈ W i q.1} :=
    measurableSet_lt measurable_const ((hp i.1).comp measurable_swap)
  have hp_pos (x : α) : ∀ᵐ y ∂φ, ∃ i : ℕ × ℕ, (ε i.2 : ℝ≥0∞) < p i.1 x y := by
    filter_upwards [IsIrreducible.ae_exists_rnDeriv_pow_succ_pos (κ := κ) x] with y ⟨n, hn⟩
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hn.ne'
    exact ⟨(n, j), (hε_le j).trans_lt hj⟩
  -- we find `C ⊆ A` and `D` such that `φ (V i x ∩ W i' z)` is bounded from below on `C ×ˢ D`
  have hφ : φ ≠ 0 := fun h ↦ hφA.ne' (by simp [h])
  have hφA' : φ.restrict A ≠ 0 := Measure.restrict_eq_zero.not.mpr hφA.ne'
  obtain ⟨i, i', hi⟩ := exists_lintegral_measure_inter_pos (μ := φ.restrict A) hV hW
    (ae_of_all _ hp_pos) (ae_of_all _ hp_pos) hφA' hφ hφ
  obtain ⟨C, D, δ, hC, hD, hφC, hφD, hδ, hCD⟩ :=
    exists_measurableSet_forall_le_measure_inter (hV i) (hW i') hi
  rw [Measure.restrict_apply hC] at hφC
  -- the set `C ∩ A` is small
  refine ⟨C ∩ A, D, (i'.1 + 1) + (i.1 + 1), ε i.2 * ε i'.2 * δ, hC.inter hA, hD, inter_subset_right,
    hφC, hφD, by lia, mul_pos (mul_pos (hε _) (hε _)) hδ, ?_⟩
  refine isSmallSet_of_le_lintegral_mul (hp i.1) (hp i'.1) (hpκ i.1) (hpκ i'.1) hD
    fun x hx z hz ↦ ?_
  calc ((ε i.2 * ε i'.2 * δ : ℝ≥0) : ℝ≥0∞)
    _ = ε i.2 * ε i'.2 * δ := by simp only [ENNReal.coe_mul]
    _ ≤ ε i.2 * ε i'.2 * φ (V i x ∩ W i' z) := by
      gcongr
      exact hCD x hx.1 z hz
    _ ≤ ∫⁻ y, p i.1 x y * p i'.1 y z ∂φ :=
      mul_measure_inter_lt_le_lintegral_mul (hp i.1).of_uncurry_left.aemeasurable
        (hp i'.1).of_uncurry_right.aemeasurable _ _

end ProbabilityTheory.Kernel
