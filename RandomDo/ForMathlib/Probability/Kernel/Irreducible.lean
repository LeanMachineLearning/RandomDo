/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Irreducible
public import RandomDo.ForMathlib.MeasureTheory.Measure.Decomposition.Exhaustion
public import RandomDo.ForMathlib.Probability.Kernel.Invariance

/-!
# Irreducible kernels

Lemmas about irreducible kernels, in particular in the presence of an invariant measure.

## Main statements

* `Kernel.IsIrreducible.exists_pow_succ_pos`: for a `φ`-irreducible kernel, every set of positive
  `φ`-measure is reached with positive probability in a positive number of steps from every
  point `x` with `κ x ≠ 0`.
* `Kernel.IsIrreducible.exists_pow_comp_apply_pos`: for a `φ`-irreducible kernel, every set of
  positive `φ`-measure is reached with positive probability from any nonzero initial measure.
* `Kernel.IsIrreducible.absolutelyContinuous`: `φ ≪ π` for every nonzero invariant measure `π`
  of a `φ`-irreducible kernel.
* `Kernel.IsIrreducible.exists_measure_le`: a kernel which is irreducible with respect to `φ ≪ π`
  is irreducible with respect to a nonzero measure `φ' ≤ π`. This allows to replace an arbitrary
  irreducibility measure by a finite one.
* `Kernel.Invariant.measure_eq_zero_or_measure_compl_eq_zero`: a measurable set of finite
  measure which is absorbing `π`-almost everywhere has `π`-measure zero or `π`-null complement.
* `Kernel.Invariant.ae_le_of_le_lintegral`: a function `f` with `f x ≤ ∫⁻ y, f y ∂κ x` for
  `π`-almost every `x` (a subharmonic function) is `π`-a.e. less than `t` as soon as
  `{x | f x ≤ t}` is not `π`-null.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {φ π : Measure α} {G : Set α}

/-- For a `φ`-irreducible kernel, the sets of points which reach a set `A` of positive
`φ`-measure with positive probability in `n` steps cover the space. -/
lemma IsIrreducible.iUnion_setOf_pow_apply_pos_eq_univ [IsIrreducible φ κ] {A : Set α}
    (hA : MeasurableSet A) (hφA : 0 < φ A) :
    ⋃ n, {y | 0 < (κ ^ n) y A} = Set.univ := by
  ext y
  simpa using IsIrreducible.irreducible (φ := φ) hA hφA y

/-- For a `φ`-irreducible kernel, every set of positive `φ`-measure is reached with positive
probability in a positive number of steps from every point `x` with `κ x ≠ 0`, hence from every
point if `κ` is a Markov kernel. -/
lemma IsIrreducible.exists_pow_succ_pos [IsIrreducible φ κ] {A : Set α} (hA : MeasurableSet A)
    (hφA : 0 < φ A) {x : α} (hx : κ x ≠ 0) :
    ∃ n, 0 < (κ ^ (n + 1)) x A := by
  have hpos : κ x (⋃ n, {y | 0 < (κ ^ n) y A}) ≠ 0 := by
    rw [IsIrreducible.iUnion_setOf_pow_apply_pos_eq_univ (φ := φ) hA hφA]
    exact Measure.measure_univ_ne_zero.mpr hx
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hpos
  exact ⟨n, (pow_succ_apply_pos_iff hA).mpr hn⟩

/-- For a `φ`-irreducible kernel, every set of positive `φ`-measure is reached with positive
probability from any nonzero initial measure. -/
lemma IsIrreducible.exists_pow_comp_apply_pos [IsIrreducible φ κ] {C : Set α}
    (hC : MeasurableSet C) (hφC : 0 < φ C) {μ : Measure α} (hμ : μ ≠ 0) :
    ∃ n : ℕ, 0 < ((κ ^ n) ∘ₘ μ) C := by
  have hpos : μ (⋃ n : ℕ, {y | 0 < (κ ^ n) y C}) ≠ 0 := by
    simp [IsIrreducible.iUnion_setOf_pow_apply_pos_eq_univ (φ := φ) hC hφC, hμ]
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hpos
  exact ⟨n, (Measure.comp_apply_pos_iff hC).mpr hn⟩

/-! ### Irreducible kernels with an invariant measure -/

/-- An irreducibility measure of a kernel is absolutely continuous with respect to every nonzero
invariant measure. -/
lemma IsIrreducible.absolutelyContinuous [IsIrreducible φ κ] (hπ : κ.Invariant π) (hπ0 : π ≠ 0) :
    φ ≪ π := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hπA ↦ ?_
  by_contra hφA
  have : NeZero π := ⟨hπ0⟩
  obtain ⟨x, hx⟩ := (hπ.ae_ae_pow (measure_eq_zero_iff_ae_notMem.mp hπA)).exists
  obtain ⟨n, hn⟩ := IsIrreducible.irreducible (φ := φ) (κ := κ) hA (pos_iff_ne_zero.mpr hφA) x
  exact hn.ne' (measure_eq_zero_iff_ae_notMem.mpr (hx n))

/-- If `κ` is `φ`-irreducible for a nonzero measure `φ ≪ π` with `π` s-finite, then `κ` is
irreducible with respect to a nonzero measure which is less than `π`. No finiteness assumption is
needed on `φ`. -/
lemma IsIrreducible.exists_measure_le [SFinite π] [IsIrreducible φ κ] (hφ : φ ≠ 0) (hφπ : φ ≪ π) :
    ∃ φ' : Measure α, φ' ≤ π ∧ φ' ≠ 0 ∧ IsIrreducible φ' κ := by
  obtain ⟨N, hN, hφN, hac⟩ := Measure.exists_null_restrict_compl_absolutelyContinuous φ π
  refine ⟨π.restrict Nᶜ, Measure.restrict_le_self, fun h0 ↦ hφ ?_, ⟨fun A hA hA_pos a ↦ ?_⟩⟩
  · rw [Measure.restrict_eq_zero] at h0
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self N]
    exact measure_union_null hφN (hφπ h0)
  · exact IsIrreducible.irreducible (φ := φ) hA (pos_iff_ne_zero.mpr fun h ↦ hA_pos.ne' (hac h)) a

/-- If `κ` is `φ`-irreducible with invariant measure `π` and `G` is absorbing `π`-almost
everywhere, with `π G ≠ 0`, then the complement of `G` is `φ`-null. -/
lemma Invariant.measure_compl_eq_zero_of_ae_absorbing [IsIrreducible φ κ] (hπ : κ.Invariant π)
    (hG : MeasurableSet G) (h : ∀ᵐ x ∂π, x ∈ G → κ x Gᶜ = 0) (hπG : π G ≠ 0) :
    φ Gᶜ = 0 := by
  by_contra hφ
  have hfreq : ∃ᵐ x ∂π, x ∈ G := frequently_ae_mem_iff.mpr hπG
  obtain ⟨x, hxG, hx⟩ := (hfreq.and_eventually (hπ.ae_pow_apply_compl_eq_zero hG h)).exists
  obtain ⟨n, hn⟩ := IsIrreducible.irreducible (φ := φ) (κ := κ) hG.compl (pos_iff_ne_zero.mpr hφ) x
  exact hn.ne' (hx hxG n)

/-- **Ergodicity** of an irreducible Markov kernel with respect to an invariant measure `π`: a
measurable set of finite measure which is absorbing `π`-almost everywhere has measure zero or its
complement has measure zero. -/
lemma Invariant.measure_eq_zero_or_measure_compl_eq_zero [IsMarkovKernel κ] [IsIrreducible φ κ]
    (hφ : φ ≠ 0) (hπ : κ.Invariant π) (hG : MeasurableSet G) (hπG : π G ≠ ∞)
    (h : ∀ᵐ x ∂π, x ∈ G → κ x Gᶜ = 0) :
    π G = 0 ∨ π Gᶜ = 0 := by
  by_contra! hcon
  have h1 : φ Gᶜ = 0 := hπ.measure_compl_eq_zero_of_ae_absorbing hG h hcon.1
  have h2 : φ Gᶜᶜ = 0 := by
    refine hπ.measure_compl_eq_zero_of_ae_absorbing hG.compl ?_ hcon.2
    simpa using hπ.ae_apply_eq_zero_of_ae_absorbing hG hπG h
  rw [compl_compl] at h2
  refine hφ ?_
  rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self G]
  exact measure_union_null h2 h1

/-- Let `κ` be an irreducible Markov kernel with finite invariant measure `π` and let `f` be a
`π`-integrable function which is subharmonic `π`-almost everywhere: `f x ≤ ∫⁻ y, f y ∂κ x` for
`π`-almost every `x`. If the set `{x | f x ≤ t}` is not `π`-null, then `f ≤ t` almost
everywhere. -/
lemma Invariant.ae_le_of_le_lintegral [IsMarkovKernel κ] [IsFiniteMeasure π] [IsIrreducible φ κ]
    (hφ : φ ≠ 0) (hπ : κ.Invariant π) {f : α → ℝ≥0∞} (hf : Measurable f)
    (hf_int : ∫⁻ x, f x ∂π ≠ ∞) (hsub : ∀ᵐ x ∂π, f x ≤ ∫⁻ y, f y ∂κ x) {t : ℝ≥0∞}
    (ht : π {x | f x ≤ t} ≠ 0) :
    ∀ᵐ x ∂π, f x ≤ t := by
  have hG : MeasurableSet {x | f x ≤ t} := measurableSet_le hf measurable_const
  -- the function `g = f - t` is subharmonic
  have hg : Measurable fun x ↦ f x - t := hf.sub_const t
  have hg_sub : ∀ᵐ x ∂π, f x - t ≤ ∫⁻ y, f y - t ∂κ x := by
    filter_upwards [hsub] with x hx
    rw [tsub_le_iff_right]
    calc f x ≤ ∫⁻ y, f y ∂κ x := hx
    _ ≤ ∫⁻ y, (f y - t) + t ∂κ x := lintegral_mono fun y ↦ le_tsub_add
    _ = ∫⁻ y, f y - t ∂κ x + t := by
      rw [lintegral_add_right _ measurable_const, MeasureTheory.lintegral_const, measure_univ,
        mul_one]
  -- hence `g` is harmonic almost everywhere
  have hg_ae : (fun x ↦ f x - t) =ᵐ[π] fun x ↦ ∫⁻ y, f y - t ∂κ x := by
    refine ae_eq_of_ae_le_of_lintegral_le hg_sub ?_ hg.lintegral_kernel.aemeasurable (le_of_eq ?_)
    · exact ((lintegral_mono fun x ↦ tsub_le_self).trans_lt hf_int.lt_top).ne
    · rw [← Measure.lintegral_bind κ.aemeasurable hg.aemeasurable, hπ.def]
  -- so the sublevel set is absorbing almost everywhere
  have h_abs : ∀ᵐ x ∂π, x ∈ {x | f x ≤ t} → κ x {x | f x ≤ t}ᶜ = 0 := by
    filter_upwards [hg_ae] with x hx hxG
    have h0 : ∫⁻ y, f y - t ∂κ x = 0 := by rw [← hx]; exact tsub_eq_zero_of_le hxG
    rw [lintegral_eq_zero_iff hg] at h0
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h0] with y hy
    simpa [tsub_eq_zero_iff_le] using hy
  rcases hπ.measure_eq_zero_or_measure_compl_eq_zero hφ hG (measure_ne_top π _) h_abs with h | h
  · exact absurd h ht
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with x hx using by simpa using hx

end ProbabilityTheory.Kernel
