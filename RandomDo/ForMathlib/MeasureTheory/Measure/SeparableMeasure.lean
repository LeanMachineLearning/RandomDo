/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import RandomDo.ForMathlib.MeasureTheory.Integral.Lebesgue.Markov
public import RandomDo.ForMathlib.MeasureTheory.Measure.Basic
public import RandomDo.ForMathlib.MeasureTheory.Measure.Prod

/-!
# Uniform lower bounds on the measure of intersections

## Main statements

* `exists_measurableSet_forall_le_measure_inter`: for jointly measurable families of sets `V x`
  and `W z` and a separable finite measure `φ`, if the integral over
  `x` and `z` of the measure of `V x ∩ W z` is positive, then there are sets `C` and `D` of
  positive measure such that the measure of `V x ∩ W z` is bounded from below uniformly over
  `x ∈ C` and `z ∈ D`. This replaces the use of a differentiation theorem for measures in the
  classical proof of the existence of small sets for irreducible kernels.
-/

@[expose] public section

open Set

open scoped ENNReal NNReal symmDiff

namespace MeasureTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {φ : Measure β} {ν : Measure γ}

/-- Consider two jointly measurable families of sets `V x` and `W z` and a separable finite
measure `φ`, such that the integral over `x` and `z` of the measure of
`V x ∩ W z` is positive. Then there are sets `C` and `D` of positive measure such that the measure
of `V x ∩ W z` is bounded from below uniformly over `x ∈ C` and `z ∈ D`. -/
lemma exists_measurableSet_forall_le_measure_inter [IsSeparable φ] [IsFiniteMeasure φ]
    [SFinite ν] {V : α → Set β} {W : γ → Set β}
    (hV : MeasurableSet {q : α × β | q.2 ∈ V q.1}) (hW : MeasurableSet {q : γ × β | q.2 ∈ W q.1})
    (h : 0 < ∫⁻ x, ∫⁻ z, φ (V x ∩ W z) ∂ν ∂μ) :
    ∃ (C : Set α) (D : Set γ) (δ : ℝ≥0), MeasurableSet C ∧ MeasurableSet D ∧ 0 < μ C ∧ 0 < ν D ∧
      0 < δ ∧ ∀ x ∈ C, ∀ z ∈ D, (δ : ℝ≥0∞) ≤ φ (V x ∩ W z) := by
  have hm : Measurable fun q : α × γ ↦ φ (V q.1 ∩ W q.2) :=
    measurable_measure_inter_of_measurableSet hV hW
  -- the set `G` of pairs `(x, z)` such that `5 * δ < φ (V x ∩ W z)` has positive measure
  rw [← lintegral_prod (fun q : α × γ ↦ φ (V q.1 ∩ W q.2)) hm.aemeasurable] at h
  obtain ⟨ε, hε, hG⟩ := exists_pos_measure_lt_of_lintegral_pos h
  obtain ⟨δ, hδ, rfl⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ 5 * δ = ε := ⟨ε / 5, by positivity, by field_simp⟩
  set G : Set (α × γ) := {q | ((5 * δ : ℝ≥0) : ℝ≥0∞) < φ (V q.1 ∩ W q.2)}
  -- `P S` and `Q S` are the sets of points `x`, `z` such that `V x`, `W z` are `δ`-close to `S`
  obtain ⟨𝒜, h𝒜c, h𝒜⟩ := exists_countable_measureDense (μ := φ)
  let P : Set β → Set α := fun S ↦ {x | φ (V x ∆ S) < δ}
  let Q : Set β → Set γ := fun S ↦ {z | φ (W z ∆ S) < δ}
  have hP (S : Set β) (hS : S ∈ 𝒜) : MeasurableSet (P S) :=
    measurableSet_lt (measurable_measure_symmDiff_of_measurableSet hV (h𝒜.measurable S hS))
      measurable_const
  have hQ (S : Set β) (hS : S ∈ 𝒜) : MeasurableSet (Q S) :=
    measurableSet_lt (measurable_measure_symmDiff_of_measurableSet hW (h𝒜.measurable S hS))
      measurable_const
  have hPcov (x : α) : ∃ S ∈ 𝒜, x ∈ P S := by
    obtain ⟨S, hS, hxS⟩ := h𝒜.approx (V x) (measurable_prodMk_left hV) (measure_ne_top _ _) δ hδ
    exact ⟨S, hS, (by simpa using hxS : φ (V x ∆ S) < δ)⟩
  have hQcov (z : γ) : ∃ S ∈ 𝒜, z ∈ Q S := by
    obtain ⟨S, hS, hzS⟩ := h𝒜.approx (W z) (measurable_prodMk_left hW) (measure_ne_top _ _) δ hδ
    exact ⟨S, hS, (by simpa using hzS : φ (W z ∆ S) < δ)⟩
  -- the countably many rectangles `P S ×ˢ Q S'` cover `G`, hence one of them meets `G` on a set
  -- of positive measure
  obtain ⟨⟨S, S'⟩, ⟨hS, hS'⟩, hpos⟩ : ∃ T ∈ 𝒜 ×ˢ 𝒜, 0 < (μ.prod ν) (G ∩ P T.1 ×ˢ Q T.2) := by
    by_contra! hcon
    refine hG.ne' (measure_mono_null (t := ⋃ T ∈ 𝒜 ×ˢ 𝒜, G ∩ P T.1 ×ˢ Q T.2) (fun q hq ↦ ?_) ?_)
    · obtain ⟨S, hS, hxS⟩ := hPcov q.1
      obtain ⟨S', hS', hzS'⟩ := hQcov q.2
      exact mem_iUnion₂.mpr ⟨(S, S'), ⟨hS, hS'⟩, hq, hxS, hzS'⟩
    · exact (measure_biUnion_null_iff (h𝒜c.prod h𝒜c)).mpr
        fun T hT ↦ nonpos_iff_eq_zero.mp (hcon T hT)
  have hrect : 0 < μ (P S) * ν (Q S') := by
    rw [← Measure.prod_prod]
    exact hpos.trans_le (measure_mono inter_subset_right)
  obtain ⟨⟨x₀, z₀⟩, hq₀, hx₀, hz₀⟩ := nonempty_of_measure_ne_zero hpos.ne'
  refine ⟨P S, Q S', δ, hP S hS, hQ S' hS', pos_of_mul_pos_left hrect zero_le,
    pos_of_mul_pos_right hrect zero_le, hδ, fun x hx z hz ↦ ?_⟩
  -- for `x ∈ P S` and `z ∈ Q S'`, the set `V x ∩ W z` is `4 * δ`-close to `V x₀ ∩ W z₀`
  by_contra! hlt
  refine lt_asymm (a := ((5 * δ : ℝ≥0) : ℝ≥0∞)) hq₀ ?_
  calc φ (V x₀ ∩ W z₀)
    _ ≤ φ (V x ∩ W z) + (φ (V x₀ ∆ S) + φ (V x ∆ S)) + (φ (W z₀ ∆ S') + φ (W z ∆ S')) :=
      measure_inter_le_measure_inter_add_symmDiff ..
    _ < δ + (δ + δ) + (δ + δ) :=
      ENNReal.add_lt_add (ENNReal.add_lt_add hlt (ENNReal.add_lt_add hx₀ hx))
        (ENNReal.add_lt_add hz₀ hz)
    _ = ((5 * δ : ℝ≥0) : ℝ≥0∞) := by
      push_cast
      ring

end MeasureTheory
