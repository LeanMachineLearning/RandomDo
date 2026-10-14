/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measure of jointly measurable families of sets

## Main statements

* `measurable_measure_inter_of_measurableSet`: for jointly measurable families of sets `V x` and
  `W z`, the measure of `V x ∩ W z` is a measurable function of `(x, z)`.
* `exists_lintegral_measure_inter_pos`: for countable collections of jointly measurable families
  `V i x` and `W i' z` which cover almost all the space, there are `i, i'` such that the integral
  over `x` and `z` of the measure of `V i x ∩ W i' z` is positive.
-/

@[expose] public section

open Set

open scoped ENNReal symmDiff

namespace MeasureTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {φ : Measure β} {ν : Measure γ}

/-- For a jointly measurable family of sets `V x`, the measure of the symmetric difference of
`V x` and a measurable set is a measurable function of `x`. -/
lemma measurable_measure_symmDiff_of_measurableSet [SFinite φ] {V : α → Set β}
    (hV : MeasurableSet {q : α × β | q.2 ∈ V q.1}) {S : Set β} (hS : MeasurableSet S) :
    Measurable fun x ↦ φ (V x ∆ S) :=
  measurable_measure_prodMk_left (hV.symmDiff (measurable_snd hS))

/-- For two jointly measurable families of sets `V x` and `W z`, the measure of `V x ∩ W z` is a
measurable function of `(x, z)`. -/
lemma measurable_measure_inter_of_measurableSet [SFinite φ] {V : α → Set β} {W : γ → Set β}
    (hV : MeasurableSet {q : α × β | q.2 ∈ V q.1}) (hW : MeasurableSet {q : γ × β | q.2 ∈ W q.1}) :
    Measurable fun q : α × γ ↦ φ (V q.1 ∩ W q.2) :=
  measurable_measure_prodMk_left
    ((hV.preimage (measurable_fst.fst.prodMk measurable_snd :
        Measurable fun t : (α × γ) × β ↦ (t.1.1, t.2))).inter
      (hW.preimage (measurable_fst.snd.prodMk measurable_snd :
        Measurable fun t : (α × γ) × β ↦ (t.1.2, t.2))))

/-- Consider two countable collections of jointly measurable families of sets `V i x` and
`W i' z` such that for almost all `x`, almost every `y` belongs to some `V i x`, and for almost
all `y`, for almost every `z`, `y` belongs to some `W i' z`. Then there are `i, i'` such that
the integral over `x` and `z` of the measure of `V i x ∩ W i' z` is positive. -/
lemma exists_lintegral_measure_inter_pos {ι ι' : Type*} [Countable ι] [Countable ι']
    [SFinite φ] [SFinite ν] {V : ι → α → Set β} {W : ι' → γ → Set β}
    (hV : ∀ i, MeasurableSet {q : α × β | q.2 ∈ V i q.1})
    (hW : ∀ i, MeasurableSet {q : γ × β | q.2 ∈ W i q.1})
    (hVae : ∀ᵐ x ∂μ, ∀ᵐ y ∂φ, ∃ i, y ∈ V i x)
    (hWae : ∀ᵐ y ∂φ, ∀ᵐ z ∂ν, ∃ i, y ∈ W i z)
    (hμ : μ ≠ 0) (hφ : φ ≠ 0) (hν : ν ≠ 0) :
    ∃ i i', 0 < ∫⁻ x, ∫⁻ z, φ (V i x ∩ W i' z) ∂ν ∂μ := by
  by_contra! h
  have hm (i : ι) (i' : ι') : Measurable fun q : α × γ ↦ φ (V i q.1 ∩ W i' q.2) :=
    measurable_measure_inter_of_measurableSet (hV i) (hW i')
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  have : (ae φ).NeBot := ae_neBot.mpr hφ
  have : (ae ν).NeBot := ae_neBot.mpr hν
  -- we can fix `x` such that for almost all `z`, the sets `V i x ∩ W i' z` have measure zero
  have hx_ae : ∀ᵐ x ∂μ, ∀ᵐ z ∂ν, ∀ i i', φ (V i x ∩ W i' z) = 0 := by
    simp_rw [ae_all_iff]
    intro i i'
    filter_upwards [(lintegral_eq_zero_iff (hm i i').lintegral_prod_right').mp
      (nonpos_iff_eq_zero.mp (h i i'))] with x hx
    exact (lintegral_eq_zero_iff ((hm i i').comp measurable_prodMk_left)).mp hx
  obtain ⟨x, hx, hVx⟩ := (hx_ae.and hVae).exists
  -- since the sets `V i x` cover almost all the space, the sets `W i' z` are almost empty
  have h2 : ∀ᵐ z ∂ν, ∀ᵐ y ∂φ, ∀ i', y ∉ W i' z := by
    filter_upwards [hx] with z hz
    have h0 : φ (⋃ i, ⋃ i', V i x ∩ W i' z) = 0 :=
      measure_iUnion_null fun i ↦ measure_iUnion_null fun i' ↦ hz i i'
    filter_upwards [hVx, measure_eq_zero_iff_ae_notMem.mp h0] with y ⟨i, hy⟩ hy' i' hi'
    exact hy' (mem_iUnion₂.mpr ⟨i, i', hy, hi'⟩)
  -- this contradicts the assumption on `W` after exchanging the two quantifiers
  rw [Measure.ae_ae_comm] at h2
  swap
  · simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i' ↦ (hW i').compl
  obtain ⟨y, hy, hWy⟩ := (h2.and hWae).exists
  obtain ⟨z, hz, i', hz'⟩ := (hy.and hWy).exists
  exact hz i' hz'

end MeasureTheory
