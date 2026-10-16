/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import RandomDo.ForMathlib.Probability.Kernel.Composition.Comp

/-!
# Lemmas about the composition of a measure and a kernel

## Main statements

* `Measure.comp_le_comp_right`, `Measure.comp_le_comp_left`: monotonicity of `κ ∘ₘ μ` in the
  measure and in the kernel.
* `Measure.restrict_comp`: `(κ.restrict hs) ∘ₘ μ = (κ ∘ₘ μ).restrict s`.
* `Measure.comp_apply_pos_iff`: `0 < (η ∘ₘ μ) s ↔ 0 < μ {a | 0 < η a s}`.
* `Measure.withDensity_lintegral_mul_le_comp`: Chapman-Kolmogorov inequality for densities.
* `Kernel.pow_add_one_apply_pos_iff`, `Kernel.pow_add_comp_apply_pos_iff`: positivity of the
  measure of a set after `n + 1` (resp. `n + m`) steps of a kernel.
-/

@[expose] public section

open ProbabilityTheory

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {s : Set β}

/-- The set of points `a` such that `η a s` is positive is measurable. -/
lemma measurableSet_apply_pos (η : Kernel α β) (hs : MeasurableSet s) :
    MeasurableSet {a | 0 < η a s} :=
  measurableSet_lt measurable_const (η.measurable_coe hs)

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {s : Set β}

@[gcongr]
lemma comp_le_comp_right (h : μ ≤ ν) (κ : Kernel α β) : κ ∘ₘ μ ≤ κ ∘ₘ ν := by
  refine Measure.le_iff.mpr fun s hs ↦ ?_
  rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable]
  exact lintegral_mono' h le_rfl

lemma comp_le_comp_left (μ : Measure α) (h : κ ≤ η) : κ ∘ₘ μ ≤ η ∘ₘ μ := by
  refine Measure.le_iff.mpr fun s hs ↦ ?_
  rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs η.aemeasurable]
  exact lintegral_mono fun a ↦ h a s

lemma comp_le_comp (hμν : μ ≤ ν) (h : κ ≤ η) : κ ∘ₘ μ ≤ η ∘ₘ ν :=
  (comp_le_comp_left μ h).trans (comp_le_comp_right hμν η)

lemma restrict_comp (hs : MeasurableSet s) : (κ.restrict hs) ∘ₘ μ = (κ ∘ₘ μ).restrict s := by
  rw [comp_eq_comp_const_apply, Kernel.comp_restrict, Kernel.restrict_apply,
    ← comp_eq_comp_const_apply]

/-- The measure `η ∘ₘ μ` gives positive mass to a measurable set `s` iff the set of points `a`
such that `η a s` is positive has positive `μ`-measure. -/
lemma comp_apply_pos_iff {s : Set β} (hs : MeasurableSet s) :
    0 < (η ∘ₘ μ) s ↔ 0 < μ {a | 0 < η a s} := by
  rw [Measure.bind_apply hs η.aemeasurable, lintegral_pos_iff_support (η.measurable_coe hs)]
  congr! 2
  ext a
  simp [pos_iff_ne_zero]

/-- The measure `η ∘ₘ μ` gives zero mass to a measurable set `s` iff the set of points `a`
such that `η a s` is positive has `μ`-measure zero. -/
lemma comp_apply_eq_zero_iff {s : Set β} (hs : MeasurableSet s) :
    (η ∘ₘ μ) s = 0 ↔ μ {a | 0 < η a s} = 0 := by
  rw [← not_iff_not, ← Ne, ← Ne, ← pos_iff_ne_zero, ← pos_iff_ne_zero, comp_apply_pos_iff hs]

/-- Chapman-Kolmogorov inequality for densities: if a measure `μ` dominates the measure with
density `p` with respect to `φ` and a kernel `η` dominates the kernel with density `q` with respect
to `ψ`, then `η ∘ₘ μ` dominates the measure with density `z ↦ ∫⁻ y, p y * q y z ∂φ` with respect
to `ψ`. -/
lemma withDensity_lintegral_mul_le_comp {μ φ : Measure α} {ψ : Measure β} [SFinite φ] [SFinite ψ]
    {η : ProbabilityTheory.Kernel α β} {p : α → ℝ≥0∞} {q : α → β → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable (Function.uncurry q))
    (hpμ : φ.withDensity p ≤ μ) (hqη : ∀ y, ψ.withDensity (q y) ≤ η y) :
    ψ.withDensity (fun z ↦ ∫⁻ y, p y * q y z ∂φ) ≤ η ∘ₘ μ := by
  refine Measure.le_iff.mpr fun B hB ↦ ?_
  rw [withDensity_apply _ hB, Measure.bind_apply hB η.aemeasurable]
  calc ∫⁻ z in B, ∫⁻ y, p y * q y z ∂φ ∂ψ
    _ = ∫⁻ y, ∫⁻ z in B, p y * q y z ∂ψ ∂φ :=
      lintegral_lintegral_swap
        ((hp.comp measurable_snd).mul (hq.comp measurable_swap)).aemeasurable
    _ = ∫⁻ y, p y * ψ.withDensity (q y) B ∂φ := by
      congr with y
      rw [lintegral_const_mul _ hq.of_uncurry_left, withDensity_apply _ hB]
    _ ≤ ∫⁻ y, p y * η y B ∂φ := by
      gcongr with y
      exact hqη y
    _ = ∫⁻ y, η y B ∂(φ.withDensity p) :=
      (lintegral_withDensity_eq_lintegral_mul _ hp (η.measurable_coe hB)).symm
    _ ≤ ∫⁻ y, η y B ∂μ := lintegral_mono' hpμ le_rfl

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

/-! ### Powers of a kernel -/

open MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {μ : Measure α}

/-- A point `y` reaches the measurable set `C` with positive probability in `n + 1` steps iff
its first step goes with positive probability to the set of points which reach `C` with positive
probability in `n` steps. -/
lemma pow_add_one_apply_pos_iff {C : Set α} (hC : MeasurableSet C) {n : ℕ} {y : α} :
    0 < (κ ^ (n + 1)) y C ↔ 0 < κ y {z | 0 < (κ ^ n) z C} := by
  rw [pow_add_one, comp_apply, Measure.comp_apply_pos_iff hC]

/-- The measurable set `C` is reached from the measure `μ` with positive probability in `n + m`
steps iff after `m` steps, the set of points which reach `C` with positive probability in `n`
steps has positive measure. -/
lemma pow_add_comp_apply_pos_iff {C : Set α} (hC : MeasurableSet C) {m n : ℕ} :
    0 < ((κ ^ (n + m)) ∘ₘ μ) C ↔ 0 < ((κ ^ m) ∘ₘ μ) {y | 0 < (κ ^ n) y C} := by
  rw [pow_add, ← Measure.comp_assoc, Measure.comp_apply_pos_iff hC]

end ProbabilityTheory.Kernel
