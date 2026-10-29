/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Invariance
public import RandomDo.ForMathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Invariant measures and powers of a kernel

## Main statements

* `Kernel.Invariant.pow`: a measure invariant for `κ` is invariant for `κ ^ n`.
* `Kernel.Invariant.smul`: a multiple of an invariant measure is invariant.
* `Kernel.Invariant.ae_ae_pow`: if a property holds `μ`-almost everywhere for a measure `μ`
  invariant for `κ`, then for `μ`-almost every `a` it holds `(κ ^ n) a`-almost everywhere for
  all `n`.
* `Kernel.Invariant.ae_apply_eq_zero_of_compl`: if a measurable set of finite measure is
  absorbing almost everywhere with respect to an invariant measure of a Markov kernel, then so is
  its complement.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {μ : Measure α}

theorem Invariant.pow (h : Invariant κ μ) (n : ℕ) : Invariant (κ ^ n) μ := by
  induction n with
  | zero => simp [Invariant]
  | succ n ih => rw [pow_succ, mul_eq_comp]; exact ih.comp h

theorem Invariant.smul (h : Invariant κ μ) (c : ℝ≥0∞) : Invariant κ (c • μ) := by
  rw [Invariant, Measure.comp_smul, h.def]

/-- If `μ` is invariant for `κ` and a property holds `μ`-almost everywhere, then for `μ`-almost
every `a` it holds `(κ ^ n) a`-almost everywhere for all `n`. -/
theorem Invariant.ae_ae_pow (h : Invariant κ μ) {p : α → Prop} (hp : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂μ, ∀ n, ∀ᵐ b ∂(κ ^ n) a, p b := by
  rw [ae_all_iff]
  intro n
  rw [← (h.pow n).def] at hp
  exact Measure.ae_ae_of_ae_comp hp

section Absorbing

variable {π : Measure α} {G : Set α}

/-- If a measurable set `G` is absorbing almost everywhere with respect to an invariant measure
`π`, then for `π`-almost every point of `G`, no power of `κ` charges `Gᶜ`. -/
theorem Invariant.ae_pow_apply_compl_eq_zero (hπ : Invariant κ π) (hG : MeasurableSet G)
    (h : ∀ᵐ x ∂π, x ∈ G → κ x Gᶜ = 0) :
    ∀ᵐ x ∂π, x ∈ G → ∀ n, (κ ^ n) x Gᶜ = 0 := by
  suffices ∀ n, ∀ᵐ x ∂π, x ∈ G → (κ ^ n) x Gᶜ = 0 by
    filter_upwards [ae_all_iff.mpr this] with x hx hxG n using hx n hxG
  intro n
  induction n with
  | zero => simp [Kernel.id_apply, Measure.dirac_apply' _ hG.compl]
  | succ n ih =>
    have h1 : ∀ᵐ x ∂π, ∀ᵐ y ∂κ x, y ∈ G → (κ ^ n) y Gᶜ = 0 := by
      rw [← hπ.def] at ih
      exact Measure.ae_ae_of_ae_comp ih
    filter_upwards [h, h1] with x hx hx1 hxG
    suffices (fun a ↦ (κ ^ n) a Gᶜ) =ᵐ[κ x] 0 by
      rwa [pow_add_one, comp_apply, Measure.bind_apply hG.compl (κ ^ n).aemeasurable,
        lintegral_eq_zero_iff ((κ ^ n).measurable_coe hG.compl)]
    have hxG' : ∀ᵐ y ∂κ x, y ∈ G := by
      simpa using measure_eq_zero_iff_ae_notMem.mp (hx hxG)
    filter_upwards [hx1, hxG'] with y hy hyG using hy hyG

/-- If a measurable set `G` of finite measure is absorbing almost everywhere with respect to an
invariant measure of a Markov kernel, then so is its complement. -/
theorem Invariant.ae_apply_eq_zero_of_compl [IsMarkovKernel κ] (hπ : Invariant κ π)
    (hG : MeasurableSet G) (hπG : π G ≠ ∞) (h : ∀ᵐ x ∂π, x ∈ G → κ x Gᶜ = 0) :
    ∀ᵐ x ∂π, x ∈ Gᶜ → κ x G = 0 := by
  have h1 : ∫⁻ x, κ x G ∂π = π G := by
    rw [← Measure.bind_apply hG κ.aemeasurable, hπ.def]
  have h2 : ∫⁻ x in G, κ x G ∂π = π G := by
    rw [← setLIntegral_one]
    refine setLIntegral_congr_fun_ae hG ?_
    filter_upwards [h] with x hx hxG using (prob_compl_eq_zero_iff hG).mp (hx hxG)
  have h3 : ∫⁻ x in Gᶜ, κ x G ∂π = 0 := by
    have h_add := lintegral_add_compl (μ := π) (fun x ↦ κ x G) hG
    rw [h1, h2] at h_add
    exact (ENNReal.add_right_inj hπG).mp (by rw [h_add, add_zero])
  rwa [setLIntegral_eq_zero_iff hG.compl (κ.measurable_coe hG)] at h3

end Absorbing

end ProbabilityTheory.Kernel
