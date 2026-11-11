/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.DifferentialPrivacy.Basic
public import RandomDo.DifferentialPrivacy.Mean
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# The Gaussian mechanism

Independent Gaussian noise with common standard deviation `σ` is added to each coordinate.
The output space is `EuclideanSpace`, so query sensitivity uses the ℓ₂ norm.
The variance passed to Mathlib is `σ ^ 2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace DifferentialPrivacy

variable {ι X α : Type*} [Fintype ι]

/-- The law of independent Gaussian coordinates with a common standard deviation. -/
noncomputable def gaussianVector (μ : EuclideanSpace ℝ ι) (σ : ℝ≥0) :
    ProbabilityMeasure (EuclideanSpace ℝ ι) :=
  ⟨(Measure.pi (fun i ↦ gaussianReal (μ i) (σ ^ 2))).map (WithLp.toLp 2),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩

/-- Release a vector-valued query with independent Gaussian noise in every coordinate. -/
noncomputable def gaussianMechanism (f : X → EuclideanSpace ℝ ι) (σ : ℝ≥0) :
    Mechanism X (EuclideanSpace ℝ ι) := fun x ↦ gaussianVector (f x) σ

/-- Scalar Gaussian mechanism, with standard deviation rather than variance as its parameter. -/
noncomputable def gaussianMechanismReal (f : X → ℝ) (σ : ℝ≥0) : Mechanism X ℝ :=
  Mechanism.ofMeasure (fun x ↦ gaussianReal (f x) (σ ^ 2)) (fun _ ↦ inferInstance)

/-- Gaussian noise added to an empirical vector mean. `n` is a public positive lower bound on
dataset size and `D` is a public upper bound on the domain's ℓ₂ diameter. `noiseMultiplier`
controls the privacy budget; the standard deviation is `noiseMultiplier * D / n`. -/
noncomputable def gaussianMean (f : α → EuclideanSpace ℝ ι)
    (D noiseMultiplier : ℝ≥0) (n : ℕ) : Mechanism (Dataset α) (EuclideanSpace ℝ ι) :=
  gaussianMechanism (empiricalMean f) (noiseMultiplier * D / n)

/-- Scalar specialization of the noisy mean. -/
noncomputable def gaussianMeanReal (f : α → ℝ) (D noiseMultiplier : ℝ≥0) (n : ℕ) :
    Mechanism (Dataset α) ℝ :=
  gaussianMechanismReal (empiricalMean f) (noiseMultiplier * D / n)

@[simp] theorem gaussianMechanismReal_zero (f : X → ℝ) (x : X) :
    (gaussianMechanismReal f 0 x : Measure ℝ) = Measure.dirac (f x) := by
  simp [gaussianMechanismReal, Mechanism.ofMeasure]

/-- The scalar mechanism is unbiased. -/
theorem integral_gaussianMechanismReal (f : X → ℝ) (σ : ℝ≥0) (x : X) :
    ∫ y, y ∂(gaussianMechanismReal f σ x : Measure ℝ) = f x :=
  integral_id_gaussianReal

namespace Gaussian

/-- Joint density of independent coordinates. -/
noncomputable def density (μ : ι → ℝ) (v : ℝ≥0) (z : ι → ℝ) : ℝ≥0∞ :=
  ∏ i, gaussianPDF (μ i) v (z i)

@[fun_prop] theorem measurable_density (μ : ι → ℝ) (v : ℝ≥0) :
    Measurable (density μ v) := by unfold density; fun_prop

theorem pi_eq_withDensity (μ : ι → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Measure.pi (fun i ↦ gaussianReal (μ i) v) =
      (Measure.pi (fun _ : ι ↦ (volume : Measure ℝ))).withDensity (density μ v) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hd : density μ v = fun z ↦ ENNReal.ofReal (∏ i, gaussianPDFReal (μ i) v (z i)) := by
    funext z
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ gaussianPDFReal_nonneg _ _ _)]
    rfl
  rw [hd, ← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun i ↦ (integrable_gaussianPDFReal (μ i) v).restrict))
    (ae_of_all _ (fun z ↦ Finset.prod_nonneg (fun i _ ↦ gaussianPDFReal_nonneg _ _ _))),
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ integral_nonneg (gaussianPDFReal_nonneg _ _))]
  exact Finset.prod_congr rfl (fun i _ ↦ (gaussianReal_apply_eq_integral (μ i) hv (s i)).symm)

/-- Squared Euclidean distance of two vectors written as coordinate functions. -/
noncomputable def sqDist (μ ν : ι → ℝ) : ℝ := ∑ i, (μ i - ν i) ^ 2

/-- The centered linear part of Gaussian privacy loss, before division by the variance. -/
noncomputable def linearNoise (μ ν z : ι → ℝ) : ℝ := ∑ i, (μ i - ν i) * (z i - μ i)

@[fun_prop] theorem measurable_linearNoise (μ ν : ι → ℝ) : Measurable (linearNoise μ ν) := by
  unfold linearNoise
  fun_prop

theorem sqDist_nonneg (μ ν : ι → ℝ) : 0 ≤ sqDist μ ν :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem sqDist_eq_norm (μ ν : EuclideanSpace ℝ ι) : sqDist μ ν = ‖μ - ν‖ ^ 2 := by
  simp [sqDist, EuclideanSpace.real_norm_sq_eq]

theorem sqDist_eq_zero_iff (μ ν : ι → ℝ) : sqDist μ ν = 0 ↔ μ = ν := by
  classical
  simp [sqDist, Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (μ i - ν i)),
    sub_eq_zero, funext_iff]

private theorem pdf_ratio (μ ν z : ℝ) (v : ℝ≥0) :
    gaussianPDF μ v z = ENNReal.ofReal
      (Real.exp (((μ - ν) * (z - μ) + (μ - ν) ^ 2 / 2) / v)) * gaussianPDF ν v z := by
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  simp only [gaussianPDFReal]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- Exact likelihood-ratio identity for Gaussians of equal variance. -/
theorem density_ratio (μ ν z : ι → ℝ) (v : ℝ≥0) :
    density μ v z = ENNReal.ofReal
      (Real.exp ((linearNoise μ ν z + sqDist μ ν / 2) / v)) * density ν v z := by
  classical
  unfold density
  calc
    _ = ∏ i, ENNReal.ofReal
        (Real.exp (((μ i - ν i) * (z i - μ i) + (μ i - ν i) ^ 2 / 2) / v)) *
          gaussianPDF (ν i) v (z i) :=
      Finset.prod_congr rfl (fun i _ ↦ pdf_ratio (μ i) (ν i) (z i) v)
    _ = _ := ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  simp only [linearNoise, sqDist, add_div, Finset.sum_add_distrib, Finset.sum_div]

/-- Centered real Gaussian variables are sub-Gaussian with their variance as parameter. -/
theorem subgaussian_centered (μ : ℝ) (v : ℝ≥0) :
    HasSubgaussianMGF (fun z ↦ z - μ) v (gaussianReal μ v) := by
  have h : HasSubgaussianMGF id v (gaussianReal 0 v) := by
    refine ⟨fun t ↦ integrable_exp_mul_gaussianReal t, fun t ↦ ?_⟩
    simp [mgf_id_gaussianReal]
  have hm : (gaussianReal μ v).map (fun z ↦ z - μ) = gaussianReal 0 v := by
    simp [gaussianReal_map_sub_const]
  rw [← hm] at h
  exact h.of_map (by fun_prop)

/-- The centered privacy loss has sub-Gaussian parameter `v * ‖μ - ν‖₂²`. -/
theorem subgaussian_linearNoise (μ ν : ι → ℝ) (v : ℝ≥0) :
    HasSubgaussianMGF (linearNoise μ ν) (v * .mk (sqDist μ ν) (sqDist_nonneg μ ν))
      (Measure.pi (fun i ↦ gaussianReal (μ i) v)) := by
  classical
  have hi := iIndepFun_pi (μ := fun i ↦ gaussianReal (μ i) v)
    (X := fun i z ↦ (μ i - ν i) * (z - μ i)) (fun _ ↦ by fun_prop)
  have hc (i : ι) := (subgaussian_centered (μ i) v).const_mul (μ i - ν i)
  have hc' (i : ι) : HasSubgaussianMGF (fun z : ι → ℝ ↦ (μ i - ν i) * (z i - μ i))
      (.mk ((μ i - ν i) ^ 2) (sq_nonneg _) * v)
      (Measure.pi (fun i ↦ gaussianReal (μ i) v)) := by
    have hmap := (measurePreserving_eval (fun i ↦ gaussianReal (μ i) v) i).map_eq
    have hci := hc i
    rw [← hmap] at hci
    exact HasSubgaussianMGF.of_map (μ := Measure.pi (fun i ↦ gaussianReal (μ i) v))
      (Y := fun z : ι → ℝ ↦ z i) (measurable_pi_apply i).aemeasurable hci
  have h := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun i _ ↦ hc' i)
  convert h using 1
  · rfl
  · apply NNReal.eq
    simp [sqDist, Finset.mul_sum, mul_comm]

/-- A dimension-independent Gaussian tail estimate in the direction between two query values. -/
theorem linearNoise_tail (μ ν : ι → ℝ) {σ : ℝ≥0} (hσ : 0 < σ) (hne : μ ≠ ν)
    (t : ℝ≥0) :
    (Measure.pi (fun i ↦ gaussianReal (μ i) (σ ^ 2)))
        {z | (t : ℝ) * σ * Real.sqrt (sqDist μ ν) < linearNoise μ ν z} ≤
      ENNReal.ofReal (Real.exp (-(t : ℝ) ^ 2 / 2)) := by
  have hs : 0 < sqDist μ ν := lt_of_le_of_ne (sqDist_nonneg μ ν)
    (Ne.symm (fun h ↦ hne ((sqDist_eq_zero_iff μ ν).mp h)))
  have hσ' : 0 < (σ : ℝ) := hσ
  have ht : 0 ≤ (t : ℝ) * σ * Real.sqrt (sqDist μ ν) := by positivity
  have h := (subgaussian_linearNoise μ ν (σ ^ 2)).measure_ge_le ht
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_mk] at h
  have heq : -((t : ℝ) * σ * Real.sqrt (sqDist μ ν)) ^ 2 /
      (2 * ((σ : ℝ) ^ 2 * sqDist μ ν)) = -(t : ℝ) ^ 2 / 2 := by
    simp only [mul_pow, Real.sq_sqrt hs.le]
    field_simp
  rw [heq] at h
  calc
    _ ≤ (Measure.pi (fun i ↦ gaussianReal (μ i) (σ ^ 2)))
        {z | (t : ℝ) * σ * Real.sqrt (sqDist μ ν) ≤ linearNoise μ ν z} :=
      measure_mono (fun z (hz : (t : ℝ) * σ * Real.sqrt (sqDist μ ν) < linearNoise μ ν z) ↦ hz.le)
    _ ≤ _ := (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr h

/-- Gaussian event inequality from sensitivity and a tail parameter. This is the quantitative
core of the Gaussian mechanism, including the case of equal query answers. -/
theorem distributionLE_pi (μ ν : ι → ℝ) {σ Δ ε δ t : ℝ≥0} (hσ : 0 < σ)
    (hΔ : Real.sqrt (sqDist μ ν) ≤ Δ)
    (hbudget : (Δ : ℝ) ^ 2 / (2 * (σ : ℝ) ^ 2) + (Δ : ℝ) / σ * t ≤ ε)
    (htail : Real.exp (-(t : ℝ) ^ 2 / 2) ≤ δ) :
    DistributionLE ε δ (Measure.pi (fun i ↦ gaussianReal (μ i) (σ ^ 2)))
      (Measure.pi (fun i ↦ gaussianReal (ν i) (σ ^ 2))) := by
  classical
  by_cases heq : μ = ν
  · subst ν
    exact (DistributionLE.refl _).mono (by positivity) (by positivity)
  have hσ' : 0 < (σ : ℝ) := hσ
  have hv : σ ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hσ)
  have hs : sqDist μ ν ≤ (Δ : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt (sqDist_nonneg μ ν), Real.sqrt_nonneg (sqDist μ ν),
      sq_nonneg ((Δ : ℝ) - Real.sqrt (sqDist μ ν))]
  let G : Set (ι → ℝ) := {z | linearNoise μ ν z ≤ (t : ℝ) * σ * Real.sqrt (sqDist μ ν)}
  have hG : MeasurableSet G := measurableSet_le (measurable_linearNoise μ ν) measurable_const
  have hgood (z : ι → ℝ) (hz : z ∈ G) :
      density μ (σ ^ 2) z ≤ ENNReal.ofReal (Real.exp ε) * density ν (σ ^ 2) z := by
    change linearNoise μ ν z ≤ (t : ℝ) * σ * Real.sqrt (sqDist μ ν) at hz
    rw [density_ratio μ ν z]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    change (linearNoise μ ν z + sqDist μ ν / 2) / (σ : ℝ) ^ 2 ≤ ε
    calc
      _ ≤ ((t : ℝ) * σ * Real.sqrt (sqDist μ ν) + sqDist μ ν / 2) / (σ : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (add_le_add hz le_rfl) (sq_nonneg _)
      _ = sqDist μ ν / (2 * (σ : ℝ) ^ 2) + Real.sqrt (sqDist μ ν) / σ * t := by
        field_simp
        ring
      _ ≤ (Δ : ℝ) ^ 2 / (2 * (σ : ℝ) ^ 2) + (Δ : ℝ) / σ * t := by gcongr
      _ ≤ ε := hbudget
  apply DistributionLE.of_goodSet hG
  · intro A hA
    rw [pi_eq_withDensity μ hv, pi_eq_withDensity ν hv,
      withDensity_apply _ (hA.inter hG), withDensity_apply _ hA]
    calc
      _ ≤ ∫⁻ z in A ∩ G, ENNReal.ofReal (Real.exp ε) * density ν (σ ^ 2) z :=
        setLIntegral_mono (by fun_prop) (fun z hz ↦ hgood z hz.2)
      _ ≤ ∫⁻ z in A, ENNReal.ofReal (Real.exp ε) * density ν (σ ^ 2) z :=
        lintegral_mono' (Measure.restrict_mono_set _ Set.inter_subset_left) le_rfl
      _ = _ := lintegral_const_mul _ (measurable_density ν (σ ^ 2))
  · change (Measure.pi (fun i ↦ gaussianReal (μ i) (σ ^ 2)))
        {z | ¬ linearNoise μ ν z ≤ (t : ℝ) * σ * Real.sqrt (sqDist μ ν)} ≤ δ
    simp only [not_le]
    exact (linearNoise_tail μ ν hσ heq t).trans (by
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal htail)

end Gaussian

/-- The Gaussian mechanism is `(ε, δ)`-DP whenever its sensitivity, standard deviation, and
tail parameter satisfy the displayed scalar inequalities. This bound is independent of the
number of output coordinates. -/
theorem gaussianMechanism_approxDP {adj : X → X → Prop} {f : X → EuclideanSpace ℝ ι}
    {σ Δ ε δ t : ℝ≥0} (hf : HasSensitivity adj f Δ) (hσ : 0 < σ)
    (hbudget : (Δ : ℝ) ^ 2 / (2 * (σ : ℝ) ^ 2) + (Δ : ℝ) / σ * t ≤ ε)
    (htail : Real.exp (-(t : ℝ) ^ 2 / 2) ≤ δ) : ApproxDP adj ε δ (gaussianMechanism f σ) := by
  intro x y hxy
  apply DistributionLE.map (f := WithLp.toLp 2) _ (by fun_prop)
  apply Gaussian.distributionLE_pi (⇑(f x)) (⇑(f y)) hσ _ hbudget htail
  simpa [Gaussian.sqDist_eq_norm, Real.sqrt_sq (norm_nonneg _)] using hf hxy

/-- Scalar version of the Gaussian privacy theorem. -/
theorem gaussianMechanismReal_approxDP {adj : X → X → Prop} {f : X → ℝ}
    {σ Δ ε δ t : ℝ≥0} (hf : HasSensitivity adj f Δ) (hσ : 0 < σ)
    (hbudget : (Δ : ℝ) ^ 2 / (2 * (σ : ℝ) ^ 2) + (Δ : ℝ) / σ * t ≤ ε)
    (htail : Real.exp (-(t : ℝ) ^ 2 / 2) ≤ δ) : ApproxDP adj ε δ (gaussianMechanismReal f σ) := by
  intro x y hxy
  have h := Gaussian.distributionLE_pi (fun _ : Fin 1 ↦ f x) (fun _ : Fin 1 ↦ f y)
    hσ (by simpa [Gaussian.sqDist, Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using hf hxy)
    hbudget htail
  have hm := h.map (measurable_pi_apply (0 : Fin 1))
  change DistributionLE ε δ (gaussianReal (f x) (σ ^ 2)) (gaussianReal (f y) (σ ^ 2))
  simpa only [(measurePreserving_eval (fun _ : Fin 1 ↦ gaussianReal (f x) (σ ^ 2)) 0).map_eq,
    (measurePreserving_eval (fun _ : Fin 1 ↦ gaussianReal (f y) (σ ^ 2)) 0).map_eq] using hm

/-- A query of zero sensitivity needs no noise. -/
theorem gaussianMechanism_of_zero_sensitivity {adj : X → X → Prop}
    {f : X → EuclideanSpace ℝ ι} (hf : HasSensitivity adj f 0) (σ ε δ : ℝ≥0) :
    ApproxDP adj ε δ (gaussianMechanism f σ) := by
  intro x y hxy
  have h : f x = f y := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (hf hxy) (norm_nonneg _)))
  simp only [gaussianMechanism, h]
  exact (DistributionLE.refl _).mono (by positivity) (by positivity)

theorem gaussianMechanismReal_of_zero_sensitivity {adj : X → X → Prop}
    {f : X → ℝ} (hf : HasSensitivity adj f 0) (σ ε δ : ℝ≥0) :
    ApproxDP adj ε δ (gaussianMechanismReal f σ) := by
  intro x y hxy
  have h : f x = f y := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (hf hxy) (norm_nonneg _)))
  simp only [gaussianMechanismReal, Mechanism.ofMeasure, h]
  exact (DistributionLE.refl _).mono (by positivity) (by positivity)

/-- Privacy of the noisy mean under insertion/removal adjacency and a public minimum size. -/
theorem gaussianMean_approxDP {f : α → EuclideanSpace ℝ ι} {D noiseMultiplier ε δ t : ℝ≥0}
    {n : ℕ} (hD : HasDiameter f D) (hn : 0 < n) (hσ : 0 < noiseMultiplier * D / n)
    (hbudget : ((D : ℝ) / n) ^ 2 / (2 * ((noiseMultiplier : ℝ) * D / n) ^ 2) +
      ((D : ℝ) / n) / ((noiseMultiplier : ℝ) * D / n) * t ≤ ε)
    (htail : Real.exp (-(t : ℝ) ^ 2 / 2) ≤ δ) :
    ApproxDP (Dataset.AtLeast n Dataset.AddRemove) ε δ (gaussianMean f D noiseMultiplier n) :=
  gaussianMechanism_approxDP (Δ := D / n)
    (sensitivity_empiricalMean_addRemove hD hn) hσ hbudget htail

/-- The same fixed noise scale protects replacement adjacency. -/
theorem gaussianMean_replaceOne_approxDP {f : α → EuclideanSpace ℝ ι}
    {D noiseMultiplier ε δ t : ℝ≥0} {n : ℕ} (hD : HasDiameter f D) (hn : 0 < n)
    (hσ : 0 < noiseMultiplier * D / n)
    (hbudget : ((D : ℝ) / n) ^ 2 / (2 * ((noiseMultiplier : ℝ) * D / n) ^ 2) +
      ((D : ℝ) / n) / ((noiseMultiplier : ℝ) * D / n) * t ≤ ε)
    (htail : Real.exp (-(t : ℝ) ^ 2 / 2) ≤ δ) :
    ApproxDP (Dataset.AtLeast n Dataset.ReplaceOne) ε δ (gaussianMean f D noiseMultiplier n) :=
  gaussianMechanism_approxDP (Δ := D / n)
    (sensitivity_empiricalMean_replaceOne hD hn) hσ hbudget htail

end DifferentialPrivacy
