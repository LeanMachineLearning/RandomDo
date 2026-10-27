/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.DifferentialPrivacy.Gaussian
import Mathlib.Tactic

/-!
# Calibrating Gaussian noise

For `ε > 0` and `0 < δ ≤ 1`, put `t = sqrt (2 log (1/δ))` and
`c = (t + sqrt (t² + 2ε)) / (2ε)`. Standard deviation `c * Δ` suffices for a query of
ℓ₂ sensitivity `Δ`. This solves the Gaussian Chernoff-bound inequality exactly, works for all
positive `ε`, and does not require the `ε < 1` restriction of the classical `1.25/δ` formula.
It is a sufficient calibration, not the optimal analytic Gaussian calibration.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace DifferentialPrivacy

/-- Gaussian tail parameter `sqrt (2 log (1/δ))`, written without a reciprocal inside the log. -/
noncomputable def gaussianTail (δ : ℝ≥0) : ℝ≥0 :=
  .mk (Real.sqrt (-2 * Real.log δ)) (Real.sqrt_nonneg _)

/-- Noise multiplier for a Gaussian mechanism. Valid privacy calibration requires `ε > 0`
and `0 < δ ≤ 1`; the function is total to simplify use in definitions. -/
noncomputable def gaussianNoiseMultiplier (ε δ : ℝ≥0) : ℝ≥0 :=
  (gaussianTail δ + NNReal.sqrt ((gaussianTail δ) ^ 2 + 2 * ε)) / (2 * ε)

theorem gaussianTail_exp {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.exp (-(gaussianTail δ : ℝ) ^ 2 / 2) = δ := by
  have hlog : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos (by positivity) hδ1
  have hs : 0 ≤ -2 * Real.log (δ : ℝ) := by linarith
  simp only [gaussianTail, NNReal.coe_mk, Real.sq_sqrt hs]
  convert Real.exp_log (show 0 < (δ : ℝ) from hδ) using 1
  congr 1
  ring

theorem gaussianNoiseMultiplier_pos {ε : ℝ≥0} (hε : 0 < ε) (δ : ℝ≥0) :
    0 < gaussianNoiseMultiplier ε δ := by
  unfold gaussianNoiseMultiplier
  have hs : 0 < (gaussianTail δ) ^ 2 + 2 * ε := by positivity
  exact div_pos (add_pos_of_nonneg_of_pos (by positivity) (NNReal.sqrt_pos.mpr hs))
    (by positivity)

/-- The calibrated multiplier makes the Gaussian privacy-loss bound exactly `ε`. -/
theorem gaussianNoiseMultiplier_budget {ε : ℝ≥0} (hε : 0 < ε) (δ : ℝ≥0) :
    1 / (2 * (gaussianNoiseMultiplier ε δ : ℝ) ^ 2) +
      1 / (gaussianNoiseMultiplier ε δ : ℝ) * gaussianTail δ = ε := by
  let t : ℝ := gaussianTail δ
  let s : ℝ := Real.sqrt (t ^ 2 + 2 * ε)
  have ht : 0 ≤ t := (gaussianTail δ).coe_nonneg
  have he : 0 < (ε : ℝ) := hε
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = t ^ 2 + 2 * ε := Real.sq_sqrt (by positivity)
  have hc : 0 < (gaussianNoiseMultiplier ε δ : ℝ) := gaussianNoiseMultiplier_pos hε δ
  have hinv : (gaussianNoiseMultiplier ε δ : ℝ)⁻¹ = s - t := by
    simp only [gaussianNoiseMultiplier, NNReal.coe_div, NNReal.coe_add, Real.coe_sqrt,
      NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_ofNat]
    change (((t + s) / (2 * (ε : ℝ)))⁻¹) = s - t
    rw [inv_div]
    apply (div_eq_iff (by positivity : t + s ≠ 0)).mpr
    nlinarith
  calc
    _ = ((gaussianNoiseMultiplier ε δ : ℝ)⁻¹) ^ 2 / 2 +
        (gaussianNoiseMultiplier ε δ : ℝ)⁻¹ * t := by
      dsimp [t]
      field_simp
    _ = (s - t) ^ 2 / 2 + (s - t) * t := by rw [hinv]
    _ = ε := by nlinarith

/-- A convenient standard deviation for a query of sensitivity `Δ`. -/
noncomputable def gaussianStddev (Δ ε δ : ℝ≥0) : ℝ≥0 := gaussianNoiseMultiplier ε δ * Δ

private theorem scaled_budget {Δ ε δ : ℝ≥0} (hΔ : 0 < Δ) (hε : 0 < ε) :
    (Δ : ℝ) ^ 2 / (2 * (gaussianStddev Δ ε δ : ℝ) ^ 2) +
      (Δ : ℝ) / (gaussianStddev Δ ε δ : ℝ) * gaussianTail δ ≤ ε := by
  have hc : 0 < (gaussianNoiseMultiplier ε δ : ℝ) := gaussianNoiseMultiplier_pos hε δ
  have hd : 0 < (Δ : ℝ) := hΔ
  rw [← gaussianNoiseMultiplier_budget hε δ]
  apply le_of_eq
  simp only [gaussianStddev, NNReal.coe_mul]
  field_simp

variable {X ι : Type*} [Fintype ι]

/-- A Gaussian mechanism calibrated directly from `(ε, δ)` is differentially private. -/
theorem calibratedGaussian_approxDP {adj : X → X → Prop} {f : X → EuclideanSpace ℝ ι}
    {Δ ε δ : ℝ≥0} (hf : HasSensitivity adj f Δ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP adj ε δ (gaussianMechanism f (gaussianStddev Δ ε δ)) := by
  by_cases hΔ : Δ = 0
  · subst Δ
    exact gaussianMechanism_of_zero_sensitivity hf _ _ _
  · have hΔ' : 0 < Δ := bot_lt_iff_ne_bot.mpr hΔ
    exact gaussianMechanism_approxDP hf
      (mul_pos (gaussianNoiseMultiplier_pos hε δ) hΔ')
      (scaled_budget hΔ' hε) (gaussianTail_exp hδ hδ1).le

theorem calibratedGaussianReal_approxDP {adj : X → X → Prop} {f : X → ℝ}
    {Δ ε δ : ℝ≥0} (hf : HasSensitivity adj f Δ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP adj ε δ (gaussianMechanismReal f (gaussianStddev Δ ε δ)) := by
  by_cases hΔ : Δ = 0
  · subst Δ
    exact gaussianMechanismReal_of_zero_sensitivity hf _ _ _
  · have hΔ' : 0 < Δ := bot_lt_iff_ne_bot.mpr hΔ
    exact gaussianMechanismReal_approxDP hf
      (mul_pos (gaussianNoiseMultiplier_pos hε δ) hΔ')
      (scaled_budget hΔ' hε) (gaussianTail_exp hδ hδ1).le

variable {α : Type*}

/-- A calibrated noisy mean satisfies approximate DP for any adjacency with the proved mean
sensitivity bound. Both insertion/removal and replacement corollaries follow below. -/
theorem gaussianMean_calibrated {adj : Dataset α → Dataset α → Prop}
    {f : α → EuclideanSpace ℝ ι} {D ε δ : ℝ≥0} {n : ℕ}
    (hf : HasSensitivity adj (empiricalMean f) ((D : ℝ) / n))
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP adj ε δ (gaussianMean f D (gaussianNoiseMultiplier ε δ) n) := by
  simpa only [gaussianMean, gaussianStddev, mul_div_assoc] using
    calibratedGaussian_approxDP (Δ := D / n) hf hε hδ hδ1

theorem gaussianMeanReal_calibrated {adj : Dataset α → Dataset α → Prop}
    {f : α → ℝ} {D ε δ : ℝ≥0} {n : ℕ}
    (hf : HasSensitivity adj (empiricalMean f) ((D : ℝ) / n))
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP adj ε δ (gaussianMeanReal f D (gaussianNoiseMultiplier ε δ) n) := by
  simpa only [gaussianMeanReal, gaussianStddev, mul_div_assoc] using
    calibratedGaussianReal_approxDP (Δ := D / n) hf hε hδ hδ1

theorem gaussianMean_calibrated_addRemove {f : α → EuclideanSpace ℝ ι} {D ε δ : ℝ≥0}
    {n : ℕ} (hD : HasDiameter f D) (hn : 0 < n)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast n Dataset.AddRemove) ε δ
      (gaussianMean f D (gaussianNoiseMultiplier ε δ) n) :=
  gaussianMean_calibrated (sensitivity_empiricalMean_addRemove hD hn) hε hδ hδ1

theorem gaussianMean_calibrated_replaceOne {f : α → EuclideanSpace ℝ ι} {D ε δ : ℝ≥0}
    {n : ℕ} (hD : HasDiameter f D) (hn : 0 < n)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast n Dataset.ReplaceOne) ε δ
      (gaussianMean f D (gaussianNoiseMultiplier ε δ) n) :=
  gaussianMean_calibrated (sensitivity_empiricalMean_replaceOne hD hn) hε hδ hδ1

theorem gaussianMeanReal_calibrated_addRemove {f : α → ℝ} {D ε δ : ℝ≥0}
    {n : ℕ} (hD : HasDiameter f D) (hn : 0 < n)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast n Dataset.AddRemove) ε δ
      (gaussianMeanReal f D (gaussianNoiseMultiplier ε δ) n) :=
  gaussianMeanReal_calibrated (sensitivity_empiricalMean_addRemove hD hn) hε hδ hδ1

theorem gaussianMeanReal_calibrated_replaceOne {f : α → ℝ} {D ε δ : ℝ≥0}
    {n : ℕ} (hD : HasDiameter f D) (hn : 0 < n)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast n Dataset.ReplaceOne) ε δ
      (gaussianMeanReal f D (gaussianNoiseMultiplier ε δ) n) :=
  gaussianMeanReal_calibrated (sensitivity_empiricalMean_replaceOne hD hn) hε hδ hδ1

end DifferentialPrivacy
