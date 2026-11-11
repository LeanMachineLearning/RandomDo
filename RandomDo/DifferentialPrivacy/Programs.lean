/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.DifferentialPrivacy.Calibration
public import RandomDo.Tactic.Computable.Polymorphic.Polymorphic
public import RandomDo.Tactic.Computable.Polymorphic.Scalar
public import RandomDo.Monad.Notation
public import RandomDo.Measurable

/-!
# Gaussian mechanisms as `rdo` programs

`gaussianMeanRealProgram` and `gaussianMeanProgram` implement the whole noisy-mean algorithm:
compute the empirical mean, scale the noise by the public domain diameter and minimum size,
and add independent Gaussian noise. They use the same polymorphic distribution interface as
other RandomDo programs. There is no separate implementation for an execution backend.

At `m := Measure`, the programs have the Gaussian laws proved below, and their privacy theorems
apply directly to these programs. Instantiate the same definitions with another interpretation
to run them. The privacy proofs concern the exact real interpretation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DifferentialPrivacy

universe v

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {R V : Type} [MeasurableSpace R] [Zero R] [Add R] [Mul V] [HasGaussian m R V R]

/-- Draw a query answer with Gaussian noise of standard deviation `σ`.
`HasGaussian` takes variance, so the standard deviation is squared here. -/
def gaussianProgram (center : R) (σ : V) : m R := rdo
  let noise ← HasGaussian.gaussian (m := m) (0 : R) (σ * σ)
  return center + noise

/-- Draw independent Gaussian coordinates in index order. The dimension is public. -/
def gaussianCoordinates : {d : ℕ} → (Fin d → R) → V → m (Fin d → R)
  | 0, _, _ => rdo return Fin.elim0
  | d + 1, center, σ => rdo
    let z ← gaussianProgram (m := m) (center 0) σ
    let zs ← gaussianCoordinates (fun i : Fin d ↦ center i.succ) σ
    return Fin.cons z zs

/-- Arithmetic mean using only operations available to polymorphic programs. No measurable
structure on records is needed, since the input dataset is fixed before sampling. -/
def meanValue {α : Type*} {R : Type} [Scalar R] (f : α → R) (xs : Dataset α) : R :=
  xs.foldr (fun x total ↦ f x + total) 0 / (xs.length : R)

/-- Add Gaussian noise to a scalar empirical mean. `D` is a public bound on the domain diameter,
`n` is a public positive lower bound on dataset size, and `c` is a public noise multiplier.
The noise standard deviation is `c * D / n`, independently of the private dataset size. -/
def gaussianMeanRealProgram {α : Type*} {R V : Type} [Scalar R] [Scalar V]
    [HasGaussian m R V R] (f : α → R) (D c : V) (n : ℕ) (xs : Dataset α) : m R := rdo
  let center := meanValue f xs
  let σ := c * D / (n : V)
  let z ← gaussianProgram (m := m) center σ
  return z

/-- Add independent Gaussian noise to every coordinate of an empirical mean. `D` bounds the
domain's ℓ₂ diameter; `n` and `c` have the same meaning as in `gaussianMeanRealProgram`.
The dimension is public and the same noise scale is used in every coordinate. -/
def gaussianMeanProgram {α : Type*} {R V : Type} [Scalar R] [Scalar V]
    [HasGaussian m R V R] {d : ℕ} (f : α → Fin d → R) (D c : V) (n : ℕ)
    (xs : Dataset α) : m (Fin d → R) := rdo
  let center := fun i ↦ meanValue (fun x ↦ f x i) xs
  let σ := c * D / (n : V)
  let z ← gaussianCoordinates (m := m) center σ
  return z

theorem gaussianProgram_real (center : ℝ) (σ : ℝ≥0) :
    gaussianProgram (m := Measure) center σ = gaussianReal center (σ ^ 2) := by
  simp only [gaussianProgram, HasGaussian.gaussian, mBind_def, mPure_def]
  rw [Measure.bind_dirac_eq_map _ (by fun_prop), gaussianReal_map_const_add]
  simp [pow_two]

/-- The exact interpretation of the scalar `rdo` program is the certified mechanism. -/
theorem gaussianProgram_eq_mechanism {X : Type*} (f : X → ℝ) (σ : ℝ≥0) (x : X) :
    gaussianProgram (m := Measure) (f x) σ = (gaussianMechanismReal f σ x : Measure ℝ) := by
  simpa [gaussianMechanismReal, Mechanism.ofMeasure] using gaussianProgram_real (f x) σ

/-- The exact interpretation of the recursive sampler has independent Gaussian coordinates. -/
theorem gaussianCoordinates_real {d : ℕ} (center : Fin d → ℝ) (σ : ℝ≥0) :
    gaussianCoordinates (m := Measure) center σ =
      Measure.pi (fun i ↦ gaussianReal (center i) (σ ^ 2)) := by
  induction d with
  | zero =>
    exact (Measure.pi_of_empty (fun i ↦ gaussianReal (center i) (σ ^ 2)) Fin.elim0).symm
  | succ d ih =>
    simp only [gaussianCoordinates, gaussianProgram_real, ih,
      mBind_def, mPure_def]
    have hcons (a : ℝ) : Measurable (Fin.cons (n := d) (α := fun _ ↦ ℝ) a) := by
      apply measurable_pi_lambda
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
      · simpa using (measurable_pi_apply j : Measurable (fun z : Fin d → ℝ ↦ z j))
    simp_rw [Measure.bind_dirac_eq_map _ (hcons _)]
    have hp := (measurePreserving_piFinSuccAbove
      (fun i ↦ gaussianReal (center i) (σ ^ 2)) (0 : Fin (d + 1))).symm.map_eq
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] at hp
    rw [← hp]
    ext A hA
    have hm : Measurable (fun a : ℝ ↦
        (Measure.pi (fun i : Fin d ↦ gaussianReal (center i.succ) (σ ^ 2))).map
          (Fin.cons (n := d) (α := fun _ ↦ ℝ) a)) := by
      apply Measure.measurable_of_measurable_coe
      intro B hB
      simp only [Measure.map_apply (hcons _) hB]
      exact measurable_measure_prodMk_left (measurable_finCons hB)
    rw [Measure.bind_apply hA hm.aemeasurable, Measure.map_apply measurable_finCons hA,
      Measure.prod_apply (measurable_finCons hA)]
    apply lintegral_congr_ae
    filter_upwards [] with a
    exact Measure.map_apply (hcons a) hA

/-- Mapping the coordinate program to Euclidean space gives the certified vector mechanism. -/
theorem gaussianCoordinates_eq_mechanism {X : Type*} {d : ℕ}
    (f : X → EuclideanSpace ℝ (Fin d)) (σ : ℝ≥0) (x : X) :
    (gaussianCoordinates (m := Measure) (⇑(f x)) σ).map (WithLp.toLp 2) =
      (gaussianMechanism f σ x : Measure (EuclideanSpace ℝ (Fin d))) := by
  rw [gaussianCoordinates_real]
  rfl

/-- The pure arithmetic in the program computes the mathematical empirical mean. -/
theorem meanValue_real {α : Type*} (f : α → ℝ) (xs : Dataset α) :
    meanValue f xs = empiricalMean f xs := by
  have hsum : xs.foldr (fun x total ↦ f x + total) 0 = (xs.map f).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [ih]
  simp only [meanValue, empiricalMean, hsum, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Taking a coordinate commutes with the empirical mean in Euclidean space. -/
theorem empiricalMean_apply {α : Type*} {d : ℕ} (f : α → EuclideanSpace ℝ (Fin d))
    (xs : Dataset α) (i : Fin d) :
    empiricalMean f xs i = empiricalMean (fun a ↦ f a i) xs := by
  have hsum : (xs.map f).sum i = (xs.map (fun a ↦ f a i)).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simpa using congrArg (f a i + ·) ih
  simpa only [empiricalMean, PiLp.smul_apply, smul_eq_mul] using
    congrArg ((xs.length : ℝ)⁻¹ * ·) hsum

/-- The exact law of the complete scalar `rdo` mean algorithm. -/
theorem gaussianMeanRealProgram_eq_mechanism {α : Type*} (f : α → ℝ)
    (D c : ℝ≥0) (n : ℕ) (xs : Dataset α) :
    gaussianMeanRealProgram (m := Measure) f D c n xs =
      (gaussianMeanReal f D c n xs : Measure ℝ) := by
  simp [gaussianMeanRealProgram, gaussianProgram_real, meanValue_real,
    gaussianMeanReal, gaussianMechanismReal, Mechanism.ofMeasure]

/-- The exact law of the complete vector `rdo` mean algorithm, in Euclidean coordinates. -/
theorem gaussianMeanProgram_eq_mechanism {α : Type*} {d : ℕ}
    (f : α → EuclideanSpace ℝ (Fin d)) (D c : ℝ≥0) (n : ℕ) (xs : Dataset α) :
    (gaussianMeanProgram (m := Measure) (fun a ↦ ⇑(f a)) D c n xs).map (WithLp.toLp 2) =
      (gaussianMean f D c n xs : Measure (EuclideanSpace ℝ (Fin d))) := by
  simpa [gaussianMeanProgram, meanValue_real, ← empiricalMean_apply, gaussianMean] using
    gaussianCoordinates_eq_mechanism (empiricalMean f) (c * D / n) xs

/-- The scalar program always denotes a probability measure, including at zero noise. -/
instance {α : Type*} (f : α → ℝ) (D c : ℝ≥0) (n : ℕ) (xs : Dataset α) :
    IsProbabilityMeasure (gaussianMeanRealProgram (m := Measure) f D c n xs) := by
  rw [gaussianMeanRealProgram_eq_mechanism]
  infer_instance

/-- The vector program always denotes a probability measure, including in dimension zero. -/
instance {α : Type*} {d : ℕ} (f : α → Fin d → ℝ) (D c : ℝ≥0) (n : ℕ) (xs : Dataset α) :
    IsProbabilityMeasure (gaussianMeanProgram (m := Measure) f D c n xs) := by
  simpa [gaussianMeanProgram, gaussianCoordinates_real] using
    (inferInstance : IsProbabilityMeasure
      (Measure.pi (fun i ↦ gaussianReal (meanValue (fun a ↦ f a i) xs) ((c * D / n) ^ 2))))

/-- The vector program's output law is the certified Euclidean law in ordinary coordinates. -/
theorem gaussianMeanProgram_eq_coordinateLaw {α : Type*} {d : ℕ}
    (f : α → EuclideanSpace ℝ (Fin d)) (D c : ℝ≥0) (n : ℕ) (xs : Dataset α) :
    gaussianMeanProgram (m := Measure) (fun a ↦ ⇑(f a)) D c n xs =
      (gaussianMean f D c n xs : Measure (EuclideanSpace ℝ (Fin d))).map WithLp.ofLp := by
  rw [← gaussianMeanProgram_eq_mechanism, Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- Privacy of the scalar `rdo` program, from any proved empirical-mean sensitivity bound.
`Mechanism.ofMeasure` only packages the program with its probability proof. -/
theorem gaussianMeanRealProgram_approxDP {α : Type*} {adj : Dataset α → Dataset α → Prop}
    {f : α → ℝ} {D ε δ : ℝ≥0} {n : ℕ}
    (hf : HasSensitivity adj (empiricalMean f) ((D : ℝ) / n))
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP adj ε δ (Mechanism.ofMeasure
      (gaussianMeanRealProgram (m := Measure) f D (gaussianNoiseMultiplier ε δ) n)
      (fun _ ↦ inferInstance)) := by
  intro xs ys hxy
  change DistributionLE ε δ (gaussianMeanRealProgram (m := Measure) _ _ _ _ xs)
    (gaussianMeanRealProgram (m := Measure) _ _ _ _ ys)
  simp only [gaussianMeanRealProgram_eq_mechanism]
  exact gaussianMeanReal_calibrated hf hε hδ hδ1 hxy

/-- Privacy of the vector `rdo` program. Sensitivity is measured in Euclidean space, so the
guarantee uses ℓ₂ sensitivity and has no extra factor depending on dimension. -/
theorem gaussianMeanProgram_approxDP {α : Type*} {d : ℕ}
    {adj : Dataset α → Dataset α → Prop} {f : α → EuclideanSpace ℝ (Fin d)}
    {D ε δ : ℝ≥0} {n : ℕ}
    (hf : HasSensitivity adj (empiricalMean f) ((D : ℝ) / n))
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP adj ε δ (Mechanism.ofMeasure
      (gaussianMeanProgram (m := Measure) (fun a ↦ ⇑(f a)) D (gaussianNoiseMultiplier ε δ) n)
      (fun _ ↦ inferInstance)) := by
  intro xs ys hxy
  change DistributionLE ε δ (gaussianMeanProgram (m := Measure) _ _ _ _ xs)
    (gaussianMeanProgram (m := Measure) _ _ _ _ ys)
  rw [gaussianMeanProgram_eq_coordinateLaw, gaussianMeanProgram_eq_coordinateLaw]
  exact (gaussianMean_calibrated hf hε hδ hδ1 hxy).map (by fun_prop)

/-- The scalar `rdo` mean program is private under insertion/removal of one record. -/
theorem gaussianMeanRealProgram_approxDP_addRemove {α : Type*} {f : α → ℝ}
    {D ε δ : ℝ≥0} {n : ℕ} (hD : HasDiameter f D) (hn : 0 < n)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast n Dataset.AddRemove) ε δ (Mechanism.ofMeasure
      (gaussianMeanRealProgram (m := Measure) f D (gaussianNoiseMultiplier ε δ) n)
      (fun _ ↦ inferInstance)) :=
  gaussianMeanRealProgram_approxDP (sensitivity_empiricalMean_addRemove hD hn) hε hδ hδ1

/-- The scalar `rdo` mean program is private under replacement of one record. -/
theorem gaussianMeanRealProgram_approxDP_replaceOne {α : Type*} {f : α → ℝ}
    {D ε δ : ℝ≥0} {n : ℕ} (hD : HasDiameter f D) (hn : 0 < n)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast n Dataset.ReplaceOne) ε δ (Mechanism.ofMeasure
      (gaussianMeanRealProgram (m := Measure) f D (gaussianNoiseMultiplier ε δ) n)
      (fun _ ↦ inferInstance)) :=
  gaussianMeanRealProgram_approxDP (sensitivity_empiricalMean_replaceOne hD hn) hε hδ hδ1

/-- The vector `rdo` mean program is private under insertion/removal of one record. -/
theorem gaussianMeanProgram_approxDP_addRemove {α : Type*} {d : ℕ}
    {f : α → EuclideanSpace ℝ (Fin d)} {D ε δ : ℝ≥0} {n : ℕ}
    (hD : HasDiameter f D) (hn : 0 < n) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast n Dataset.AddRemove) ε δ (Mechanism.ofMeasure
      (gaussianMeanProgram (m := Measure) (fun a ↦ ⇑(f a)) D (gaussianNoiseMultiplier ε δ) n)
      (fun _ ↦ inferInstance)) :=
  gaussianMeanProgram_approxDP (sensitivity_empiricalMean_addRemove hD hn) hε hδ hδ1

/-- The vector `rdo` mean program is private under replacement of one record. -/
theorem gaussianMeanProgram_approxDP_replaceOne {α : Type*} {d : ℕ}
    {f : α → EuclideanSpace ℝ (Fin d)} {D ε δ : ℝ≥0} {n : ℕ}
    (hD : HasDiameter f D) (hn : 0 < n) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast n Dataset.ReplaceOne) ε δ (Mechanism.ofMeasure
      (gaussianMeanProgram (m := Measure) (fun a ↦ ⇑(f a)) D (gaussianNoiseMultiplier ε δ) n)
      (fun _ ↦ inferInstance)) :=
  gaussianMeanProgram_approxDP (sensitivity_empiricalMean_replaceOne hD hn) hε hδ hδ1

end DifferentialPrivacy
