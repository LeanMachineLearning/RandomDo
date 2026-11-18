/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Differential privacy

A `Mechanism X Y` assigns a probability distribution on `Y` to each input in `X`.
There is no measurable-space requirement on inputs: privacy compares individual inputs.
`ApproxDP` quantifies over measurable output events and an explicit adjacency relation.
`PureDP` is its specialization to `δ = 0`.

Privacy parameters are nonnegative reals. Allowing `δ ≥ 1` is convenient for bounds, although
only `δ < 1` is informative. No finite-precision sampler is identified with an exact real law.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace DifferentialPrivacy

universe u v w

/-- A probabilistic algorithm, specified by its output law at each input. -/
abbrev Mechanism (X : Type u) (Y : Type v) [MeasurableSpace Y] := X → ProbabilityMeasure Y

namespace Mechanism

variable {X : Type u} {Y : Type v} {Z : Type w}
  [MeasurableSpace Y] [MeasurableSpace Z]

/-- Package a measure-valued algorithm with proofs that all its laws have mass one. -/
def ofMeasure (M : X → Measure Y) (hM : ∀ x, IsProbabilityMeasure (M x)) : Mechanism X Y :=
  fun x ↦ ⟨M x, hM x⟩

/-- Measurable deterministic postprocessing of a mechanism. -/
noncomputable def postprocess (M : Mechanism X Y) (f : Y → Z) (hf : Measurable f) :
    Mechanism X Z := fun x ↦ (M x).map hf.aemeasurable

end Mechanism

variable {X : Type u} {Y : Type v} {Z : Type w}
  [MeasurableSpace Y] [MeasurableSpace Z]

/-- The directed event inequality underlying approximate differential privacy. Symmetry is
supplied by a symmetric adjacency relation when using `ApproxDP`. -/
def DistributionLE (ε δ : ℝ≥0) (μ ν : Measure Y) : Prop :=
  ∀ A, MeasurableSet A → μ A ≤ ENNReal.ofReal (Real.exp ε) * ν A + δ

/-- `(ε, δ)` differential privacy relative to `adj`. -/
def ApproxDP (adj : X → X → Prop) (ε δ : ℝ≥0) (M : Mechanism X Y) : Prop :=
  ∀ ⦃x x'⦄, adj x x' → DistributionLE ε δ (M x : Measure Y) (M x' : Measure Y)

/-- Pure `ε` differential privacy: `P(M x ∈ A) ≤ exp ε * P(M x' ∈ A)`. -/
def PureDP (adj : X → X → Prop) (ε : ℝ≥0) (M : Mechanism X Y) : Prop :=
  ApproxDP adj ε 0 M

namespace DistributionLE

variable {ε ε' δ δ' : ℝ≥0} {μ ν : Measure Y}

theorem refl (μ : Measure Y) : DistributionLE 0 0 μ μ := by
  intro A _
  simp

/-- A larger privacy budget preserves the event inequality. -/
theorem mono (h : DistributionLE ε δ μ ν) (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    DistributionLE ε' δ' μ ν := by
  intro A hA
  exact (h A hA).trans (add_le_add
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hε)) le_rfl)
    (ENNReal.coe_le_coe.mpr hδ))

theorem map (h : DistributionLE ε δ μ ν) {f : Y → Z} (hf : Measurable f) :
    DistributionLE ε δ (μ.map f) (ν.map f) := by
  intro A hA
  simpa only [Measure.map_apply hf hA] using h (f ⁻¹' A) (hf hA)

/-- It suffices to dominate the measure on a good event and bound its complement. -/
theorem of_goodSet {G : Set Y} (hG : MeasurableSet G)
    (hgood : ∀ A, MeasurableSet A → μ (A ∩ G) ≤ ENNReal.ofReal (Real.exp ε) * ν A)
    (hbad : μ Gᶜ ≤ δ) : DistributionLE ε δ μ ν := by
  intro A hA
  calc
    μ A = μ (A ∩ G) + μ (A \ G) := (measure_inter_add_sdiff A hG).symm
    _ ≤ ENNReal.ofReal (Real.exp ε) * ν A + δ :=
      add_le_add (hgood A hA) ((measure_mono (Set.sdiff_subset_compl A G)).trans hbad)

end DistributionLE

namespace ApproxDP

variable {adj adj' : X → X → Prop} {ε ε' δ δ' : ℝ≥0} {M : Mechanism X Y}

theorem mono (h : ApproxDP adj ε δ M) (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    ApproxDP adj ε' δ' M := fun _ _ hxx' ↦ (h hxx').mono hε hδ

/-- Privacy for a relation also holds for any subrelation. -/
theorem of_subrelation (h : ApproxDP adj ε δ M) (hadj : ∀ x x', adj' x x' → adj x x') :
    ApproxDP adj' ε δ M := fun _ _ hxx' ↦ h (hadj _ _ hxx')

theorem postprocess (h : ApproxDP adj ε δ M) {f : Y → Z} (hf : Measurable f) :
    ApproxDP adj ε δ (M.postprocess f hf) := fun _ _ hxx' ↦ (h hxx').map hf

/-- Preprocessing is allowed when it preserves adjacency. In particular this restricts a
mechanism to a public input domain, such as datasets of size at least `n`. -/
theorem precompose {W : Type*} {rel : W → W → Prop} (h : ApproxDP adj ε δ M)
    (f : W → X) (hf : ∀ x x', rel x x' → adj (f x) (f x')) :
    ApproxDP rel ε δ (M ∘ f) := fun _ _ hxx' ↦ h (hf _ _ hxx')

theorem const (adj : X → X → Prop) (μ : ProbabilityMeasure Y) :
    ApproxDP adj 0 0 (fun _ : X ↦ μ) := fun _ _ _ ↦ DistributionLE.refl (μ : Measure Y)

end ApproxDP

theorem pureDP_iff {adj : X → X → Prop} {ε : ℝ≥0} {M : Mechanism X Y} :
    PureDP adj ε M ↔ ∀ ⦃x x'⦄, adj x x' → ∀ A, MeasurableSet A →
      (M x : Measure Y) A ≤ ENNReal.ofReal (Real.exp ε) * (M x' : Measure Y) A := by
  simp [PureDP, ApproxDP, DistributionLE]

end DifferentialPrivacy
