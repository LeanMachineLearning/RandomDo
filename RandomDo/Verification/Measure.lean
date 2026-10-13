/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Monad.Instances
public import Std.Internal.Do.Triple
public import Std.Tactic.Do

/-!
# Quantitative Hoare logic for measures

The `WP` interpretation of a measure integrates nonnegative extended postexpectations.
Thus `Triple μ p Q EPost.Nil.mk` means `p ≤ ∫⁻ x, Q x ∂μ`. In particular, an indicator
postexpectation specifies a lower bound on the measure of an event. Measures need not have mass
one, and this interpretation performs no normalization.

These instances and specification lemmas extend Lean's stock `vcgen` tactic to `rdo`. Bind rules
retain their measurability hypotheses. No conjunction-preservation instance is provided:
integration is monotone but does not preserve pointwise minima.

The pinned Lean version exposes this experimental interface in `Std.Internal.Do`.
-/

@[expose] public section

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind Std.Internal.Do
open scoped ENNReal

namespace ENNReal

/-- The assertion lattice used by Lean's quantitative weakest-precondition interface. -/
noncomputable instance instLeanCompleteLattice : Lean.Order.CompleteLattice ℝ≥0∞ where
  rel := (· ≤ ·)
  rel_refl := le_rfl
  rel_trans := le_trans
  rel_antisymm := le_antisymm
  has_sup s := ⟨sSup {x | s x}, fun _ ↦ sSup_le_iff⟩

@[simp] theorem leanOrder_le_iff (x y : ℝ≥0∞) :
    Lean.Order.PartialOrder.rel x y ↔ x ≤ y := Iff.rfl

end ENNReal

namespace MeasureTheory.Measure

universe u

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A measure acts on postexpectations by the nonnegative Lebesgue integral. -/
noncomputable instance instWP : WP (Measure α) α ℝ≥0∞ EPost.Nil where
  wpTrans μ := ⟨fun Q _ ↦ ∫⁻ x, Q x ∂μ⟩
  wp_trans_monotone μ := by
    intro Q Q' _ _ _ hQ
    exact lintegral_mono hQ

theorem wp_eq_lintegral (μ : Measure α) (Q : α → ℝ≥0∞) (E : EPost.Nil) :
    wp μ Q E = ∫⁻ x, Q x ∂μ := rfl

@[fun_prop] theorem measurable_wp {Q : α → ℝ≥0∞} (hQ : Measurable Q) (E : EPost.Nil) :
    Measurable (fun μ : Measure α ↦ wp μ Q E) := measurable_lintegral hQ

theorem triple_iff (μ : Measure α) (p : ℝ≥0∞) (Q : α → ℝ≥0∞) (E : EPost.Nil) :
    Triple μ p Q E ↔ p ≤ ∫⁻ x, Q x ∂μ :=
  ⟨fun h ↦ h.le_wp, fun h ↦ ⟨h⟩⟩

@[simp] theorem wp_dirac [MeasurableSingletonClass α] (a : α)
    (Q : α → ℝ≥0∞) (E : EPost.Nil) : wp (dirac a) Q E = Q a :=
  lintegral_dirac a Q

theorem wp_dirac_of_measurable (a : α) {Q : α → ℝ≥0∞} (hQ : Measurable Q)
    (E : EPost.Nil) : wp (dirac a) Q E = Q a := lintegral_dirac' a hQ

theorem wp_bind_of_aemeasurable (μ : Measure α) (k : α → Measure β)
    (Q : β → ℝ≥0∞) (E : EPost.Nil) (hk : AEMeasurable k μ)
    (hQ : AEMeasurable Q (μ.bind k)) :
    wp (μ.bind k) Q E = wp μ (fun a ↦ wp (k a) Q E) E := lintegral_bind hk hQ

@[simp] theorem wp_bind (μ : Measure α) (k : α → Measure β)
    (Q : β → ℝ≥0∞) (E : EPost.Nil) (hk : Measurable k) (hQ : Measurable Q) :
    wp (μ.bind k) Q E = wp μ (fun a ↦ wp (k a) Q E) E :=
  wp_bind_of_aemeasurable μ k Q E hk.aemeasurable hQ.aemeasurable

theorem wp_mPure [MeasurableSingletonClass α] (a : α)
    (Q : α → ℝ≥0∞) (E : EPost.Nil) : wp (mPure a : Measure α) Q E = Q a :=
  wp_dirac a Q E

@[spec] theorem mPure_spec [MeasurableSingletonClass α] (a : α)
    (Q : α → ℝ≥0∞) (E : EPost.Nil) :
    Triple (mPure a : Measure α) (Q a) Q E := ⟨(wp_mPure a Q E).ge⟩

@[spec] theorem mPure_spec_of_measurable (a : α) (Q : α → ℝ≥0∞) (E : EPost.Nil)
    (hQ : Measurable Q) : Triple (mPure a : Measure α) (Q a) Q E :=
  ⟨(wp_dirac_of_measurable a hQ E).ge⟩

theorem wp_mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (k : α → Measure β) (Q : β → ℝ≥0∞) (E : EPost.Nil)
    (hk : Measurable k) (hQ : Measurable Q) :
    wp (μ >>=ₘ k) Q E = wp μ (fun a ↦ wp (k a) Q E) E := wp_bind μ k Q E hk hQ

@[spec] theorem mBind_spec {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (k : α → Measure β) (Q : β → ℝ≥0∞) (E : EPost.Nil)
    (hk : Measurable k) (hQ : Measurable Q) :
    Triple (μ >>=ₘ k) (wp μ (fun a ↦ wp (k a) Q E) E) Q E :=
  ⟨(wp_mBind μ k Q E hk hQ).ge⟩

theorem wp_indicator (μ : Measure α) {s : Set α} (hs : MeasurableSet s) (E : EPost.Nil) :
    wp μ (s.indicator fun _ ↦ 1) E = μ s := by
  simp [wp_eq_lintegral, hs]

theorem triple_indicator_iff (μ : Measure α) (p : ℝ≥0∞) {s : Set α}
    (hs : MeasurableSet s) (E : EPost.Nil) :
    Triple μ p (s.indicator fun _ ↦ 1) E ↔ p ≤ μ s := by
  rw [Triple.iff]
  rw [wp_indicator μ hs E]
  rfl

/-- Specifications for every measurable postexpectation imply domination of measures. -/
theorem le_of_forall_triple {μ ν : Measure α}
    (h : ∀ Q : α → ℝ≥0∞, Measurable Q → Triple μ (wp ν Q ⟨⟩) Q ⟨⟩) : ν ≤ μ := by
  refine le_intro fun s hs _ ↦ ?_
  have hQ := (h (s.indicator fun _ ↦ 1) (measurable_const.indicator hs)).le_wp
  simpa only [wp_indicator μ hs, wp_indicator ν hs, ENNReal.leanOrder_le_iff] using hQ

/-- For probability measures, lower bounds for all postexpectations determine the whole law. -/
theorem eq_of_forall_triple {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ Q : α → ℝ≥0∞, Measurable Q → Triple μ (wp ν Q ⟨⟩) Q ⟨⟩) : μ = ν :=
  (eq_of_le_of_isProbabilityMeasure (le_of_forall_triple h)).symm

end MeasureTheory.Measure
