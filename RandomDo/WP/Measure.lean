/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.Instances.Measure
public import RandomDo.WP.MeasurableSpaceMonad
public import Std.WP.EStack

/-!
# Weakest preexpectations of measures

The weakest preexpectation of a measure is the integral of its nonnegative extended
postexpectation. Thus `Triple μ p Q estack⟨⟩` means `p ≤ ∫⁻ x, Q x ∂μ`. There is no normalization
and no restriction to probability measures.

This interpretation implements `WPMeasurableSpaceMonad`, so the same bind and map rules work
for qualitative and quantitative verification. Integration is monotone but does not in general
preserve conjunction (pointwise minimum); no such instance is supplied. The assertion lattice
itself does have finite meets distributing over arbitrary suprema, supplying the `PreservesSup`
instance needed by the generic well-founded loop specifications.
-/

@[expose] public section

open MeasureTheory Std.WP
open scoped ENNReal

namespace ENNReal

-- No core analogue: core provides assertion lattices for its qualitative interpretations.
-- This uses mathlib's complete lattice, as in `Verification/Measure.lean` at 6e9f206.
noncomputable instance instLeanCompleteLattice : Lean.Order.CompleteLattice ℝ≥0∞ where
  rel := (· ≤ ·)
  rel_refl := le_rfl
  rel_trans := le_trans
  rel_antisymm := le_antisymm
  has_sup s := ⟨sSup {x | s x}, fun _ => sSup_le_iff⟩

@[simp] theorem leanOrder_le_iff (x y : ℝ≥0∞) :
    Lean.Order.PartialOrder.rel x y ↔ x ≤ y := Iff.rfl

-- Identify core's assertion-lattice operations with mathlib's operations on ℝ≥0∞.
@[simp] theorem leanOrder_sup_eq_sSup (s : ℝ≥0∞ → Prop) :
    Lean.Order.CompleteLattice.sup s = sSup {x | s x} := by
  apply le_antisymm
  · exact Lean.Order.sup_le s (x := sSup {x | s x}) fun x hx => _root_.le_sSup hx
  · exact sSup_le fun x hx => Lean.Order.le_sup s hx

@[simp] theorem leanOrder_meet_eq_min (x y : ℝ≥0∞) :
    Lean.Order.meet x y = min x y := by
  apply le_antisymm
  · exact le_min (Lean.Order.meet_le_left x y) (Lean.Order.meet_le_right x y)
  · exact Lean.Order.le_meet (min x y) x y (min_le_left x y) (min_le_right x y)

@[simp] theorem leanOrder_top_eq : (Lean.Order.top : ℝ≥0∞) = ⊤ := by
  simp [Lean.Order.top]

open scoped Lean.Order in
@[simp] theorem leanOrder_bot_eq : (Lean.Order.bot : ℝ≥0∞) = 0 := by
  apply le_antisymm
  · exact Lean.Order.bot_le (0 : ℝ≥0∞)
  · exact bot_le

@[simp] theorem leanOrder_ofProp_eq (p : Prop) [Decidable p] :
    (Lean.Order.CompleteLattice.ofProp p : ℝ≥0∞) = if p then ⊤ else 0 := by
  by_cases h : p <;> simp [h]

-- Analogue of core's instance for Prop. Here minimum distributes over arbitrary suprema
-- in the quantitative assertion lattice. This is a property of assertions themselves;
-- it does not require integration to preserve minimum.
#check Lean.Order.instPreservesSupMeet

instance (x : ℝ≥0∞) : Lean.Order.PreservesSup (Lean.Order.meet x) where
  map_sup s := by
    simp only [leanOrder_sup_eq_sSup, leanOrder_meet_eq_min]
    rw [inf_sSup_eq, ← sSup_image]
    congr 1
    ext y
    simp [eq_comm]

end ENNReal

namespace MeasureTheory.Measure

-- Core's `WPMonad` has no `Measure` instance. The integral interpretation follows
-- `Verification/Measure.lean` at 6e9f206; the new part packages its measurability and monad laws
-- in `WPMeasurableSpaceMonad`, rather than a separate collection of tactic specifications.
#check Std.WP.WPMonad

noncomputable instance : WPMeasurableSpaceMonad Measure ℝ≥0∞ EStack⟨⟩ where
  toWP _ :=
    { wpTrans := fun μ => ⟨fun Q _ => ∫⁻ x, Q x ∂μ⟩
      wp_trans_monotone := fun _ _ _ _ _ _ hQ => lintegral_mono hQ }
  measurable_wp hQ _ := measurable_lintegral hQ
  mPure_le_wp_mPure a _ _ hQ := (lintegral_dirac' a hQ).symm.le
  mBind_le_wp_mBind _ _ _ _ hf hQ := (lintegral_bind hf.aemeasurable hQ.aemeasurable).symm.le

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

-- No core analogues: these expose the quantitative interpretation for calculations.
theorem wp_eq_lintegral (μ : Measure α) (Q : α → ℝ≥0∞) (E : EStack⟨⟩) :
    wp μ Q E = ∫⁻ x, Q x ∂μ := rfl

theorem triple_iff (μ : Measure α) (p : ℝ≥0∞) (Q : α → ℝ≥0∞) (E : EStack⟨⟩) :
    Triple μ p Q E ↔ p ≤ ∫⁻ x, Q x ∂μ :=
  ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩

@[simp] theorem wp_dirac (a : α) {Q : α → ℝ≥0∞} (hQ : Measurable Q) (E : EStack⟨⟩) :
    wp (dirac a) Q E = Q a := lintegral_dirac' a hQ

@[simp] theorem wp_bind (μ : Measure α) (f : α → Measure β)
    (Q : β → ℝ≥0∞) (E : EStack⟨⟩) (hf : Measurable f) (hQ : Measurable Q) :
    wp (μ.bind f) Q E = wp μ (fun a => wp (f a) Q E) E :=
  lintegral_bind hf.aemeasurable hQ.aemeasurable

theorem wp_indicator (μ : Measure α) {s : Set α} (hs : MeasurableSet s) (E : EStack⟨⟩) :
    wp μ (s.indicator 1) E = μ s := lintegral_indicator_one hs

end MeasureTheory.Measure
