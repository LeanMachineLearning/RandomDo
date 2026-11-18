/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.Instances.Measure.Loop
public import RandomDo.WP.Measure
public import RandomDo.WP.ForIn

/-!
# Quantitative verification of unbounded loops

A bounded subinvariant gives a lower bound on the loop's weakest preexpectation when the mass
of unfinished runs tends to zero. The finite bound makes the residual reward of those runs
vanish; a subinvariant alone would not justify this conclusion.

The `@[spec]` rules use the same `WhileInvariant` annotations and stock `vcgen` interface as
the generic well-founded rule. Almost-sure termination replaces a strictly decreasing variant,
allowing loops such as repeated independent sampling until success. This rule requires neither
a discrete state space nor an order on arbitrary measure-valued computations.

## Main theorems

* `Measure.le_wp_loop_of_terminates`: the bounded quantitative invariant rule.
* `Measure.mForInLoop_invariant_spec`: the rule for a loop with an `invariant` clause.
-/

@[expose] public section

open Std.WP Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

-- No core analogue: these integral identities expose the finite-exit interpretation.
-- The finite-horizon estimate and limit argument below adapt `Verification/While.lean`
-- at 6e9f206, itself built on Gaëtan's `loopExit`/`loopRun` semantics.
theorem wp_loop_eq_tsum (f : α → Measure (ForInStep α)) (b : α)
    (Q : α → ℝ≥0∞) (E : EStack⟨⟩) :
    wp (loop f b) Q E = ∑' n, wp (loopExit f n b) Q E :=
  lintegral_sum_measure _ _

theorem wp_loop {f : α → Measure (ForInStep α)} (hf : Measurable f) (b : α)
    {Q : α → ℝ≥0∞} (hQ : Measurable Q) (E : EStack⟨⟩) :
    wp (loop f b) Q E = wp (f b) (fun t => match t with
      | .done a => Q a | .yield a => wp (loop f a) Q E) E :=
  lintegral_loop hf b hQ

/-- A bounded subinvariant is at most the loop's postexpectation plus the maximum reward
of unfinished runs. This finite-horizon estimate needs no termination hypothesis. -/
theorem le_wp_loop_add_loopRun {f : α → Measure (ForInStep α)}
    (I Q : α → ℝ≥0∞) (C : ℝ≥0) (E : EStack⟨⟩)
    (hf : Measurable f) (hQ : Measurable Q) (hbound : ∀ b, I b ≤ C)
    (step : ∀ b, I b ≤ wp (f b) (fun t => match t with
      | .done a => Q a | .yield a => I a) E)
    (n : ℕ) (b : α) :
    I b ≤ wp (loop f b) Q E + C * loopRun f n b Set.univ := by
  induction n generalizing b with
  | zero => simpa using (hbound b).trans (le_add_left (le_refl (C : ℝ≥0∞)))
  | succ n ih =>
    have hW : Measurable (fun a => wp (loop f a) Q E) := by fun_prop
    have hRun : Measurable (fun a => loopRun f n a Set.univ) :=
      (measurable_coe MeasurableSet.univ).comp (measurable_loopRun hf n)
    calc
      I b ≤ wp (f b) (fun t => match t with | .done a => Q a | .yield a => I a) E := step b
      _ ≤ ∫⁻ t, (match t with | .done a => Q a | .yield a => wp (loop f a) Q E) +
          (C : ℝ≥0∞) * (match t with | .done _ => 0 | .yield a => loopRun f n a Set.univ)
          ∂f b := by
        apply lintegral_mono
        intro t
        cases t with
        | done a => simp
        | yield a => exact ih a
      _ = wp (loop f b) Q E + C * loopRun f (n + 1) b Set.univ := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
          loopRun_succ_apply_univ hf, wp_loop hf b hQ E]
        rfl

/-- Almost-sure termination makes the residual contribution of a bounded subinvariant vanish.
The bound is on the invariant; the measurable postexpectation may be unbounded. -/
theorem le_wp_loop_of_terminates {f : α → Measure (ForInStep α)}
    (I Q : α → ℝ≥0∞) (C : ℝ≥0) (E : EStack⟨⟩)
    (hf : Measurable f) (hQ : Measurable Q) (hbound : ∀ b, I b ≤ C)
    (step : ∀ b, I b ≤ wp (f b) (fun t => match t with
      | .done a => Q a | .yield a => I a) E)
    (b : α) (hterm : Terminates f b) : I b ≤ wp (loop f b) Q E := by
  have hlim : Tendsto (fun n => wp (loop f b) Q E + C * loopRun f n b Set.univ)
      atTop (𝓝 (wp (loop f b) Q E)) := by
    simpa using tendsto_const_nhds.add
      (ENNReal.Tendsto.const_mul hterm (Or.inr ENNReal.coe_ne_top))
  exact ge_of_tendsto hlim (Eventually.of_forall
    (fun n => le_wp_loop_add_loopRun I Q C E hf hQ hbound step n b))

-- Related core rule, not an identical analogue: a finite bound and vanishing tail mass
-- replace the well-founded variant. We do not assume that integration preserves meets.
#check Std.WP.Spec.forIn_loop

@[spec] theorem loop_spec (f : α → Measure (ForInStep α)) (b : α)
    (inv : WhileInvariant α ℝ≥0∞) (E : EStack⟨⟩)
    (hf : Measurable f) (hinv : Measurable (inv true))
    (hbound : ∃ C : ℝ≥0, ∀ a, inv false a ≤ C) (hterm : Terminates f b)
    (step : ∀ a, Triple (f a) (inv false a)
      (fun t => match t with | .done a' => inv true a' | .yield a' => inv false a') E) :
    Triple (loop f b) (inv false b) (fun a => inv true a) E := by
  obtain ⟨C, hC⟩ := hbound
  exact ⟨le_wp_loop_of_terminates _ _ C E hf hinv hC (fun a => (step a).le_wp) b hterm⟩

#check Std.WP.Spec.forIn_loop

@[spec] theorem mForIn_loop_spec (l : Lean.Loop) (b : α)
    (f : Unit → α → Measure (ForInStep α)) (inv : WhileInvariant α ℝ≥0∞) (E : EStack⟨⟩)
    (hf : Measurable (f ())) (hinv : Measurable (inv true))
    (hbound : ∃ C : ℝ≥0, ∀ a, inv false a ≤ C) (hterm : Terminates (f ()) b)
    (step : ∀ a, Triple (f () a) (inv false a)
      (fun t => match t with | .done a' => inv true a' | .yield a' => inv false a') E) :
    Triple (mForIn l b f) (inv false b) (fun a => inv true a) E :=
  loop_spec (f ()) b inv E hf hinv hbound hterm step

#check Std.WP.Spec.forInLoop_invariant

@[spec] theorem mForInLoop_invariant_spec (l : Lean.Loop) (b : α)
    (f : Unit → α → Measure (ForInStep α)) (inv : Bool → α → ℝ≥0∞) (E : EStack⟨⟩)
    (hf : Measurable (f ())) (hinv : Measurable (inv true))
    (hbound : ∃ C : ℝ≥0, ∀ a, inv false a ≤ C) (hterm : Terminates (f ()) b)
    (step : ∀ a, Triple (f () a) (binderNameHint a (inv false) <| inv false a)
      (fun t => match t with | .done a' => inv true a' | .yield a' => inv false a') E) :
    Triple (MeasureTheory.WP.mForInLoopWithInvariant l b f (WhileInvariant.mk inv))
      (inv false b) (fun a => binderNameHint a (inv true) <| inv true a) E :=
  loop_spec (f ()) b (WhileInvariant.mk inv) E hf hinv hbound hterm step

end MeasureTheory.Measure
