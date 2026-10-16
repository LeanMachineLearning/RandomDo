/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.ForMathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Small sets of a kernel

A set `C` is *small* for a kernel `κ : Kernel α α` if the measures `(κ ^ n) x` for `x ∈ C` have a
common component: there is an `n : ℕ` and a measure `ν` such that `ν ≤ (κ ^ n) x` for all `x ∈ C`.
When `κ` is the transition kernel of a Markov chain, this means that the chain forgets where it
started in `C` with positive probability after `n` steps.

## Main definitions

* `ProbabilityTheory.Kernel.IsSmallSet κ C n ν`: `ν ≤ (κ ^ n) x` for all `x ∈ C`.

## References

* [Meyn, S.P. and Tweedie, R.L., *Markov Chains and Stochastic Stability*][meyntweedie1993]
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {C C' : Set α} {n : ℕ}
  {ν ν' : Measure α}

/-- A set `C` is `(n, ν)`-small for the kernel `κ : Kernel α α` if `ν ≤ (κ ^ n) x` for all
`x ∈ C`.
Ref. *Meyn-Tweedie*, Section 5.2. -/
def IsSmallSet (κ : Kernel α α) (C : Set α) (n : ℕ) (ν : Measure α) : Prop :=
  ∀ x ∈ C, ν ≤ (κ ^ n) x

namespace IsSmallSet

lemma mono (h : IsSmallSet κ C n ν) (hC : C' ⊆ C) : IsSmallSet κ C' n ν :=
  fun x hx ↦ h x (hC hx)

lemma mono_measure (h : IsSmallSet κ C n ν) (hν : ν' ≤ ν) : IsSmallSet κ C n ν' :=
  fun x hx ↦ hν.trans (h x hx)

lemma isFiniteMeasure [IsFiniteKernel κ] (h : IsSmallSet κ C n ν) (hC : C.Nonempty) :
    IsFiniteMeasure ν :=
  isFiniteMeasure_of_le _ (h hC.some hC.some_mem)

/-- If `C` is `(n, ν)`-small, then a measure `μ` is sent by `κ ^ n` to a measure which is at
least `μ C • ν`. -/
lemma smul_le_comp (h : IsSmallSet κ C n ν) (μ : Measure α) : μ C • ν ≤ (κ ^ n) ∘ₘ μ := by
  refine Measure.le_iff.mpr fun s hs ↦ ?_
  rw [Measure.bind_apply hs (κ ^ n).aemeasurable, Measure.smul_apply, smul_eq_mul]
  calc μ C * ν s = ∫⁻ _ in C, ν s ∂μ := by rw [MeasureTheory.setLIntegral_const, mul_comm]
  _ ≤ ∫⁻ x in C, (κ ^ n) x s ∂μ :=
    setLIntegral_mono ((κ ^ n).measurable_coe hs) fun x hx ↦ h x hx s
  _ ≤ ∫⁻ x, (κ ^ n) x s ∂μ := setLIntegral_le_lintegral _ _

/-- If `C` is `(n, ν)`-small, then `(κ ^ (n + m)) x` is at least `(κ ^ m) x C • ν`. -/
lemma smul_le_pow_add_apply (h : IsSmallSet κ C n ν) (m : ℕ) (x : α) :
    (κ ^ m) x C • ν ≤ (κ ^ (n + m)) x := by
  rw [pow_add, comp_apply]
  exact h.smul_le_comp _

end IsSmallSet

/-- If `C` is `(k, ν)`-small, the point `y` reaches `C` with positive probability in `n` steps
and `C` is reached from `ν` with positive probability in `m` steps, then `y` reaches `C` with
positive probability in `m + k + n` steps. -/
lemma IsSmallSet.pow_apply_pos_of_pow_comp_apply_pos {C : Set α} {k m n : ℕ} {y : α}
    (h : IsSmallSet κ C k ν) (hy : 0 < (κ ^ n) y C) (hm : 0 < ((κ ^ m) ∘ₘ ν) C) :
    0 < (κ ^ (m + k + n)) y C := by
  have hle : (κ ^ n) y C • ((κ ^ m) ∘ₘ ν) ≤ (κ ^ (m + k + n)) y := by
    rw [add_assoc, pow_add, comp_apply, ← Measure.comp_smul]
    exact Measure.comp_le_comp_right (h.smul_le_pow_add_apply n y) _
  refine lt_of_lt_of_le ?_ (hle C)
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos hy.ne' hm.ne'

/-- If `C` is `(k, ν)`-small and is reached with positive probability from `μ` in `n` steps and
from `ν` in `m` steps, then it is reached with positive probability from `μ` in `m + k + n`
steps. -/
lemma IsSmallSet.pow_comp_apply_pos_of_pow_comp_apply_pos {C : Set α} {k m n : ℕ}
    {μ : Measure α} (h : IsSmallSet κ C k ν) (hC : MeasurableSet C)
    (hμ : 0 < ((κ ^ n) ∘ₘ μ) C) (hm : 0 < ((κ ^ m) ∘ₘ ν) C) :
    0 < ((κ ^ (m + k + n)) ∘ₘ μ) C := by
  rw [Measure.comp_apply_pos_iff hC] at hμ ⊢
  exact hμ.trans_le (measure_mono fun y hy ↦ h.pow_apply_pos_of_pow_comp_apply_pos hy hm)

end ProbabilityTheory.Kernel
