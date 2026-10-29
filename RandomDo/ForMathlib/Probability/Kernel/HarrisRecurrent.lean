/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Irreducible
public import RandomDo.ForMathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Harris recurrent kernels

A Markov chain with transition kernel `κ : Kernel α α` is Harris recurrent with respect to a
measure `φ` if from every starting point, it reaches every set of positive `φ`-measure almost
surely.

We state this property without reference to the law of the trajectories of the chain. For a
measurable set `A`, the kernel `κ.restrict hA.compl` describes one step of the chain killed when
it enters `A`. Hence `((κ.restrict hA.compl) ^ n) x Set.univ` is the probability that the chain
started at `x` does not visit `A` during its first `n` steps, and the chain reaches `A` almost
surely if and only if that quantity tends to zero as `n` tends to infinity.

## Main definitions

* `ProbabilityTheory.Kernel.IsHarrisRecurrent κ φ`: from every point, the chain with kernel `κ`
  reaches every set of positive `φ`-measure almost surely.

## Main statements

* `ProbabilityTheory.Kernel.IsHarrisRecurrent.isIrreducible`: a Markov kernel which is Harris
  recurrent with respect to `φ` is `φ`-irreducible.

## References

* [Meyn, S.P. and Tweedie, R.L., *Markov Chains and Stochastic Stability*][meyntweedie1993]
-/

@[expose] public section

open MeasureTheory Filter Topology

open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {φ : Measure α}

/-- A kernel `κ : Kernel α α` is Harris recurrent with respect to a measure `φ` if for every
measurable set `A` with `φ A > 0` and every `x`, the probability
`((κ.restrict hA.compl) ^ n) x Set.univ` that the Markov chain with kernel `κ` started at `x`
does not visit `A` during its first `n` steps tends to zero as `n` tends to infinity. In other
words, every set of positive `φ`-measure is reached almost surely from every point.
Ref. *Meyn-Tweedie*, Section 9.1. -/
def IsHarrisRecurrent (κ : Kernel α α) (φ : Measure α) : Prop :=
  ∀ ⦃A : Set α⦄ (hA : MeasurableSet A), 0 < φ A → ∀ x,
    Tendsto (fun n : ℕ ↦ ((κ.restrict hA.compl) ^ n) x Set.univ) atTop (𝓝 0)

/-- If a kernel is Harris recurrent with respect to a measure `φ₂`, then it is Harris recurrent
with respect to every measure `φ₁ ≪ φ₂`. -/
lemma IsHarrisRecurrent.mono_ac {φ₁ φ₂ : Measure α} (h : κ.IsHarrisRecurrent φ₂)
    (hφ : φ₁ ≪ φ₂) :
    κ.IsHarrisRecurrent φ₁ :=
  fun _ hA hφA x ↦ h hA (pos_iff_ne_zero.mpr fun h0 ↦ hφA.ne' (hφ h0)) x

/-- A Markov kernel which is Harris recurrent with respect to a measure `φ` is `φ`-irreducible:
if a point never reaches a set, then the chain killed when it enters that set is never killed. -/
lemma IsHarrisRecurrent.isIrreducible [IsMarkovKernel κ] (h : κ.IsHarrisRecurrent φ) :
    IsIrreducible φ κ := by
  refine ⟨fun A hA hφA a ↦ ?_⟩
  by_contra! hcon
  -- if `a` never reaches `A`, then the powers of `κ` and of its restriction to `Aᶜ` agree at `a`
  have h_eq : ∀ n : ℕ, ((κ.restrict hA.compl) ^ n) a = (κ ^ n) a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h0 : (κ ∘ₘ (κ ^ n) a) A = 0 := by
        rw [← comp_apply, ← pow_add_one']
        exact nonpos_iff_eq_zero.mp (hcon (n + 1))
      rw [pow_add_one', comp_apply, ih, pow_add_one', comp_apply, Measure.restrict_comp]
      exact Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.mp h0)
  have h_tendsto := h hA hφA a
  simp_rw [h_eq, measure_univ] at h_tendsto
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h_tendsto)

end ProbabilityTheory.Kernel
