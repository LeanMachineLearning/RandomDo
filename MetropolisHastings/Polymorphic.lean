/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MetropolisHastings.Theory

/-!
# Random-walk Metropolis–Hastings, polymorphic in the monad

The algorithm of `MetropolisHastings.Defs`, written once over an arbitrary `MeasurableSpaceMonad`
`m` and scalar type `R`. It draws through `HasGaussian` and `HasBernoulli`, and computes with the
operations of `R`. Read at `m := Measure` and `R := ℝ`, it is the program of
`MetropolisHastings.Defs` (`mhStepPoly_measure`, `mhChainPoly_measure`), so it inherits all of
`MetropolisHastings.Theory`. Run at `m := RandM` and `R := Float`, it samples.

Unlike the `@[computable]` route of `MetropolisHastings.Computable`, no program is written for us
here: the definition that runs is the one the theorems are about, and the only thing to trust is
that the instances at `RandM` sample from the distributions of the instances at `Measure`.

## Main definitions

* `mhStepPoly logπ s x`: one step of the chain from `x`.
* `mhChainPoly logπ s n x₀`: `n` steps of the chain from `x₀`.

## Main results

* `mhStepPoly_measure`, `mhChainPoly_measure`: at `Measure`, they are `mhStep` and `mhChain`.
* `isReversible_mhStepPoly`, `invariant_mhChainPoly`: detailed balance and stationarity, for the
  polymorphic programs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MetropolisHastings

universe v

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {R V : Type} [MeasurableSpace R] [Sub R] [Min R] [One R] [HasExp R]

/-- One step of random-walk Metropolis–Hastings from `x`, with proposal variance `s`, in any monad
that can draw from a Gaussian and a Bernoulli distribution. -/
def mhStepPoly [HasGaussian m R V R] [HasBernoulli m R] (logπ : R → R) (s : V) (x : R) : m R := rdo
  let y ← HasGaussian.gaussian (m := m) x s
  let accept ← HasBernoulli.bernoulli (m := m) (min 1 (HasExp.exp (logπ y - logπ x)))
  return if accept then y else x

/-- `n` steps of random-walk Metropolis–Hastings from `x₀`, with proposal variance `s`, in any
monad that can draw from a Gaussian and a Bernoulli distribution. -/
def mhChainPoly [HasGaussian m R V R] [HasBernoulli m R] (logπ : R → R) (s : V) (n : ℕ)
    (x₀ : R) : m R := rdo
  let mut x := x₀
  for _ in List.range n rdo
    let y ← mhStepPoly (m := m) logπ s x
    x := y
  return x

section Measure

variable (logπ : ℝ → ℝ) (s : ℝ≥0)

/-- At `Measure`, the polymorphic step is `mhStep`. -/
theorem mhStepPoly_measure : mhStepPoly (m := Measure) logπ s = mhStep logπ s := by
  ext1 x
  change (gaussianReal x s).bind (fun y ↦ (Ber(true, false,
      Set.projIcc 0 1 zero_le_one (min 1 (Real.exp (logπ y - logπ x))))).bind
    fun b ↦ Measure.dirac (if b = true then y else x)) = _
  congr with y : 1
  have h : Set.projIcc (0 : ℝ) 1 zero_le_one (min 1 (Real.exp (logπ y - logπ x)))
      = acceptProb logπ x y :=
    Set.projIcc_of_mem _ (acceptProb logπ x y).2
  rw [h]
  rfl

/-- At `Measure`, the polymorphic chain is `mhChain`. -/
theorem mhChainPoly_measure : mhChainPoly (m := Measure) logπ s = mhChain logπ s := by
  ext1 n
  unfold mhChainPoly mhChain
  rw [mhStepPoly_measure]

variable [hπ : Fact (Measurable logπ)]

/- `is_markov` reads the polymorphic programs directly, through the instances at `Measure`. -/

instance : IsMarkov (mhStepPoly (m := Measure) logπ s) := by
  have := hπ.out
  is_markov

instance (n : ℕ) : IsMarkov (mhChainPoly (m := Measure) logπ s n) := by
  have := hπ.out
  is_markov

/-- **Detailed balance** of the polymorphic step, read at `Measure`. -/
theorem isReversible_mhStepPoly :
    (IsMarkov.toKernel (mhStepPoly (m := Measure) logπ s)).IsReversible (target logπ) := by
  convert isReversible_mhStep logπ s using 2
  exact mhStepPoly_measure logπ s

/-- **Stationarity** of the polymorphic chain, read at `Measure`. -/
theorem invariant_mhChainPoly (n : ℕ) :
    (target logπ).bind (mhChainPoly (m := Measure) logπ s n) = target logπ := by
  rw [mhChainPoly_measure, invariant_mhChain]

end Measure

end MetropolisHastings
