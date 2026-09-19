/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo

/-!
# The random-walk Metropolis–Hastings algorithm, as an `rdo` program

The target is the measure `π(dx) = exp (logπ x) dx` on `ℝ`, given through its log-density, which
need not be normalised. From the current state `x`, one step of the algorithm proposes
`y ∼ 𝒩(x, s)` and accepts it with probability `min 1 (exp (logπ y - logπ x))`; on rejection the
chain stays at `x`. The chain runs `n` such steps from `x₀`.

Both programs denote Markov kernels, written over the Giry monad. `MetropolisHastings.Theory`
proves what they satisfy, `MetropolisHastings.Computable` and `MetropolisHastings.Polymorphic` turn
them into programs that run, and `MetropolisHastings.Targets` gives two targets to run them on.
To run them and draw the plots, from the root of the repository:

```
lake exe mh                     # runs both samplers, checks they agree, writes mh_output/
python3 scripts/mh_plot.py      # checks them against numpy, draws mh_output/*.png
```

## Main definitions

* `MetropolisHastings.target logπ`: the measure with density `exp ∘ logπ` against Lebesgue.
* `MetropolisHastings.acceptProb logπ x y`: the probability of accepting a move from `x` to `y`.
* `MetropolisHastings.mhStep logπ s x`: the law of one step of the chain started at `x`.
* `MetropolisHastings.mhChain logπ s n x₀`: the law of the state after `n` steps from `x₀`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MetropolisHastings

variable (logπ : ℝ → ℝ) (s : ℝ≥0)

/-- The target measure, with density `exp ∘ logπ` against the Lebesgue measure. -/
noncomputable def target : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal (Real.exp (logπ x))

/-- The probability of accepting a move from `x` to `y`: the ratio of the target densities, capped
at one. -/
noncomputable def acceptProb (x y : ℝ) : unitInterval :=
  ⟨min 1 (Real.exp (logπ y - logπ x)),
    le_min zero_le_one (Real.exp_nonneg _), min_le_left _ _⟩

@[fun_prop]
lemma measurable_acceptProb {γ : Type*} [MeasurableSpace γ] {logπ : ℝ → ℝ} {f g : γ → ℝ}
    (hπ : Measurable logπ) (hf : Measurable f) (hg : Measurable g) :
    Measurable fun c ↦ acceptProb logπ (f c) (g c) :=
  Measurable.subtype_mk (by fun_prop)

/-- One step of random-walk Metropolis–Hastings from `x`, with proposal variance `s`. -/
noncomputable def mhStep (x : ℝ) : Measure ℝ := rdo
  let y ← gaussianReal x s
  let accept ← bernoulliMeasure true false (acceptProb logπ x y)
  return if accept then y else x

/-- `n` steps of random-walk Metropolis–Hastings from `x₀`, with proposal variance `s`. -/
noncomputable def mhChain (n : ℕ) (x₀ : ℝ) : Measure ℝ := rdo
  let mut x := x₀
  for _ in List.range n rdo
    let y ← mhStep logπ s x
    x := y
  return x

end MetropolisHastings
