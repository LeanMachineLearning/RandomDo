/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MetropolisHastings.Computable
public import MetropolisHastings.Polymorphic
public meta import MetropolisHastings.Computable

/-!
# Two targets to run the chain on

Each target is written twice, once for each route from the theory to a sampler: on `ℝ`, where
`@[computable]` translates it into a function on `Float`, and polymorphically in the scalars, to be
read at `ℝ` for the theorems and at `Float` for running. The two agree at `ℝ` by definition.

* `stdNormal`: the standard Gaussian, `logπ x = -x² / 2`.
* `bimodal`: the mixture `0.3 𝒩(-3, 1) + 0.7 𝒩(3, 1)`, up to normalisation. Its modes are far
  apart, so how well the chain moves between them depends on the proposal variance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MetropolisHastings

/-! ## On `ℝ`, translated by `@[computable]` -/

/-- The log-density of the standard Gaussian, up to an additive constant. -/
@[computable]
noncomputable def stdNormal (x : ℝ) : ℝ := -(x * x) / 2

/-- The log-density of the mixture `0.3 𝒩(-3, 1) + 0.7 𝒩(3, 1)`, up to an additive constant. -/
@[computable]
noncomputable def bimodal (x : ℝ) : ℝ :=
  Real.log (0.3 * Real.exp (-((x + 3) * (x + 3)) / 2) + 0.7 * Real.exp (-((x - 3) * (x - 3)) / 2))

instance : Fact (Measurable stdNormal) := ⟨by unfold stdNormal; fun_prop⟩

instance : Fact (Measurable bimodal) := ⟨by unfold bimodal; fun_prop⟩

/-! ## Polymorphic in the scalars -/

section Polymorphic

variable {R : Type} [Add R] [Sub R] [Mul R] [Div R] [Neg R] [OfNat R 2] [OfNat R 3]
  [OfScientific R] [HasExp R] [HasLog R]

/-- `stdNormal`, polymorphic in the scalars. -/
def stdNormalPoly (x : R) : R := -(x * x) / 2

/-- `bimodal`, polymorphic in the scalars. -/
def bimodalPoly (x : R) : R :=
  HasLog.log (0.3 * HasExp.exp (-((x + 3) * (x + 3)) / 2)
    + 0.7 * HasExp.exp (-((x - 3) * (x - 3)) / 2))

theorem stdNormalPoly_real : stdNormalPoly (R := ℝ) = stdNormal := rfl

theorem bimodalPoly_real : bimodalPoly (R := ℝ) = bimodal := rfl

end Polymorphic

/-! ## What the theory says about the chains we run -/

/-- Started from the bimodal target, the chain run on it has that target as its law after any
number of steps, whatever the proposal variance. -/
example (s : ℝ≥0) (n : ℕ) : (target bimodal).bind (mhChain bimodal s n) = target bimodal :=
  invariant_mhChain bimodal s n

/-- The same, for the polymorphic chain run on the polymorphic target. -/
example (s : ℝ≥0) (n : ℕ) :
    (target bimodal).bind (mhChainPoly (m := Measure) bimodalPoly s n) = target bimodal := by
  rw [bimodalPoly_real]
  exact invariant_mhChainPoly bimodal s n

end MetropolisHastings
