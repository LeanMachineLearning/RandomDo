module

public import RandomDo.MeasurableSpaceMonad.Instances.Id
public import RandomDo.NumLean.Distributions
public import RandomDo.Tactic.IsMarkov.Deriving
public import RandomDo.RDo.Loop
public import Mathlib.Probability.Distributions.Bernoulli

set_option linter.style.header false

/-!
# Shared scaffolding for the `rdo` test suite

The files in this library exercise the features of `rdo` that are currently implemented. They are
`module` files, like the library they test.

Where a program reduces, a test states the value it computes rather than only that it elaborates.
One family does not reduce here: a `for` loop over several collections streams the ones past
the first through `Std.Stream`, and for an `Array` or a `Vector` that goes through the
`Array → Subarray` conversion, which core marks `@[no_expose]`. Those are checked by elaborating.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

/-- The fair coin, as a probability measure on `Bool`. -/
noncomputable def fairCoin : Measure Bool := bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩

instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

end
