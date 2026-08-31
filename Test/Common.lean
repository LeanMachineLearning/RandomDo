module

public import RandomDo

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

universe u

/-- A deterministic `MeasurableSpaceMonad`. An `rdo` program written at `IdM` denotes a value, so
the tests can state what a program computes and not merely that it typechecks. -/
abbrev IdM := Monad.toMeasurableSpaceMonad Id

/-- Read the value out of a deterministic `rdo` program. `IdM α` is definitionally `α` but not
reducibly so, which is what otherwise stops numerals and `rfl` from seeing through it. -/
def IdM.run {α : Type u} [MeasurableSpace α] (x : IdM α) : α := x

/-- The fair coin, as a probability measure on `Bool`. -/
noncomputable def fairCoin : Measure Bool := bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩

instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

end
