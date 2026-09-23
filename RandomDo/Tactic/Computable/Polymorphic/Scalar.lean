/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

@[expose] public section

/-- `Scalar R` bundles a measurable space structure on `R` with the operations and numerals of a
field, but none of its axioms, so that it applies to both `ℝ` and `Float`. -/
class abbrev Scalar (R : Type*) :=
  MeasurableSpace R, Add R, Mul R, Div R, Sub R, Zero R, One R, NatCast R, OfScientific R
