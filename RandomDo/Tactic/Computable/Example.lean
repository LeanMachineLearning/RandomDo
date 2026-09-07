module
/- /-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Monad.Instances
public import RandomDo.Monad.Notation
public import RandomDo.NumLean.Distributions
public import RandomDo.Tactic.Computable.Deriving
public import Mathlib
meta import RandomDo.NumLean.Distributions
meta import Batteries.Data.Float.Basic

/-!
# `@[computable]` on an `rdo` program

`test` denotes a distribution: a Gaussian draw, shifted by one. The attribute reads it and writes
the program that samples from it, drawing from `NumLean.normal` instead and shifting the draw the
same way.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory NumLean

/-- Test -/
@[computable]
noncomputable def test (m : ℝ) : Measure ℝ := rdo
  let x ← gaussianReal m 1
  return x + 1

/- And it runs: seeded alike, it draws what numpy 2.3.4 draws from `default_rng(42).normal() + 1`,
down to the last bit. -/
run_cmd do IO.runRandPCG do
  let x ← (IO.runRandPCG <| test_computable 10 : IO Float)
  Lean.logInfo m!"`test_computable` drew {x.toStringFull}"
 -/
