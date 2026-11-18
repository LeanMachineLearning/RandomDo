/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Sampling.Measure
public import RandomDo.Sampling.PCG64
public import RandomDo.Sampling.StdGen
public import RandomDo.RDo
import all Init.Data.Range.Polymorphic.RangeIterator
meta import RandomDo.Sampling.PCG64
meta import RandomDo.Sampling.StdGen
meta import RandomDo.RDo

/-!
# Worked examples for the RandomDo refactor

This file collects illustrative programs to edit, run, and discuss as the refactor develops.
Use these examples to assess notation, API design, readability, and the experience of interpreting
one program as both a measure and an executable sampler. The file is built with `TestNext`.

The programs request sampling primitives through `HasBernoulli` and `HasUniform`. All three
interpretations are imported together: changing `m` selects the interpretation, and the runners
select the initial state. `Measure` uses real probabilities; `PCG64M` and `StdGenM` use `Float`.
-/

-- Evaluations are part of these worked examples.
set_option linter.hashCommand false

@[expose] public section

open MeasureTheory HasBernoulli HasUniform

namespace TestNext.Examples

/-! ## Binomial distribution -/

/-- Count successes in `n` Bernoulli trials with probability `p`.

The same definition denotes a binomial distribution under `Measure` and executes using the
selected generator under `PCG64M` or `StdGenM`. Each iteration performs another draw and threads
the generator state through the program.
-/
def binomial {m : (α : Type) → [MeasurableSpace α] → Type*} [MeasurableSpaceMonad m]
    {P : Type} [HasBernoulli m P] (n : Nat) (p : P) : m Nat := rdo
  let mut successes := 0
  for _ in 0...n rdo
    let success ← bernoulli p
    if success then
      successes := successes + 1
  return successes

-- The same program and probability, with different generators. Change the seed and reevaluate.
#eval PCG64M.runWithSeed 42 (binomial 10 0.25)
#eval StdGenM.runWithSeed 42 (binomial 10 0.25)

-- With no trials, the result is concentrated at zero, whatever the success probability.
example (p : unitInterval) : binomial 0 p = Measure.dirac 0 := by
  unfold binomial
  dsimp only
  rw [Rco.mForIn_eq_mForIn_iter, Iter.mForIn_eq_match_step (fun _ => measurable_from_nat)]
  simp [Std.Rxo.Iterator.step_eq_step, Std.Rxo.Iterator.step, Std.Rco.Internal.iter, mPure, mBind]

/-! ## Drawing a probability before the trials -/

/-- Draw a unit-interval probability, then return it together with a binomial sample.

This uses both primitives without fixing a scalar type or depending on generator operations.
The measure interpretation describes the ideal continuous mixture; the executable interpretations
use their finite floating-point grids.
-/
def randomBinomial {m : (α : Type) → [MeasurableSpace α] → Type*} [MeasurableSpaceMonad m]
    {R : Type} [MeasurableSpace R] [HasUniform m R] [HasBernoulli m R]
    (n : Nat) : m (R × Nat) := rdo
  let p ← uniform
  let successes ← binomial n p
  return (p, successes)

-- Here the interpretation determines the scalar type: Float for both executable samplers.
#eval PCG64M.runWithSeed 42 (randomBinomial 10)
#eval StdGenM.runWithSeed 42 (randomBinomial 10)

/-- The identical two-primitive program interpreted as a measure, using real probabilities. -/
noncomputable def randomBinomialMeasure (n : Nat) : Measure (ℝ × Nat) :=
  randomBinomial n

-- Keep the final state to resume sampling, rather than restarting from the seed.
#eval Id.run do
  let (first, state) := PCG64M.run (randomBinomial 10) (NumLean.mkPCG64 42)
  let (second, _) := PCG64M.run (randomBinomial 10) state
  return (first, second)

end TestNext.Examples
