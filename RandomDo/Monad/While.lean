/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Monad.Instances
import RandomDo.Monad.Notation
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# `while` loops

`while c rdo body` is a loop over `Lean.Loop`, which runs `body` for as long as `c` holds. Each step
of the loop returns a `ForInStep`: `yield b` to carry on from the state `b`, `done b` to stop there.
Such a loop need not terminate, so its meaning depends on the monad, which provides it through the
class `MeasurableSpaceMonadWhile`.

## Main definitions

* `MeasurableSpaceMonadWhile`: a measurable space monad with an unbounded loop. Its instances:
  - at a core monad, core's loop over `Lean.Loop`;
  - at `Measure`, the least fixed point of "one step, then stop or run the loop again": the sum
    over `n` of the runs that stop at the `n + 1`-th step. The runs that never stop carry no mass.
* `MeasurableSpaceMonad.loopExit f n b`: the runs of the loop whose step is `f` that, from `b`, stop
  at the `n + 1`-th step, in any measurable space monad with a zero.
* The instance of `MeasurableSpaceForIn m Lean.Loop Unit`, for any `MeasurableSpaceMonadWhile m`:
  `while … rdo` runs the loop of the monad.

## Implementation notes

The while loop could instead be a field of `MeasurableSpaceMonad` itself. Every program over an
arbitrary measurable space monad could then use `while` with no further hypothesis, as it uses
`for`, at the price of asking every measurable space monad for its own implementation of the loop.

## References

* Dexter Kozen, *Semantics of probabilistic programs*, 1981.
-/

@[expose] public section

universe u v

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

/-- A measurable space monad with an unbounded loop, the one behind `while … rdo`. -/
class MeasurableSpaceMonadWhile (m : (α : Type u) → [MeasurableSpace α] → Type v) where
  /-- Run the step `f` from `b`, then from each state it carries on with, until it stops. -/
  loop {β : Type u} [MeasurableSpace β] (f : β → m (ForInStep β)) (b : β) : m β

/-- At a core monad, the loop is core's loop over `Lean.Loop`. -/
instance {m : Type u → Type v} [Monad m] :
    MeasurableSpaceMonadWhile (Monad.toMeasurableSpaceMonad m) where
  loop f b := ForIn.forIn (m := m) Lean.Loop.mk b fun _ ↦ f

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {β : Type u} [MeasurableSpace β] [Zero (m β)]

/-- The runs of the loop whose step is `f` that, from `b`, stop at the `n + 1`-th step. A run that
does not stop there contributes `0`. -/
def MeasurableSpaceMonad.loopExit (f : β → m (ForInStep β)) : ℕ → β → m β
  -- One step from `b`: keep the runs that stop there, drop the ones that carry on.
  | 0, b => f b >>=ₘ fun s ↦ ForInStep.casesOn (motive := fun _ ↦ m β) s mPure fun _ ↦ 0
  -- One step from `b`: drop the runs that stop there, keep those that stop `n + 1` steps later.
  | n + 1, b => f b >>=ₘ fun s ↦
      ForInStep.casesOn (motive := fun _ ↦ m β) s (fun _ ↦ 0) (loopExit f n)

/-- At `Measure`, the loop is the least fixed point of "one step, then stop or run the loop again":
the sum over `n` of the runs that stop at the `n + 1`-th step. -/
noncomputable instance : MeasurableSpaceMonadWhile Measure where
  loop f b := Measure.sum fun n ↦ MeasurableSpaceMonad.loopExit f n b

/-- The unbounded loop behind `while … rdo` is the loop of the monad. -/
instance [MeasurableSpaceMonadWhile m] : MeasurableSpaceForIn m Lean.Loop Unit where
  forIn _ b f := MeasurableSpaceMonadWhile.loop (f ()) b
