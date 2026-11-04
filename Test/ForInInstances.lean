/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.MeasurableSpaceMonad.ForInInstances.Basic
import RandomDo.Monad.Instances
import RandomDo.Monad.Notation
import Std.Data.Iterators
import all Init.Data.Range.Polymorphic.RangeIterator
import all Std.Data.Iterators.Producers.Range
meta import RandomDo.MeasurableSpaceMonad.ForInInstances.Basic
meta import RandomDo.Monad.Instances
meta import RandomDo.Monad.Notation
meta import Std.Data.Iterators

/-!
# Collection and iterator loops in the supported measurable space monads

The abstract checks keep the element and state universes independent and require no measurable
space on the elements. Executable checks use an adapted state monad to observe iteration order
and early termination, including the array's compiler implementation. A kernel check covers its
reference implementation, and measure programs check that loop-body effects are retained. Iterator
checks cover lazy pipelines, producer effects, membership proofs, and termination wrappers. Direct
range checks cover endpoint conventions, bounded-type exhaustion, and inference from typed binders.
-/

-- This module contains private fixtures and executable regression checks.
set_option linter.privateModule false
set_option linter.hashCommand false

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

universe uα u v

section Inference

variable {α : Type uα} {m : (α : Type u) → [MeasurableSpace α] → Type v}
  [MeasurableSpaceMonad m]

example : MeasurableSpaceForIn' m (List α) α inferInstance := inferInstance
example : MeasurableSpaceForIn' m (Array α) α inferInstance := inferInstance
example {n : Nat} : MeasurableSpaceForIn' m (Vector α n) α inferInstance := inferInstance

end Inference

namespace Test.ForInInstances

-- These fixtures use main's ordinary-monad adapter; no sampler refactor is required.
private abbrev TraceT (m : Type → Type) := Monad.toMeasurableSpaceMonad (RandGT Nat m)

private abbrev Trace := TraceT Id

-- Record visited elements as decimal digits in the sampler state. This makes both their order
-- and any actions performed after the requested stop observable.
private def record (n : Nat) : Trace Unit := fun s => ((), ⟨10 * s.down + n⟩)

private def visit {ρ : Type} [MeasurableSpaceForIn (Trace) ρ Nat]
    (xs : ρ) : Trace Nat := rdo
  let mut total := 0
  for n in xs rdo
    record n
    total := total + n
    if n = 3 then break
  return total

private def run (action : Trace Nat) (s : Nat := 0) : Nat × Nat :=
  let (a, s') := action ⟨s⟩
  (a, s'.down)

-- Kernel reduction checks the safe array reference implementation.
example : run (visit #[1, 3, 7]) = (4, 13) := rfl

-- Executable checks use the array implementation selected by `implemented_by`.
#guard run (visit [1, 3, 7]) == (4, 13)
#guard run (visit #[1, 3, 7]) == (4, 13)
#guard run (visit (#[1, 3, 7].toVector)) == (4, 13)
#guard run (visit (#[] : Array Nat)) 42 == (0, 42)
#guard run (visit #[1, 2]) == (3, 12)
#guard run (visit [1, 2]) == (3, 12)

-- A zero-measure action inside a nonempty loop must annihilate the result measure.
example :
    (rdo
      let mut total := 0
      for n in [1, 2] rdo
        let a ← (0 : Measure Nat)
        total := total + n + a
      return total : Measure Nat) = 0 := by
  simp [MeasureTheory.forIn, MeasureTheory.forIn',
    MeasureTheory.List.measurableSpaceForIn', MeasureTheory.List.measurableSpaceForIn'.loop,
    mPure, mBind]

-- Pipelines must stay lazy: filtering skips elements, take stops the producer, and break can
-- terminate an unbounded iterator. The sampler state records precisely the visited elements.
#guard run (visit ([0, 1, 2, 3, 4, 5].iter.map (· + 1) |>.filter (· % 2 == 0) |>.take 2)) ==
  (6, 24)
#guard run (visit (([1, 2, 9].iter.zip #[0, 0].iter).map fun p => p.1 + p.2)) == (3, 12)
#guard run (visit ((0...* : Std.Rci Nat).iter)) == (6, 123)
#guard run (visit [1, 3, 7].iter.ensureTermination) == (4, 13)

-- Iterator internals and elements need no measurable-space instance. In particular, the
-- elements can inhabit a larger universe than the sampler's return values.
example {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m]
    (xs : List (Type)) : m Nat := rdo
  let mut count := 0
  for _ in xs.iter rdo
    count := count + 1
  return count

-- Producer effects and body effects must interleave. Breaking at 3 must prevent the producer
-- from processing 7. The expected log is producer(1), body(1), producer(3), body(3).
private def produce (n : Nat) : RandGT Nat Id Nat := do
  record (2 * n)
  return n

#guard run (visit ([1, 3, 7].iter.mapM produce)) == (4, 2163)
#guard run (visit ([1, 3, 7].iter.mapM produce).ensureTermination) == (4, 2163)

-- Producer effects can also lift from the base monad of a transformer. An absent producer
-- value aborts the computation, even though the loop body itself never fails.
private def fromBase (xs : List (Option Nat)) : TraceT Option Nat := rdo
  let mut total := 0
  for n in xs.iter.mapM id rdo
    total := total + n
  return total

#guard (fromBase [some 1, some 2]).run ⟨42⟩ == some (3, ⟨42⟩)
#guard (fromBase [some 1, none, some 2]).run ⟨42⟩ == none

-- Check the compatibility wrappers without using the deprecated allowNontermination function.
#guard run (visit (Std.Iter.Partial.mk [1, 3, 7].iter)) == (4, 13)
#guard run (visit (Std.IterM.Partial.mk ([1, 3, 7].iter.mapM produce))) == (4, 2163)

-- As in core, membership-aware iterator loops are enabled explicitly.
private def withIteratorProof : Trace Nat :=
  let it := [1, 2].iter
  letI := MeasureTheory.Iter.instMeasurableSpaceForIn' (m := Trace)
    (ι := Std.Iterators.Types.ListIterator Nat)
  rdo
    let mut total := 0
    for h : n in it rdo
      have : it.IsPlausibleIndirectOutput n := h
      record n
      total := total + n
    return total

#guard run withIteratorProof == (3, 12)

-- The unfolding theorem supports kernel proofs about Measure, not just executable samplers.
example : MeasureTheory.forIn ([] : List Nat).iter 17
    (fun _ _ => (0 : Measure (ForInStep Nat))) = Measure.dirac 17 := by
  rw [MeasureTheory.Iter.forIn_eq_match_step]
  simp [mPure]

-- One polymorphic program must support both the executable and measure interpretations.
-- The sampler argument affects the sum, and breaking must prevent subsequent sampling.
private def sampledSum {m : (α : Type) → [MeasurableSpace α] → Type}
    [MeasurableSpaceMonad m] (sample : Nat → m Nat) (xs : List Nat) : m Nat := rdo
  let mut total := 0
  for n in xs.iter rdo
    let a ← sample n
    total := total + a
    if n = 3 then break
  return total

private def sample (n : Nat) : Trace Nat := rdo
  record n
  return n

#guard run (sampledSum sample [1, 3, 7]) == (4, 13)
#guard run (sampledSum sample []) 42 == (0, 42)

example : sampledSum (m := Measure) (fun _ => 0) [1, 3, 7] = 0 := by
  unfold sampledSum
  dsimp only
  rw [MeasureTheory.Iter.forIn_eq_match_step]
  simp [mBind, mPure]

-- The closed-range specialization must exhaust a bounded type without wrapping around.
private def boundaryRange {m : (α : Type) → [MeasurableSpace α] → Type}
    [MeasurableSpaceMonad m] (sample : UInt8 → m Nat) : m Nat := rdo
  let mut total := 0
  for n in (253 : UInt8)...=255 rdo
    let a ← sample n
    total := total + a
  return total

#guard run (boundaryRange (fun n => rdo record 1; return n.toNat)) == (762, 111)

-- This proof uses the specialized range's lawfulness instance, not just the default consumer.
example : boundaryRange (m := Measure) (fun _ => 0) = 0 := by
  unfold boundaryRange
  dsimp only
  rw [Rcc.forIn_eq_forIn_iter, MeasureTheory.Iter.forIn_eq_match_step]
  simp [Std.Rxc.Iterator.step_eq_step, Std.Rxc.Iterator.step, Std.Rcc.Internal.iter, mBind, mPure]

-- Each direct range form must preserve its endpoint convention and stop at type exhaustion.
private def rangeElements {ρ : Type} [MeasurableSpaceForIn (Trace) ρ UInt8]
    (r : ρ) : Array Nat :=
  ((rdo
    let mut elements := #[]
    for n in r rdo
      elements := elements.push n.toNat
    return elements : Trace (Array Nat)) ⟨0⟩).1

#guard rangeElements ((2 : UInt8)...=4) == #[2, 3, 4]
#guard rangeElements ((2 : UInt8)...4) == #[2, 3]
#guard rangeElements ((253 : UInt8)...*) == #[253, 254, 255]
#guard rangeElements ((2 : UInt8)<...=4) == #[3, 4]
#guard rangeElements ((2 : UInt8)<...4) == #[3]
#guard rangeElements ((253 : UInt8)<...*) == #[254, 255]
#guard rangeElements (*...=(2 : UInt8)) == #[0, 1, 2]
#guard rangeElements (*...(2 : UInt8)) == #[0, 1]
#guard rangeElements (*...* : Std.Rii UInt8) == Array.ofFn (fun i : Fin 256 => i.val)
#guard rangeElements ((255 : UInt8)<...*) == #[]
#guard rangeElements ((4 : UInt8)...2) == #[]

-- The element type inferred from the body must determine a range with literal or absent bounds.
-- Known notation limitation: `for (i : Int) in 1...3 rdo ...` still defaults the bounds to
-- Nat during pattern expansion, unlike core. Annotating a bound or using the body as below works.
-- Keep that elaborator issue separate from the range instances.
#guard run (rdo
    let mut total := 0
    for i in 1...3 rdo
      total := total + (i : Int).toNat
    for i in *...* rdo
      total := total + (i : Fin 3).val
    return total) == (6, 0)

-- Range membership must supply a usable bounds proof, so indexing needs no run-time check.
private def indexedSum {m : (α : Type) → [MeasurableSpace α] → Type}
    [MeasurableSpaceMonad m] (xs : Array Nat) : m Nat := rdo
  let mut total := 0
  for h : i in 0...xs.size rdo
    total := total + xs[i]'h.2
  return total

#guard run (indexedSum #[2, 4, 8]) == (14, 0)

-- Direct ranges also preserve early exit and skip effects after continue or return.
#guard run (visit (1...8 : Std.Rco Nat)) == (6, 123)
#guard run (rdo
    let mut total := 0
    for i in 0...5 rdo
      if i = 0 then continue
      record i
      if i = 2 then return total
      total := total + i
    return total) == (1, 12)

-- As in core, a potentially infinite Nat range needs explicit iterator syntax instead.
example : True := by
  fail_if_success
    have : MeasurableSpaceForIn (Trace) (Std.Rci Nat) Nat := inferInstance
  trivial

end Test.ForInInstances
