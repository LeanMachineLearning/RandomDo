/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.MeasurableSpaceMonad.ForInInstances.Array.Basic
import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.Instances
import RandomDo.MeasurableSpaceMonad.ForInInstances.List
import RandomDo.MeasurableSpaceMonad.ForInInstances.Ranges
import RandomDo.MeasurableSpaceMonad.Instances.Measure
import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom
import RandomDo.RDo.Loop
import Std.Data.Iterators
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import all Init.Data.Iterators.Basic
import all Init.Data.Range.Polymorphic.RangeIterator
import all Std.Data.Iterators.Producers.Range
meta import RandomDo.MeasurableSpaceMonad.ForInInstances.Array.Basic
meta import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.Instances
meta import RandomDo.MeasurableSpaceMonad.ForInInstances.List
meta import RandomDo.MeasurableSpaceMonad.ForInInstances.Ranges
meta import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom
meta import RandomDo.RDo.Loop
meta import Std.Data.Iterators

/-!
# Collection and iterator loops in the supported measurable space monads

The abstract collection checks keep the element and state universes independent and require no
measurable space on the elements. Executable checks use `PseudoRand` to observe iteration order
and early termination, including the array's compiler implementation. A kernel check covers its
reference implementation, and measure programs check that loop-body effects are retained.
Iterator checks cover lazy pipelines, producer effects, membership proofs, and termination
wrappers. Direct range checks cover endpoint conventions, bounded-type exhaustion, and inference
from typed binders.
-/

-- This module contains private fixtures and executable regression checks.
set_option linter.privateModule false
set_option linter.hashCommand false

open MeasureTheory MeasureTheory.Internal

universe uα u v

section Inference

variable {α : Type uα} {m : (α : Type u) → [MeasurableSpace α] → Type v}
  [MeasurableSpaceMonad m]

example : MeasurableSpaceForIn' m (List α) α inferInstance := inferInstance
example : MeasurableSpaceForIn' m (Array α) α inferInstance := inferInstance
example {n : Nat} : MeasurableSpaceForIn' m (Vector α n) α inferInstance := inferInstance

end Inference

namespace TestNext.MeasurableSpaceMonad.ForInInstances

-- Record visited elements as decimal digits in the sampler state. This makes both their order
-- and any actions performed after the requested stop observable.
private def record (n : Nat) : PseudoRand Nat Unit := fun s => ((), ⟨10 * s.down + n⟩)

private def visit {ρ : Type} [MeasurableSpaceForIn (PseudoRand Nat) ρ Nat]
    (xs : ρ) : PseudoRand Nat Nat := rdo
  let mut total := 0
  for n in xs rdo
    record n
    total := total + n
    if n = 3 then break
  return total

private def run (action : PseudoRand Nat Nat) (s : Nat := 0) : Nat × Nat :=
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
  simp [mForIn, mForIn',
    List.mForIn', List.mForIn'.loop,
    mPure, mBind]

-- Pipelines must stay lazy: filtering skips elements, take stops the producer, and break can
-- terminate an unbounded iterator. The sampler state records precisely the visited elements.
#guard run (visit ([0, 1, 2, 3, 4, 5].iter.map (· + 1) |>.filter (· % 2 == 0) |>.take 2)) ==
  (6, 24)
#guard run (visit (([1, 2, 9].iter.zip #[0, 0].iter).map fun p => p.1 + p.2)) == (3, 12)
#guard run (visit ((0...* : Std.Rci Nat).iter)) == (6, 123)
#guard run (visit [1, 3, 7].iter.ensureTermination) == (4, 13)

-- Supplied element spaces induce the iterator state space. The element universe remains
-- independent of the sampler's return universe, even for pure iteration.
example {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m]
    [MeasurableSpace (Type)] (xs : List (Type)) : m Nat := rdo
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

-- Structural spaces must compose through effectful combinators. Dropping 1 still runs its
-- producer effect, taking 1 visits only 3, and the next producer effect must not run.
#guard run (visit ([1, 3, 7].iter.mapM produce |>.drop 1 |>.take 1)) == (3, 263)

-- Producer effects can also lift from the base monad of a transformer. An absent producer
-- value aborts the computation, even though the loop body itself never fails.
private def fromBase (xs : List (Option Nat)) : PseudoRandT Nat Option Nat := rdo
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
private def withIteratorProof : PseudoRand Nat Nat :=
  let it := [1, 2].iter
  letI := MeasureTheory.Iter.instMeasurableSpaceForIn' (n := PseudoRand Nat)
    (α := Std.Iterators.Types.ListIterator Nat)
  rdo
    let mut total := 0
    for h : n in it rdo
      have : it.IsPlausibleIndirectOutput n := h
      record n
      total := total + n
    return total

#guard run withIteratorProof == (3, 12)

-- The unfolding theorem supports kernel proofs about Measure, not just executable samplers.
example : mForIn ([] : List Nat).iter 17
    (fun _ _ => (0 : Measure (ForInStep Nat))) = Measure.dirac 17 := by
  rw [MeasureTheory.Iter.mForIn_eq_match_step (fun _ => measurable_from_nat)]
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

private def sample (n : Nat) : PseudoRand Nat Nat := rdo
  record n
  return n

#guard run (sampledSum sample [1, 3, 7]) == (4, 13)
#guard run (sampledSum sample []) 42 == (0, 42)

example : sampledSum (m := Measure) (fun _ => 0) [1, 3, 7] = 0 := by
  unfold sampledSum
  dsimp only
  rw [MeasureTheory.Iter.mForIn_eq_match_step (fun _ => measurable_from_nat)]
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
  rw [Rcc.mForIn_eq_mForIn_iter,
    MeasureTheory.Iter.mForIn_eq_match_step (fun _ => measurable_from_nat)]
  simp [Std.Rxc.Iterator.step_eq_step, Std.Rxc.Iterator.step, Std.Rcc.Internal.iter, mBind, mPure]

-- The optimized range must agree with the default consumer for an arbitrary lawful lift.
-- A real accumulator and an unrestricted body check that the equality requires neither
-- discreteness nor measurability of the loop body.
example
    (lift : ∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β],
      (α → Measure β) → MId α → Measure β)
    [LawfulMeasurableSpaceMonadLiftBindFunction
      (m := MId) (n := Measure)
      lift]
    (it : MeasureTheory.IterM (α := Std.Rxc.Iterator Nat) MId Nat) (init : ℝ)
    (f : (b : Nat) → it.IsPlausibleIndirectOutput b → ℝ → Measure {_s : ForInStep ℝ // True}) :
    MeasurableSpaceIteratorLoop.mForIn lift ℝ (fun _ _ _ => True) it init f =
      MeasurableSpaceIteratorLoop.defaultImplementation.mForIn
        lift ℝ (fun _ _ _ => True) it init f :=
  LawfulMeasurableSpaceIteratorLoop.lawful lift ℝ it init _
    MeasurableSpaceIteratorLoop.wellFounded_of_finite f

-- Each direct range form must preserve its endpoint convention and stop at type exhaustion.
private def rangeElements {ρ : Type} [MeasurableSpaceForIn (PseudoRand Nat) ρ UInt8]
    (r : ρ) : Array Nat :=
  ((rdo
    let mut elements := #[]
    for n in r rdo
      elements := elements.push n.toNat
    return elements : PseudoRand Nat (Array Nat)) ⟨0⟩).1

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

-- A typed binder must determine the range's element type before its literal bounds default.
#guard run (rdo
    let mut total : Int := 0
    for (i : Int) in 1...3 rdo
      total := total + i
    return total.toNat) == (3, 0)

-- The element type inferred from the body must determine a range with literal or absent bounds.
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
    have : MeasurableSpaceForIn (PseudoRand Nat) (Std.Rci Nat) Nat := inferInstance
  trivial

-- Unlike a finite-loop check, this requires the body's restriction to `.done` in the relation.
example (k : Nat) :
    MeasurableSpaceIteratorLoop.mForIn (n := Measure) (fun _ _ _ _ f x => f x.run)
      Nat (fun b _ s => s = .done b) (k...* : Std.Rci Nat).iter.toMeasurable 0
      (fun b _ _ => mPure ⟨.done b, rfl⟩) = Measure.dirac k := by
  rw [MeasurableSpaceIteratorLoop.mForIn_eq_match_step _ _ _ _
    (MeasurableSpaceIteratorLoop.wellFounded_of_productive (by intro b c s h; simp [h]))]
  simp only [MeasureTheory.IterM.inflate_step_id, Std.Iter.toMeasurable,
    Std.IterM.toCore_toMeasurable, Std.Rci.iter, Std.Iter.toIterM_mk,
    Std.Rxi.Iterator.Monadic.step_eq_step,
    Std.Rxi.Iterator.Monadic.step, Std.PRange.Nat.succ?_eq, Id.run_pure,
    Std.Shrink.inflate_deflate, Std.IterM.Step.toMeasurable, Std.IterStep.mapIterator, mPure_def,
    mBind_def]
  rw [Measure.dirac_bind]
  convert (measurable_const : Measurable
    (fun _ : {s : ForInStep Nat // s = .done k} => (mPure k : Measure Nat))) using 1
  ext ⟨step, h⟩
  cases h
  rfl

-- The ordinary-loop equation also works with an uncountable accumulator.
example (x : ℝ) :
    mForIn [()].iter x
      (fun _ a => (mPure (.done (a + 1)) : Measure (ForInStep ℝ))) = Measure.dirac (x + 1) := by
  rw [MeasureTheory.Iter.mForIn_eq_match_step (by intro; fun_prop)]
  simp only [List.step_iter_cons]
  rw [mPure_mBind]
  · rfl
  · apply measurable_fun_forInStep
    · exact measurable_mPure
    · apply MeasureTheory.Iter.measurable_mForIn
      intro _
      fun_prop

-- An arbitrary producer must choose its loop implementation, as in core. This guards
-- against reintroducing a blanket default that hides missing producer-specific instances.
example {α β : Type} [Std.Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β] : True := by
  fail_if_success
    have : MeasurableSpaceIteratorLoop α MId Measure := inferInstance
  trivial

-- The constructor check rules out a blanket discrete space on iterator states or steps.
-- The case-analysis check exercises the corresponding `fun_prop` rule over the Borel reals.
example : Measurable (fun x : ℝ =>
    Std.Shrink.deflate (Std.IterStep.yield (Std.IterM.mk x : Std.IterM (α := ℝ) Id ℝ) x)) := by
  fun_prop

example : Measurable (fun s : Std.IterStep ℝ ℝ =>
    match s with
    | .yield next out => next + out
    | .skip next => next
    | .done => 0) := by
  fun_prop

end TestNext.MeasurableSpaceMonad.ForInInstances
