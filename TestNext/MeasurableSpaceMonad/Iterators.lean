/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.Loop
import RandomDo.MeasurableSpaceMonad.Instances.Measure
import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom
import RandomDo.RDo.Loop
meta import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.Loop
meta import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom
meta import RandomDo.RDo.Loop

/-!
# Measurable producer regression checks

A single producer samples in the abstract measurable monad. The same loop is interpreted as a
measure and as a stateful sampler. The executable check observes both producer and body effects,
including the final state when the body stops early. The measure check detects dropping producer
effects. The total wrapper additionally checks the producer's termination instance.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open MeasureTheory Std

namespace TestNext.MeasurableSpaceMonad.Iterators

-- The action is a parameter, as functions are in core's combinators. It is not stored in a
-- function space with an invented measurable structure; the iterator state is just a counter.
private structure Samples (m : (α : Type) → [MeasurableSpace α] → Type) (sample : m Bool) where
  remaining : Nat

private instance {m : (α : Type) → [MeasurableSpace α] → Type} {sample : m Bool} :
    MeasurableSpace (Samples m sample) := MeasurableSpace.comap Samples.remaining inferInstance

private instance {m : (α : Type) → [MeasurableSpace α] → Type}
    [MeasurableSpaceMonad m] {sample : m Bool} :
    MeasurableSpaceIterator (Samples m sample) m Bool where
  IsPlausibleStep it
    | .yield it' _ => it.internalState.remaining = it'.internalState.remaining + 1
    | .skip _ => False
    | .done => it.internalState.remaining = 0
  step it :=
    match it.internalState.remaining with
    | 0 => mPure (Shrink.deflate (.done rfl))
    | k + 1 => rdo
      let b ← sample
      return Shrink.deflate (.yield ⟨⟨k⟩⟩ b rfl)

private instance {m : (α : Type) → [MeasurableSpace α] → Type}
    [MeasurableSpaceMonad m] {sample : m Bool} :
    MeasureTheory.Iterators.Finite (Samples m sample) m :=
  .of_finitenessRelation {
    Rel it' it := it'.internalState.remaining < it.internalState.remaining
    wf := (measure (fun it : MeasureTheory.IterM (α := Samples m sample) m Bool =>
      it.internalState.remaining)).wf
    subrelation := by
      rintro it it' ⟨s, hs, hp⟩
      cases s with
      | yield next out =>
        cases Option.some.inj hs
        exact hp ▸ Nat.lt_succ_self _
      | skip next => exact False.elim hp
      | done => cases hs }

private instance {m n : (α : Type) → [MeasurableSpace α] → Type}
    [MeasurableSpaceMonad m] [MeasurableSpaceMonad n] {sample : m Bool} :
    MeasurableSpaceIteratorLoop (Samples m sample) m n := .defaultImplementation

private def samples {m : (α : Type) → [MeasurableSpace α] → Type}
    (sample : m Bool) (k : Nat) : MeasureTheory.IterM (α := Samples m sample) m Bool := ⟨⟨k⟩⟩

private def countSamples {m : (α : Type) → [MeasurableSpace α] → Type}
    [MeasurableSpaceMonad m] (sample : m Bool) (onVisit : Bool → m Unit) (k : Nat) : m Nat := rdo
  let mut count := 0
  for b in (samples sample k).ensureTermination rdo
    onVisit b
    if b then count := count + 1
    if count = 2 then break
  return count

private def record (digit : Nat) : PseudoRand Nat Unit :=
  fun s => ((), ⟨10 * s.down + digit⟩)

private def run (x : PseudoRand Nat Nat) (s : Nat := 0) : Nat × Nat :=
  let (a, s') := x ⟨s⟩
  (a, s'.down)

-- The trace must be producer, body, producer, body. The third producer action must not run.
#guard run (countSamples (rdo record 1; return true) (fun _ => record 2) 3) == (2, 1212)
#guard run (countSamples (rdo record 1; return true) (fun _ => record 2) 0) 42 == (0, 42)

-- A certain sample must remain a nonzero measure on the correct next step.
example : (samples (m := Measure) (Measure.dirac true) 1).step =
    Measure.dirac (Shrink.deflate (.yield ⟨⟨0⟩⟩ true rfl)) := by
  dsimp only [samples, MeasureTheory.IterM.step, MeasurableSpaceIterator.step, mBind, mPure]
  exact Measure.dirac_bind measurable_from_top true

-- Producer effects remain present in the measure interpretation of the same program.
example : countSamples (m := Measure) 0 (fun _ => mPure ()) 3 = 0 := by
  have hs : (samples (m := Measure) 0 3).step = 0 := by
    dsimp only [samples, MeasureTheory.IterM.step, MeasurableSpaceIterator.step, mBind, mPure]
    exact Measure.bind_zero_left _
  unfold countSamples
  dsimp only
  simp only [mForIn, mForIn']
  rw [MeasurableSpaceIteratorLoop.mForIn_eq_match_step _ _ _ _
    MeasurableSpaceIteratorLoop.wellFounded_of_finite]
  dsimp only [MeasureTheory.IterM.ensureTermination]
  simp only [hs, mBind, mMonadLift]
  apply Eq.trans (congrArg (fun x : Measure Nat => x.bind (fun a => Measure.dirac a))
    (Measure.bind_zero_left _))
  exact Measure.bind_zero_left _


end TestNext.MeasurableSpaceMonad.Iterators
