/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.Measurability
public import RandomDo.MeasurableSpaceMonad.Defs

/-!
# Iterators with measurable producer effects

This file follows `Init.Data.Iterators.Basic`. Both the producer and the consumer can use a
measurable space monad. The producer's state and output carry their supplied measurable spaces;
these induce the space on its proof-carrying step type.

## Main definitions

* `IterM`: An iterator which produces values in a measurable space monad.
* `MeasurableSpaceIterator`: A typeclass which specifies the steps of an iterator.
* `Iterators.Finite`: Asserts that an iterator has only finitely many steps.

Core's `IterStep`, `PlausibleIterStep`, and `Shrink` are reused. The iterator and its termination
relations need counterparts because core's `IterM` takes an ordinary monad constructor.
The conversions for existing core producers are in `Iterators.Core`.
-/

@[expose] public section

namespace MeasureTheory

open Std

universe w w' x

#check Std.IterM

/-- An iterator which produces values of type `β` in a measurable space monad `m`.
Analogue of `Std.IterM`. -/
@[ext]
structure IterM {α : Type w} (m : (γ : Type w) → [MeasurableSpace γ] → Type w')
    (β : Type w) where
  /-- The internal state of the iterator. -/
  internalState : α

-- These instances use the state space, just as the instances for core iterators do.
instance IterM.instMeasurableSpace {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} [MeasurableSpace α] :
    MeasurableSpace (IterM (α := α) m β) :=
  MeasurableSpace.comap IterM.internalState inferInstance

@[fun_prop] theorem IterM.measurable_internalState {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} [MeasurableSpace α] :
    Measurable (IterM.internalState (α := α) (m := m) (β := β)) :=
  comap_measurable _

@[fun_prop] theorem IterM.measurable_mk {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} [MeasurableSpace α] :
    Measurable (IterM.mk : α → IterM (α := α) m β) :=
  measurable_comap_iff.mpr measurable_id

#check Std.Iterator

/-- A typeclass which specifies the steps of an iterator in a measurable space monad.
Analogue of `Std.Iterator`. -/
class MeasurableSpaceIterator (α : Type w)
    (m : (γ : Type w) → [MeasurableSpace γ] → Type w') (β : outParam (Type w))
    [MeasurableSpace α] [MeasurableSpace β] where
  /-- The steps which the iterator can plausibly take. -/
  IsPlausibleStep : IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop
  /-- Take one step, together with a proof that the step is plausible. -/
  step : (it : IterM (α := α) m β) → m (Shrink <| PlausibleIterStep <| IsPlausibleStep it)

theorem IterM.mk_internalState {α m β} (it : IterM (α := α) m β) :
    ⟨it.internalState⟩ = it := by
  simp

@[simp]
theorem IterM.internalState_mk {α m β} (it : α) :
    (⟨it⟩ : IterM m β).internalState = it :=
  rfl

#check Std.IterM.IsPlausibleStep

/-- The steps which the iterator can plausibly take. Analogue of `Std.IterM.IsPlausibleStep`. -/
abbrev IterM.IsPlausibleStep {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {β : Type w} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] :
    IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop :=
  MeasurableSpaceIterator.IsPlausibleStep (α := α) (m := m)

/--
The type of the step object returned by `IterM.step`, containing an `IterStep`
and a proof that this is a plausible step for the given iterator.
-/
abbrev IterM.Step {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    (it : IterM (α := α) m β) :=
  PlausibleIterStep it.IsPlausibleStep

/--
Makes a single step with the given iterator `it`, potentially emitting a value and providing a
succeeding iterator. If this function is used recursively, termination can sometimes be proved with
the termination measure `it.finitelyManySteps`.
-/
@[always_inline, inline]
def IterM.step {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    (it : IterM (α := α) m β) : m (Shrink it.Step) :=
  MeasurableSpaceIterator.step it

#check Std.IterM.step_eq

theorem IterM.step_eq {α m β} [MeasurableSpace α] [MeasurableSpace β]
    {IsPlausibleStep step} {it : IterM (α := α) m β} :
    letI : MeasurableSpaceIterator α m β := ⟨IsPlausibleStep, step⟩
    it.step = step it := rfl

#check Std.IterM.step_mk

theorem IterM.step_mk {α m β} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] (it : α) :
    (⟨it⟩ : IterM m β).step = MeasurableSpaceIterator.step (⟨it⟩ : IterM m β) := by
  simp [IterM.step_eq]

/--
Asserts that a certain output value could plausibly be emitted by the given iterator in its next
step.
-/
def IterM.IsPlausibleOutput {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {β : Type w} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    (it : IterM (α := α) m β) (out : β) : Prop :=
  ∃ it', it.IsPlausibleStep (.yield it' out)

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it`.
-/
def IterM.IsPlausibleSuccessorOf {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {β : Type w} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    (it' it : IterM (α := α) m β) : Prop :=
  ∃ step, step.successor = some it' ∧ it.IsPlausibleStep step

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it` while no value is emitted (see `IterStep.skip`).
-/
def IterM.IsPlausibleSkipSuccessorOf {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ]
    → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] (it' it : IterM (α
    := α) m β) : Prop :=
  it.IsPlausibleStep (.skip it')

inductive IterM.IsPlausibleIndirectOutput {α β : Type w} {m : (γ : Type w) → [MeasurableSpace γ]
    → Type w'} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    : IterM (α := α) m β → β → Prop where
  /-- The output value could plausibly be emitted in the next step. -/
  | direct {it : IterM (α := α) m β} {out : β} : it.IsPlausibleOutput out →
      it.IsPlausibleIndirectOutput out
  /-- The output value could plausibly be emitted in a step after the next step. -/
  | indirect {it it' : IterM (α := α) m β} {out : β} : it'.IsPlausibleSuccessorOf it →
      it'.IsPlausibleIndirectOutput out → it.IsPlausibleIndirectOutput out

/--
Asserts that an iterator `it'` could plausibly produce `it'` as a successor iterator after
finitely many steps. This relation is reflexive.
-/
inductive IterM.IsPlausibleIndirectSuccessorOf {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] : IterM (α := α) m β
    → IterM (α := α) m β → Prop where
  /-- Every iterator is a plausible indirect successor of itself. -/
  | refl (it : IterM (α := α) m β) : it.IsPlausibleIndirectSuccessorOf it
  /-- The iterator is a plausible successor of one of the current iterator's successors. -/
  | cons_right {it'' it' it : IterM (α := α) m β} (h' : it''.IsPlausibleIndirectSuccessorOf it')
      (h : it'.IsPlausibleSuccessorOf it) : it''.IsPlausibleIndirectSuccessorOf it

theorem IterM.IsPlausibleIndirectSuccessorOf.trans {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] {it'' it' it : IterM
    (α := α) m β}
    (h' : it''.IsPlausibleIndirectSuccessorOf it') (h : it'.IsPlausibleIndirectSuccessorOf it) :
    it''.IsPlausibleIndirectSuccessorOf it := by
  induction h
  case refl => exact h'
  case cons_right ih => exact IsPlausibleIndirectSuccessorOf.cons_right ih ‹_›

theorem IterM.IsPlausibleIndirectSuccessorOf.single {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] {it' it : IterM (α
    := α) m β}
    (h : it'.IsPlausibleSuccessorOf it) :
    it'.IsPlausibleIndirectSuccessorOf it :=
  .cons_right (.refl _) h

theorem IterM.IsPlausibleIndirectOutput.trans {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {it' it : IterM (α := α) m β} {out : β} (h : it'.IsPlausibleIndirectSuccessorOf it)
    (h' : it'.IsPlausibleIndirectOutput out) : it.IsPlausibleIndirectOutput out := by
  induction h
  case refl => exact h'
  case cons_right ih => exact IsPlausibleIndirectOutput.indirect ‹_› ih

#check Std.Iterators.Finite

/-- The relation of plausible successors is well-founded. Analogue of `Std.Iterators.Finite`. -/
class Iterators.Finite (α : Type w) (m : (γ : Type w) → [MeasurableSpace γ] → Type w')
    {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] : Prop where
  /-- The relation of plausible successors is well-founded. -/
  wf : WellFounded (IterM.IsPlausibleSuccessorOf (α := α) (m := m))

open MeasureTheory.Iterators


structure IterM.TerminationMeasures.Finite
    (α : Type w) (m : (γ : Type w) → [MeasurableSpace γ] → Type w') {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] where
  /--
  The wrapped iterator.

  In the wrapper, its finiteness is used as a termination measure.
  -/
  it : IterM (α := α) m β

/--
The relation of plausible successors on `IterM.TerminationMeasures.Finite`. It is well-founded
if there is a `Finite` instance.
-/
def IterM.TerminationMeasures.Finite.Rel
    {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] :
    TerminationMeasures.Finite α m → TerminationMeasures.Finite α m → Prop :=
  Relation.TransGen <| InvImage IterM.IsPlausibleSuccessorOf IterM.TerminationMeasures.Finite.it

instance IterM.TerminationMeasures.instWellFoundedRelationFinite {α : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {β : Type w} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    [Iterators.Finite α m] :
    WellFoundedRelation (IterM.TerminationMeasures.Finite α m) where
  rel := IterM.TerminationMeasures.Finite.Rel
  wf := by exact (InvImage.wf _ Iterators.Finite.wf).transGen

/--
Termination measure to be used in well-founded recursive functions recursing over a finite iterator
(see also `Finite`).
-/
def IterM.finitelyManySteps {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {β : Type w} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    [Iterators.Finite α m] (it : IterM (α := α) m β) : IterM.TerminationMeasures.Finite α m :=
  ⟨it⟩

/--
Termination measure to be used in recursive functions built with `WellFounded.extrinsicFix`
recursing over a finite iterator without requiring a proof of finiteness (see also `Finite`).
-/
def IterM.finitelyManySteps! {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {β : Type w} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    (it : IterM (α := α) m β) : IterM.TerminationMeasures.Finite α m :=
  ⟨it⟩

/--
This theorem is used by a `decreasing_trivial` extension. It powers automatic termination proofs
with `IterM.finitelyManySteps`.
-/
theorem IterM.TerminationMeasures.Finite.rel_of_yield
    {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {it it' : IterM (α := α) m β} {out : β} (h : it.IsPlausibleStep (.yield it' out)) :
    Rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

@[inherit_doc IterM.TerminationMeasures.Finite.rel_of_yield]
theorem IterM.TerminationMeasures.Finite.rel_of_skip
    {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {it it' : IterM (α := α) m β} (h : it.IsPlausibleStep (.skip it')) :
    Rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

theorem IterM.TerminationMeasures.Finite.rel_trans
    {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {it it' it'' : TerminationMeasures.Finite α m} :
    it.Rel it' → it'.Rel it'' → it.Rel it'' :=
  .trans

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
  | exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
  | fail)


#check Std.Iterators.Productive

/-- The relation of plausible skip successors is well-founded.
Analogue of `Std.Iterators.Productive`. -/
class Iterators.Productive (α m) {β} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] : Prop where
  /-- The relation of plausible successors during skips is well-founded. -/
  wf : WellFounded (IterM.IsPlausibleSkipSuccessorOf (α := α) (m := m))

theorem IterM.isPlausibleSuccessorOf_of_yield
    {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {it' it : IterM (α := α) m β} {out : β} (h : it.IsPlausibleStep (.yield it' out)) :
    it'.IsPlausibleSuccessorOf it :=
  ⟨_, rfl, h⟩

theorem IterM.isPlausibleSuccessorOf_of_skip
    {α m β} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] {it it'
    : IterM (α := α) m β}
    (h : it.IsPlausibleStep (.skip it')) :
    it'.IsPlausibleSuccessorOf it :=
  ⟨_, rfl, h⟩


instance Iterators.instProductiveOfFinite {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [Iterators.Finite α m] :
    Iterators.Productive α m where
  wf := by
    apply Subrelation.wf (r := IterM.IsPlausibleSuccessorOf)
    · intro it' it h
      exact IterM.isPlausibleSuccessorOf_of_skip h
    · exact Iterators.Finite.wf

#check Std.LawfulDeterministicIterator

/-- Every iterator state has exactly one plausible step.
Analogue of `Std.LawfulDeterministicIterator`. -/
class LawfulDeterministicMeasurableSpaceIterator {β : Type w} (α : Type w)
    (m : (γ : Type w) → [MeasurableSpace γ] → Type w') [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β]
    where
  /--
  Every iterator with state `α` in monad `m` has exactly one plausible step.
  -/
  isPlausibleStep_eq_eq : ∀ it : IterM (α := α) m β, ∃ step, it.IsPlausibleStep = (· = step)


namespace Iterators

/--
This structure provides a more convenient way to define `Finite α m` instances using
`Finite.of_finitenessRelation : FinitenessRelation α m → Finite α m`.
-/
structure FinitenessRelation (α : Type w) (m : (γ : Type w) → [MeasurableSpace γ] → Type w')
    {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] where
  /--
  A well-founded relation such that if `it'` is a successor iterator of `it`, then `Rel it' it`.
  -/
  Rel (it' it : IterM (α := α) m β) : Prop
  /-- `Rel` is well-founded. -/
  wf : WellFounded Rel
  /-- If `it'` is a successor iterator of `it`, then `Rel it' it`. -/
  subrelation : ∀ {it it'}, it'.IsPlausibleSuccessorOf it → Rel it' it

theorem Finite.of_finitenessRelation
    {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] (r
    : FinitenessRelation α m) : Finite α m where
  wf := by
    refine Subrelation.wf (r := r.Rel) ?_ ?_
    · intro x y h
      apply FinitenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact r.wf

/--
This structure provides a more convenient way to define `Productive α m` instances using
`Productive.of_productivenessRelation : ProductivenessRelation α m → Productive α m`.
-/
structure ProductivenessRelation (α : Type w) (m : (γ : Type w) → [MeasurableSpace γ] → Type w')
    {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] where
  /--
  A well-founded relation such that if `it'` is obtained from `it` by skipping, then `Rel it' it`.
  -/
  Rel : (IterM (α := α) m β) → (IterM (α := α) m β) → Prop
  /-- `Rel` is well-founded. -/
  wf : WellFounded Rel
  /-- If `it'` is obtained from `it` by skipping, then `Rel it' it`. -/
  subrelation : ∀ {it it'}, it'.IsPlausibleSkipSuccessorOf it → Rel it' it

theorem Productive.of_productivenessRelation
    {α : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] (r
    : ProductivenessRelation α m) : Productive α m where
  wf := by
    refine Subrelation.wf (r := r.Rel) ?_ ?_
    · intro x y h
      apply ProductivenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact r.wf

end Iterators

#check Std.IterM.inductSteps

/-- Induction over the plausible steps of a finite iterator. Analogue of `Std.IterM.inductSteps`. -/
@[specialize]
def IterM.inductSteps {α m β} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [Finite α m]
  (motive : IterM (α := α) m β → Sort x)
  (step : (it : IterM (α := α) m β) →
    (ih_yield : ∀ {it' : IterM (α := α) m β} {out : β},
      it.IsPlausibleStep (.yield it' out) → motive it') →
    (ih_skip : ∀ {it' : IterM (α := α) m β}, it.IsPlausibleStep (.skip it') → motive it') →
    motive it)
  (it : IterM (α := α) m β) : motive it :=
  step it
    (fun {it' _} _ => inductSteps motive step it')
    (fun {it'} _ => inductSteps motive step it')
termination_by it.finitelyManySteps

#check Std.IterM.Partial

/-- Compatibility wrapper for partial consumers. Analogue of `Std.IterM.Partial`. -/
structure IterM.Partial {α : Type w}
    (m : (γ : Type w) → [MeasurableSpace γ] → Type w') (β : Type w) where
  /-- The wrapped iterator. -/
  it : IterM (α := α) m β

#check Std.IterM.Total

/-- An iterator whose consumers require termination. Analogue of `Std.IterM.Total`. -/
structure IterM.Total {α : Type w}
    (m : (γ : Type w) → [MeasurableSpace γ] → Type w') (β : Type w) where
  /-- The wrapped iterator. -/
  it : IterM (α := α) m β

#check Std.IterM.ensureTermination

/-- Use the consumers that require a termination proof. Analogue of `Std.IterM.ensureTermination`.
-/
@[always_inline, inline]
def IterM.ensureTermination {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} (it : IterM (α := α) m β) :
    IterM.Total (α := α) m β := ⟨it⟩

end MeasureTheory
