/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.Basic
public import RandomDo.MeasurableSpaceMonad.ForIn
public import RandomDo.MeasurableSpaceMonad.Lift
public import RandomDo.RDo.Core
public import Init.Data.Iterators.Consumers.Loop
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Monadic.Basic
import all Init.Data.Iterators.Basic

/-!
# Iterator loops in measurable space monads

This file adapts core's iterator consumers to `mPure` and `mBind`. Both the producer monad `m`
and the consumer monad `n` are measurable space monads. Their supplied measurable spaces induce
the step space; the lifting function passes a producer step to the loop body.

Existing core iterators are supported by the conversions and instances in `Iterators.CoreLoop`.

## Main definitions

* `MeasurableSpaceIteratorLoop`: A typeclass which specifies how to iterate over an iterator
in a measurable space monad.
* `LawfulMeasurableSpaceIteratorLoop`: Asserts that a given `MeasurableSpaceIteratorLoop`
instance is equal to `MeasurableSpaceIteratorLoop.defaultImplementation`.

## Main theorems

* `MeasurableSpaceIteratorLoop.mForIn_eq_match_step`: Expresses a well-founded loop in terms of its
first step and the remaining loop.
-/

@[expose] public section

namespace MeasureTheory

open Std MeasureTheory.Iterators MeasureTheory.Internal

universe w w' w'' x x'

#check Std.IteratorLoop.rel
#check Std.IteratorLoop.WellFounded

/--
Relation that needs to be well-formed in order for a loop over an iterator to terminate.
It is assumed that the `plausible_forInStep` predicate relates the input and output of the
stepper function.
-/
def MeasurableSpaceIteratorLoop.rel (α : Type w)
    (m : (γ : Type w) → [MeasurableSpace γ] → Type w') {β : Type w} [MeasurableSpace α]
    [MeasurableSpace β]
    [MeasurableSpaceIterator α m β]
    {γ : Type x} (plausible_forInStep : β → γ → ForInStep γ → Prop)
    (p' p : IterM (α := α) m β × γ) : Prop :=
  (∃ b, p.1.IsPlausibleStep (.yield p'.1 b) ∧ plausible_forInStep b p.2 (.yield p'.2)) ∨
    (p.1.IsPlausibleStep (.skip p'.1) ∧ p'.2 = p.2)

/--
Asserts that `MeasurableSpaceIteratorLoop.rel` is well-founded.
-/
def MeasurableSpaceIteratorLoop.WellFounded (α : Type w)
    (m : (γ : Type w) → [MeasurableSpace γ] → Type w') {β : Type w} [MeasurableSpace α]
    [MeasurableSpace β]
    [MeasurableSpaceIterator α m β]
    {γ : Type x} (plausible_forInStep : β → γ → ForInStep γ → Prop) : Prop :=
    _root_.WellFounded (MeasurableSpaceIteratorLoop.rel α m plausible_forInStep)

#check Std.IteratorLoop
#check Std.IteratorLoop.forIn

/--
Loop consumers for an iterator and a measurable space monad. Analogue of `Std.IteratorLoop`.
-/
@[ext]
class MeasurableSpaceIteratorLoop (α : Type w) (m : (γ : Type w) → [MeasurableSpace γ] → Type w')
    {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    (n : (γ : Type x) → [MeasurableSpace γ] → Type x') where
  /-- Iteration over the iterator `it` in the manner expected by `for` loops. -/
  mForIn : ∀ (_liftBind : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ),
    (γ : Type x) → [MeasurableSpace γ] →
    (plausible_forInStep : β → γ → ForInStep γ → Prop) →
    (it : IterM (α := α) m β) → γ →
    ((b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (plausible_forInStep b c))) →
    n γ

#check Std.IteratorLoop.WithWF

/-- Internal implementation detail of the iterator library. -/
structure MeasurableSpaceIteratorLoop.WithWF (α : Type w)
    (m : (γ : Type w) → [MeasurableSpace γ] → Type w') {β : Type w} [MeasurableSpace α]
    [MeasurableSpace β]
    [MeasurableSpaceIterator α m β]
    {γ : Type x} (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    (hwf : MeasurableSpaceIteratorLoop.WellFounded α m PlausibleForInStep) where
  /-- Internal implementation detail of the iterator library. -/
  it : IterM (α := α) m β
  /-- Internal implementation detail of the iterator library. -/
  acc : γ

instance MeasurableSpaceIteratorLoop.WithWF.instWellFoundedRelation
    (α : Type w) (m : (γ : Type w) → [MeasurableSpace γ] → Type w') {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {γ : Type x} (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    (hwf : MeasurableSpaceIteratorLoop.WellFounded α m PlausibleForInStep) :
    WellFoundedRelation (WithWF α m PlausibleForInStep hwf) where
  rel := InvImage (MeasurableSpaceIteratorLoop.rel α m PlausibleForInStep) (fun x => (x.it, x.acc))
  wf := by exact InvImage.wf _ hwf

/--
This is the loop implementation of the default instance
`MeasurableSpaceIteratorLoop.defaultImplementation`.
Analogue of `Std.IterM.DefaultConsumers.forIn'`.
-/
@[always_inline, inline]
def IterM.DefaultConsumers.mForIn'
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {α : Type w} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    (lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ)
    (γ : Type x) [MeasurableSpace γ]
    (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    (it : IterM (α := α) m β) (init : γ)
    (P : β → Prop) (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (Subtype (PlausibleForInStep b c))) : n γ :=
  haveI : Nonempty γ := ⟨init⟩
  WellFounded.extrinsicFix₃ (C₃ := fun _ _ _ => n γ)
    (InvImage (MeasurableSpaceIteratorLoop.rel α m PlausibleForInStep) (fun x => (x.1, x.2.1)))
    (fun it acc (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b) recur =>
      (lift _ _ · it.step) fun s => rdo
        match s.inflate with
        | .yield it' out h =>
          match ← f out (hP out <| .direct ⟨_, h⟩) acc with
          | ⟨.yield c, h'⟩ =>
            recur it' c (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') (Or.inl ⟨out, ‹_›, ‹_›⟩)
          | ⟨.done c, _⟩ => return c
        | .skip it' h =>
          recur it' acc (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') (Or.inr ⟨‹_›, rfl⟩)
        | .done _ => return acc) it init hP

/-- The well-founded reference implementation of the default loop instance
`MeasurableSpaceIteratorLoop.defaultImplementation`.
Analogue of `Std.IterM.DefaultConsumers.forIn'.wf`. -/
@[specialize]
def IterM.DefaultConsumers.mForIn'.wf
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {α : Type w} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    (lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ)
    (γ : Type x) [MeasurableSpace γ]
    (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    (wf : MeasurableSpaceIteratorLoop.WellFounded α m PlausibleForInStep)
    (it : IterM (α := α) m β) (init : γ)
    (P : β → Prop) (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (Subtype (PlausibleForInStep b c))) : n γ :=
  haveI : WellFounded _ := wf
  (lift _ _ · it.step) fun s =>
    match s.inflate with
    | .yield it' out h => rdo
      match ← f out (hP _ <| .direct ⟨_, h⟩) init with
      | ⟨.yield c, _⟩ =>
        IterM.DefaultConsumers.mForIn'.wf lift _ PlausibleForInStep wf it' c P
          (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
      | ⟨.done c, _⟩ => return c
    | .skip it' h =>
      IterM.DefaultConsumers.mForIn'.wf lift _ PlausibleForInStep wf it' init P
          (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
    | .done _ => mPure init
termination_by MeasurableSpaceIteratorLoop.WithWF.mk it init (hwf := wf)
decreasing_by
  · exact Or.inl ⟨out, ‹_›, ‹_›⟩
  · exact Or.inr ⟨‹_›, rfl⟩

/--
This is the default implementation of the `MeasurableSpaceIteratorLoop` class.
It simply iterates through the iterator using `IterM.step`. For certain iterators,
more efficient implementations are possible and should be used instead.
Analogue of `Std.IteratorLoop.defaultImplementation`.
-/
@[always_inline, inline, instance_reducible]
def MeasurableSpaceIteratorLoop.defaultImplementation {β α : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] : MeasurableSpaceIteratorLoop α m n where
  mForIn lift γ _ Pl it init :=
    IterM.DefaultConsumers.mForIn' lift γ Pl it init _ (fun _ => id)

/--
Asserts that a given `MeasurableSpaceIteratorLoop` instance is equal to
`MeasurableSpaceIteratorLoop.defaultImplementation`. Analogue of `Std.LawfulIteratorLoop`.
-/
class LawfulMeasurableSpaceIteratorLoop {β : Type w} (α : Type w)
    (m : (γ : Type w) → [MeasurableSpace γ] → Type w')
    (n : (γ : Type x) → [MeasurableSpace γ] → Type x') [MeasurableSpaceMonad m]
    [MeasurableSpaceMonad n]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]
    [∀ δ, [MeasurableSpace δ] → MeasurableSpace (n δ)]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    [i : MeasurableSpaceIteratorLoop α m n] where
  /-- Equality with the default implementation for any lawful measurable lifting function.
  Analogue of `Std.LawfulIteratorLoop.lawful`. -/
  lawful (lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ)
    [LawfulMeasurableSpaceMonadLiftBindFunction lift]
    (γ : Type x) [MeasurableSpace γ] (it : IterM (α := α) m β) (init : γ)
    (Pl : β → γ → ForInStep γ → Prop) (wf : MeasurableSpaceIteratorLoop.WellFounded α m Pl)
    (f : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    i.mForIn lift γ Pl it init f =
      MeasurableSpaceIteratorLoop.defaultImplementation.mForIn lift γ Pl it init f

instance instLawfulMeasurableSpaceIteratorLoopDefaultImplementation
    {β : Type w} (α : Type w) (m : (γ : Type w) → [MeasurableSpace γ] → Type w')
    (n : (γ : Type x) → [MeasurableSpace γ] → Type x') [MeasurableSpaceMonad m]
    [MeasurableSpaceMonad n]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]
    [∀ δ, [MeasurableSpace δ] → MeasurableSpace (n δ)]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β] [Finite α m] :
    letI : MeasurableSpaceIteratorLoop α m n := .defaultImplementation
    LawfulMeasurableSpaceIteratorLoop α m n := by
  let : MeasurableSpaceIteratorLoop α m n := .defaultImplementation
  constructor; simp

theorem MeasurableSpaceIteratorLoop.wellFounded_of_finite
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {α β : Type w} {γ : Type x} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [Finite α m] {P : β → γ → ForInStep γ → Prop} :
    WellFounded α m (γ := γ) P := by
  apply Subrelation.wf
    (r := InvImage IterM.TerminationMeasures.Finite.Rel (fun p => p.1.finitelyManySteps))
  · intro p' p h
    apply Relation.TransGen.single
    obtain ⟨b, h, _⟩ | ⟨h, _⟩ := h
    · exact ⟨.yield p'.fst b, rfl, h⟩
    · exact ⟨.skip p'.fst, rfl, h⟩
  · apply InvImage.wf
    exact WellFoundedRelation.wf

theorem MeasurableSpaceIteratorLoop.wellFounded_of_productive {α β : Type w} {γ : Type x} {m :
    (γ : Type w) → [MeasurableSpace γ] → Type w'}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    [MeasurableSpaceIteratorLoop α m m] [Productive α m] {P : β → γ → ForInStep γ → Prop}
    (hp : ∀ {b g s}, P b g s → s matches ForInStep.done ..) :
    WellFounded α m (γ := γ) P := by
  rw [WellFounded]
  unfold MeasurableSpaceIteratorLoop.rel
  have {b g q} : ¬ P b g (ForInStep.yield q) := fun h => by simpa using hp h
  simp only [and_false, exists_false, false_or, this]
  exact Subrelation.wf And.left (InvImage.wf Prod.fst Productive.wf)

#check Std.IteratorLoop.finiteForIn'

/-- Membership-aware iteration using an explicit lifting function.
Analogue of `Std.IteratorLoop.finiteForIn'`. -/
@[always_inline, inline, instance_reducible]
def MeasurableSpaceIteratorLoop.finiteForIn' {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'}
    {α : Type w} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [MeasurableSpaceIteratorLoop α m n]
    [MeasurableSpaceMonad n]
    (lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ) :
    MeasurableSpaceForIn' n (IterM (α := α) m β) β
      ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  mForIn' {γ} _ it init f :=
    MeasurableSpaceIteratorLoop.mForIn (α := α) (m := m) lift γ (fun _ _ _ => True) it init
      (rdo return ⟨← f · · ·, trivial⟩)

-- As in core, the monadic instance constructs its handler from a lift and bind.
-- Its intermediate step space is induced by the supplied state and element spaces.
#check Std.IterM.instForIn'

/-- Membership-aware iteration. Analogue of `Std.IterM.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate. -/
@[always_inline, inline, instance_reducible]
def IterM.instMeasurableSpaceForIn' {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [MeasurableSpaceIteratorLoop α m n]
    [MeasurableSpaceMonad n] [MeasurableSpaceMonadLiftT m n] :
    MeasurableSpaceForIn' n (IterM (α := α) m β) β
      ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ :=
  MeasurableSpaceIteratorLoop.finiteForIn' fun _ _ _ _ f x =>
    mMonadLift (m := m) x >>=ₘ f

#check Std.IterM.instForInOfIteratorLoop

instance IterM.instMeasurableSpaceForInOfIteratorLoop
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [MeasurableSpaceIteratorLoop α m n]
    [MeasurableSpaceMonadLiftT m n] [MeasurableSpaceMonad n] :
    MeasurableSpaceForIn n (IterM (α := α) m β) β :=
  haveI : MeasurableSpaceForIn' n (IterM (α := α) m β) β _ := IterM.instMeasurableSpaceForIn'
  instMeasurableSpaceForInOfForIn'

#check Std.IterM.Partial.instForIn'

/-- Membership-aware iteration. Analogue of `Std.IterM.Partial.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate. -/
@[always_inline, inline, instance_reducible]
def IterM.Partial.instMeasurableSpaceForIn' {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [MeasurableSpaceIteratorLoop α m n]
    [MeasurableSpaceMonadLiftT m n] [MeasurableSpaceMonad n] :
    MeasurableSpaceForIn' n (IterM.Partial (α := α) m β) β
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  mForIn' it init f :=
    haveI := @IterM.instMeasurableSpaceForIn'
    mForIn' it.it init f

#check Std.IterM.Total.instForIn'

/-- Membership-aware iteration. Analogue of `Std.IterM.Total.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate.
The `Finite` assumption restricts the total wrapper to terminating iterators; its implementation
reuses the ordinary consumer. -/
@[always_inline, inline, instance_reducible, nolint unusedArguments]
def IterM.Total.instMeasurableSpaceForIn' {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [MeasurableSpaceIteratorLoop α m n]
    [MeasurableSpaceMonadLiftT m n] [MeasurableSpaceMonad n]
    [Finite α m] :
    MeasurableSpaceForIn' n (IterM.Total (α := α) m β) β
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  mForIn' it init f := IterM.instMeasurableSpaceForIn'.mForIn' it.it init f

#check Std.IterM.Partial.instForInOfIteratorLoop

instance IterM.Partial.instMeasurableSpaceForInOfIteratorLoop
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [MeasurableSpaceIteratorLoop α m n]
    [MeasurableSpaceMonadLiftT m n] [MeasurableSpaceMonad n] :
    MeasurableSpaceForIn n (IterM.Partial (α := α) m β) β :=
  haveI : MeasurableSpaceForIn' n (IterM.Partial (α := α) m β) β _ :=
    IterM.Partial.instMeasurableSpaceForIn'
  instMeasurableSpaceForInOfForIn'

#check Std.instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite

instance {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [MeasurableSpaceIteratorLoop α m n]
    [MeasurableSpaceMonadLiftT m n] [MeasurableSpaceMonad n]
    [Finite α m] :
    MeasurableSpaceForIn n (IterM.Total (α := α) m β) β :=
  haveI : MeasurableSpaceForIn' n (IterM.Total (α := α) m β) β _ :=
    IterM.Total.instMeasurableSpaceForIn'
  instMeasurableSpaceForInOfForIn'

-- This is a structural equation, so its proof needs no measurable monad laws.
-- Requiring them, as in core's statement, would also require spaces on all computation types.
#check Std.IterM.DefaultConsumers.forIn'_eq_match_step

/-- Unfold the default consumer when its iteration relation is well-founded. -/
theorem IterM.DefaultConsumers.mForIn'_eq_match_step
    {α β : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    {lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ}
    {γ : Type x} [MeasurableSpace γ] {it : IterM (α := α) m β} {init : γ}
    {P : β → Prop} {hP : ∀ b, it.IsPlausibleIndirectOutput b → P b}
    (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    {f : (b : β) → P b → (c : γ) → n (Subtype (PlausibleForInStep b c))}
    (wf : MeasurableSpaceIteratorLoop.WellFounded α m PlausibleForInStep) :
    mForIn' lift γ PlausibleForInStep it init P hP f =
      (lift _ _ · it.step) (fun s =>
        match s.inflate with
        | .yield it' out h => rdo
          match ← f out (hP _ <| .direct ⟨_, h⟩) init with
          | ⟨.yield c, _⟩ =>
            mForIn' lift _ PlausibleForInStep it' c P
              (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
          | ⟨.done c, _⟩ => return c
        | .skip it' h =>
          mForIn' lift _ PlausibleForInStep it' init P
            (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
        | .done _ => mPure init) := by
  have : Nonempty γ := ⟨init⟩
  rw [mForIn', WellFounded.extrinsicFix₃_eq_apply]
  · congr; ext step
    cases step.inflate using Std.PlausibleIterStep.casesOn
    · simp only
      apply MeasurableSpaceBind.bind_congr; intro step
      split <;> simp [mForIn']
    · simp [mForIn']
    · simp
  · apply InvImage.wf
    exact wf

#check Std.IterM.DefaultConsumers.forIn'_eq_wf

/-- The default consumer agrees with its well-founded reference implementation. -/
theorem IterM.DefaultConsumers.mForIn'_eq_wf
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {α : Type w} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    {lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ}
    {γ : Type x} [MeasurableSpace γ]
    (Pl : β → γ → ForInStep γ → Prop) (wf : MeasurableSpaceIteratorLoop.WellFounded α m Pl)
    {it : IterM (α := α) m β} {init : γ}
    {P : β → Prop} {hP : ∀ b, it.IsPlausibleIndirectOutput b → P b}
    (f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))) :
    mForIn' lift γ Pl it init P hP f =
      mForIn'.wf lift γ Pl wf it init P hP f := by
  have : Nonempty γ := ⟨init⟩
  rw [mForIn', WellFounded.extrinsicFix₃_eq_fix]; rotate_left
  · apply InvImage.wf
    exact wf
  · fun_induction mForIn'.wf lift γ Pl wf it init P hP f
    rename_i ihy ihs
    rw [WellFounded.fix_eq]
    congr 1; ext step
    cases step.inflate using Std.PlausibleIterStep.casesOn
    · apply MeasurableSpaceBind.bind_congr; intro forInStep
      match forInStep with
      | ⟨.yield c, h⟩ => simp (discharger := assumption) [ihy]
      | ⟨.done c, h⟩ => simp
    · simp (discharger := assumption) [ihs]
    · simp

#check Std.IterM.DefaultConsumers.forIn'_eq_wf_of_finite

/-- A finite iterator's default consumer agrees with its well-founded implementation. -/
theorem IterM.DefaultConsumers.mForIn'_eq_wf_of_finite
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {α : Type w} {β : Type w} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIterator α m β] [Finite α m]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    {lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ}
    {γ : Type x} [MeasurableSpace γ] {it : IterM (α := α) m β} {init : γ}
    {P : β → Prop} {hP : ∀ b, it.IsPlausibleIndirectOutput b → P b}
    (f : (b : β) → P b → (c : γ) → n (Subtype (fun _ : ForInStep γ => True))) :
    mForIn' lift γ (fun _ _ _ => True) it init P hP f =
      mForIn'.wf lift γ (fun _ _ _ => True)
        MeasurableSpaceIteratorLoop.wellFounded_of_finite it init P hP f := by
  apply mForIn'_eq_wf

#check Std.IterM.DefaultConsumers.forIn'_eq_forIn'

/-- The default consumer is independent of the predicate used to carry membership information. -/
theorem IterM.DefaultConsumers.mForIn'_eq_mForIn'
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} {α : Type w} {β : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    {lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ}
    {γ : Type x} [MeasurableSpace γ]
    {it : IterM (α := α) m β} {init : γ}
    {P : β → Prop} {hP : ∀ b, it.IsPlausibleIndirectOutput b → P b}
    {Q : β → Prop} {hQ : ∀ b, it.IsPlausibleIndirectOutput b → Q b}
    (Pl : β → γ → ForInStep γ → Prop)
    {f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))}
    {g : (b : β) → Q b → (c : γ) → n (Subtype (Pl b c))}
    (wf : MeasurableSpaceIteratorLoop.WellFounded α m Pl)
    (hfg : ∀ b c (hPb : P b) (hQb : Q b), f b hPb c = g b hQb c) :
    mForIn' lift γ Pl it init P hP f =
      mForIn' lift γ Pl it init Q hQ g := by
  rw [mForIn'_eq_match_step Pl wf, mForIn'_eq_match_step Pl wf]
  congr; ext step
  split
  · congr 1
    · apply hfg
    · funext forInStep
      match forInStep with
      | ⟨.yield _, _⟩ => apply mForIn'_eq_mForIn' Pl wf hfg
      | ⟨.done _, _⟩ => rfl
  · apply mForIn'_eq_mForIn' Pl wf hfg
  · rfl
termination_by MeasurableSpaceIteratorLoop.WithWF.mk it init (hwf := wf)
decreasing_by
  · exact Or.inl ⟨_, ‹_›, ‹_›⟩
  · exact Or.inr ⟨‹_›, rfl⟩

-- Core states the corresponding equation for `Std.IterM`'s `ForIn'` instance. This version
-- exposes the general consumer, retaining its body-step predicate and proof-carrying results.
-- It is also needed for accumulator-dependent termination (including an infinite productive
-- iterator whose body always stops), where the ordinary finite-iterator equation is inapplicable.
#check Std.IterM.forIn'_eq_match_step

/-- Unfold a lawful loop consumer by one producer step. -/
theorem MeasurableSpaceIteratorLoop.mForIn_eq_match_step
    {α β : Type w} {m : (γ : Type w) → [MeasurableSpace γ] → Type w'} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad m]
    [MeasurableSpaceMonad n]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]
    [∀ δ, [MeasurableSpace δ] → MeasurableSpace (n δ)]
    [MeasurableSpaceIteratorLoop α m n] [LawfulMeasurableSpaceIteratorLoop α m n]
    (lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ)
    [LawfulMeasurableSpaceMonadLiftBindFunction lift]
    {γ : Type x} [MeasurableSpace γ] (it : IterM (α := α) m β) (init : γ)
    (Pl : β → γ → ForInStep γ → Prop) (wf : MeasurableSpaceIteratorLoop.WellFounded α m Pl)
    (f : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    MeasurableSpaceIteratorLoop.mForIn lift γ Pl it init f =
      (lift _ _ · it.step) (fun s =>
        match s.inflate with
        | .yield it' out h => rdo
          match ← f out (.direct ⟨_, h⟩) init with
          | ⟨.yield c, _⟩ =>
            MeasurableSpaceIteratorLoop.mForIn lift γ Pl it' c
              (fun out h' acc => f out (.indirect ⟨_, rfl, h⟩ h') acc)
          | ⟨.done c, _⟩ => return c
        | .skip it' h => MeasurableSpaceIteratorLoop.mForIn lift γ Pl it' init
            (fun out h' acc => f out (.indirect ⟨_, rfl, h⟩ h') acc)
        | .done _ => mPure init) := by
  rw [LawfulMeasurableSpaceIteratorLoop.lawful (lift := lift) γ it init Pl wf]
  simp only [MeasurableSpaceIteratorLoop.mForIn]
  rw [IterM.DefaultConsumers.mForIn'_eq_match_step Pl wf]
  congr 1; funext s
  cases s.inflate using Std.PlausibleIterStep.casesOn
  · apply MeasurableSpaceBind.bind_congr
    intro step
    match step with
    | ⟨.yield _, _⟩ =>
      simp only
      rw [LawfulMeasurableSpaceIteratorLoop.lawful (lift := lift) γ _ _ Pl wf]
      exact IterM.DefaultConsumers.mForIn'_eq_mForIn' Pl wf (by intros; rfl)
    | ⟨.done _, _⟩ => rfl
  · simp only
    rw [LawfulMeasurableSpaceIteratorLoop.lawful (lift := lift) γ _ _ Pl wf]
    exact IterM.DefaultConsumers.mForIn'_eq_mForIn' Pl wf (by intros; rfl)
  · rfl

end MeasureTheory
