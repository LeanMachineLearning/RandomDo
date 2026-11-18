/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.Basic
public import RandomDo.MeasurableSpaceMonad.Instances.Id

/-!
# Core iterator producers in measurable space monads

An ordinary producer is interpreted in `Monad.toMeasurableSpaceMonad m`. The conversions keep
its internal state and transport its step and plausibility proofs. Finiteness, productivity, and
determinism are inherited from core. This is the boundary at which an ordinary producer is
converted; the measurable producer and loop APIs themselves use measurable monads throughout.
The conversion maps the producer's result to transport its step, so it requires `Functor m`.
-/

@[expose] public section

namespace MeasureTheory

open Std

universe w w'

-- Core has conversions between pure and monadic iterators. These conversions instead change
-- the producer's constructor from an ordinary monad to its measurable interpretation.
/-- Interpret an ordinary iterator as a producer in a measurable space monad. -/
@[always_inline, inline]
def _root_.Std.IterM.toMeasurable {α β : Type w} {m : Type w → Type w'}
    (it : Std.IterM (α := α) m β) : IterM (α := α) (Monad.toMeasurableSpaceMonad m) β :=
  ⟨it.internalState⟩

/-- Recover the ordinary iterator underlying a converted producer. -/
@[always_inline, inline]
def IterM.toCore {α β : Type w} {m : Type w → Type w'}
    (it : IterM (α := α) (Monad.toMeasurableSpaceMonad m) β) : Std.IterM (α := α) m β :=
  ⟨it.internalState⟩

@[fun_prop] theorem _root_.Std.IterM.measurable_toMeasurable {α β : Type w}
    {m : Type w → Type w'} [MeasurableSpace α] :
    Measurable (Std.IterM.toMeasurable (α := α) (m := m) (β := β)) :=
  measurable_comap_iff.mpr Std.IterM.measurable_internalState

@[fun_prop] theorem IterM.measurable_toCore {α β : Type w}
    {m : Type w → Type w'} [MeasurableSpace α] :
    Measurable (IterM.toCore (α := α) (m := m) (β := β)) :=
  measurable_comap_iff.mpr IterM.measurable_internalState

@[simp] theorem IterM.toMeasurable_toCore {α β : Type w} {m : Type w → Type w'}
    (it : IterM (α := α) (Monad.toMeasurableSpaceMonad m) β) :
    it.toCore.toMeasurable = it := rfl

@[simp] theorem _root_.Std.IterM.toCore_toMeasurable {α β : Type w} {m : Type w → Type w'}
    (it : Std.IterM (α := α) m β) : it.toMeasurable.toCore = it := rfl

@[simp] theorem IterM.toMeasurable_comp_toCore {α β : Type w} {m : Type w → Type w'} :
    Std.IterM.toMeasurable ∘ (IterM.toCore (α := α) (m := m) (β := β)) = id := rfl

@[simp] theorem _root_.Std.IterM.toCore_comp_toMeasurable
    {α β : Type w} {m : Type w → Type w'} :
    IterM.toCore ∘ (Std.IterM.toMeasurable (α := α) (m := m) (β := β)) = id := rfl

/-- Interpret a pure core iterator as a measurable producer. -/
@[always_inline, inline]
def _root_.Std.Iter.toMeasurable {α β : Type w} (it : Std.Iter (α := α) β) :
    IterM (α := α) MId β := it.toIterM.toMeasurable

/-- Transport a core step to the measurable iterator representation. -/
@[always_inline, inline]
def _root_.Std.IterM.Step.toMeasurable {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] {it : Std.IterM (α := α) m β} (s : it.Step) :
    {s : IterStep (IterM (α := α) (Monad.toMeasurableSpaceMonad m) β) β //
      it.IsPlausibleStep (s.mapIterator IterM.toCore)} :=
  ⟨s.val.mapIterator Std.IterM.toMeasurable, by simpa using s.property⟩

-- No core counterpart is needed there: its producers already use ordinary monads.
@[always_inline, inline]
instance instMeasurableSpaceIteratorOfIterator {α β : Type w} {m : Type w → Type w'}
    [Functor m] [Iterator α m β] [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableSpaceIterator α (Monad.toMeasurableSpaceMonad m) β where
  IsPlausibleStep it s := it.toCore.IsPlausibleStep (s.mapIterator IterM.toCore)
  step it := (fun s => Shrink.deflate s.inflate.toMeasurable) <$> it.toCore.step

/-- A converted producer transports the result of the original producer's step. -/
theorem _root_.Std.IterM.step_toMeasurable {α β : Type w} {m : Type w → Type w'}
    [Functor m] [Iterator α m β] [MeasurableSpace α] [MeasurableSpace β]
    (it : Std.IterM (α := α) m β) :
    it.toMeasurable.step = (fun s => Shrink.deflate s.inflate.toMeasurable) <$> it.step := rfl

/-- The converted pure producer takes exactly the same step as the core producer. -/
theorem IterM.step_id {α β : Type w} [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β]
    (it : IterM (α := α) MId β) :
    it.step = (pure (Shrink.deflate it.toCore.step.run.inflate.toMeasurable) :
      Id (Shrink it.Step)) := rfl

/-- Transport the proof-carrying step of a converted pure iterator. -/
theorem IterM.inflate_step_id {α β : Type w} [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β]
    (it : IterM (α := α) MId β) :
    it.step.run.inflate = it.toCore.step.run.inflate.toMeasurable := by
  rw [IterM.step_id, Id.run_pure, Shrink.inflate_deflate]

@[simp] theorem _root_.Std.IterM.inflate_step_toMeasurable {α β : Type w}
    [Iterator α Id β] [MeasurableSpace α] [MeasurableSpace β]
    (it : Std.IterM (α := α) Id β) :
    it.toMeasurable.step.run.inflate = it.step.run.inflate.toMeasurable := by
  rw [IterM.step_id, Id.run_pure, Shrink.inflate_deflate]
  rfl

@[simp] theorem IterM.isPlausibleSuccessorOf_toCore {α β : Type w} {m : Type w → Type w'}
    [Functor m] [Iterator α m β] [MeasurableSpace α] [MeasurableSpace β]
    {it it' : IterM (α := α) (Monad.toMeasurableSpaceMonad m) β} :
    it'.IsPlausibleSuccessorOf it ↔ it'.toCore.IsPlausibleSuccessorOf it.toCore := by
  constructor
  · rintro ⟨s, hs, hp⟩
    refine ⟨s.mapIterator IterM.toCore, ?_, hp⟩
    cases s <;> simp_all [IterStep.successor, IterStep.mapIterator]
  · rintro ⟨s, hs, hp⟩
    refine ⟨s.mapIterator Std.IterM.toMeasurable, ?_, ?_⟩
    · cases s <;> simp_all [IterStep.successor, IterStep.mapIterator]
    · simpa [IterM.IsPlausibleStep, MeasurableSpaceIterator.IsPlausibleStep] using hp

@[simp] theorem IterM.isPlausibleOutput_toCore {α β : Type w} {m : Type w → Type w'}
    [Functor m] [Iterator α m β] [MeasurableSpace α] [MeasurableSpace β]
    {it : IterM (α := α) (Monad.toMeasurableSpaceMonad m) β} {out : β} :
    it.IsPlausibleOutput out ↔ it.toCore.IsPlausibleOutput out := by
  constructor
  · rintro ⟨it', h⟩
    exact ⟨it'.toCore, h⟩
  · rintro ⟨it', h⟩
    exact ⟨it'.toMeasurable, h⟩

@[simp] theorem IterM.isPlausibleIndirectOutput_toCore {α β : Type w}
    {m : Type w → Type w'} [Functor m] [Iterator α m β]
    [MeasurableSpace α] [MeasurableSpace β]
    {it : IterM (α := α) (Monad.toMeasurableSpaceMonad m) β} {out : β} :
    it.IsPlausibleIndirectOutput out ↔ it.toCore.IsPlausibleIndirectOutput out := by
  constructor
  · intro h
    induction h with
    | direct h => exact .direct (isPlausibleOutput_toCore.mp h)
    | indirect h _ ih => exact .indirect (isPlausibleSuccessorOf_toCore.mp h) ih
  · intro h
    generalize hi : it.toCore = coreIt at h
    induction h generalizing it with
    | direct h => exact .direct (isPlausibleOutput_toCore.mpr (hi ▸ h))
    | @indirect coreIt it' out h h' ih =>
      apply IterM.IsPlausibleIndirectOutput.indirect (it' := it'.toMeasurable)
      · apply isPlausibleSuccessorOf_toCore.mpr
        simpa [hi] using h
      · exact ih rfl

instance instFiniteOfCoreIterator {α β : Type w} {m : Type w → Type w'}
    [Functor m] [Iterator α m β] [MeasurableSpace α] [MeasurableSpace β]
    [Std.Iterators.Finite α m] : Iterators.Finite α (Monad.toMeasurableSpaceMonad m) where
  wf := by
    apply Subrelation.wf (r := InvImage Std.IterM.IsPlausibleSuccessorOf IterM.toCore)
    · intro _ _ h
      exact IterM.isPlausibleSuccessorOf_toCore.mp h
    · exact InvImage.wf _ Std.Iterators.Finite.wf

instance instProductiveOfCoreIterator {α β : Type w} {m : Type w → Type w'}
    [Functor m] [Iterator α m β] [MeasurableSpace α] [MeasurableSpace β]
    [Std.Iterators.Productive α m] : Iterators.Productive α (Monad.toMeasurableSpaceMonad m) where
  wf := by
    exact InvImage.wf IterM.toCore Std.Iterators.Productive.wf

instance instLawfulDeterministicMeasurableSpaceIteratorOfCore {α β : Type w}
    {m : Type w → Type w'} [Functor m] [Iterator α m β]
    [MeasurableSpace α] [MeasurableSpace β] [LawfulDeterministicIterator α m] :
    LawfulDeterministicMeasurableSpaceIterator α (Monad.toMeasurableSpaceMonad m) where
  isPlausibleStep_eq_eq it := by
    obtain ⟨s, hs⟩ := LawfulDeterministicIterator.isPlausibleStep_eq_eq (it := it.toCore)
    refine ⟨s.mapIterator Std.IterM.toMeasurable, ?_⟩
    funext t
    apply propext
    simp only [IterM.IsPlausibleStep, MeasurableSpaceIterator.IsPlausibleStep, hs]
    constructor
    · intro h
      simpa using congrArg (IterStep.mapIterator Std.IterM.toMeasurable) h
    · intro h
      simp [h]

end MeasureTheory
