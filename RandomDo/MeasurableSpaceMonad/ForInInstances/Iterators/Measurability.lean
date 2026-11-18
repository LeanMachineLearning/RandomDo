/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Collections
public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Option
public import Init.Data.Iterators.Basic
public import Std.Data.Iterators
public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Slice.Array.Iterator

/-!
# Measurable spaces for core iterators

This file defines measurable space instances for various data structures used to impliment
iterator consumers for measurable space monads. It also proves measurability of some basic
operations on those data structures.

-/

@[expose] public section

namespace Std

universe u v w x

instance Shrink.instMeasurableSpace {α : Type u} [MeasurableSpace α] :
    MeasurableSpace (Shrink α) := MeasurableSpace.comap Shrink.inflate inferInstance

@[fun_prop] theorem Shrink.measurable_inflate {α : Type u} [MeasurableSpace α] :
    Measurable (Shrink.inflate : Shrink α → α) := comap_measurable _

@[fun_prop] theorem Shrink.measurable_deflate {α : Type u} [MeasurableSpace α] :
    Measurable (Shrink.deflate : α → Shrink α) := by
  rintro s ⟨t, ht, rfl⟩
  simpa [Set.preimage_preimage, Function.comp_def] using ht

instance IterM.instMeasurableSpace {α β : Type u} {m : Type u → Type v}
    [MeasurableSpace α] : MeasurableSpace (IterM (α := α) m β) :=
  MeasurableSpace.comap IterM.internalState inferInstance

@[fun_prop] theorem IterM.measurable_internalState {α β : Type u} {m : Type u → Type v}
    [MeasurableSpace α] : Measurable (IterM.internalState (α := α) (m := m) (β := β)) :=
  comap_measurable _

@[fun_prop] theorem IterM.measurable_mk {α β : Type u} {m : Type u → Type v}
    [MeasurableSpace α] : Measurable (IterM.mk : α → IterM (α := α) m β) :=
  measurable_comap_iff.mpr measurable_id

instance Iter.instMeasurableSpace {α β : Type u} [MeasurableSpace α] :
    MeasurableSpace (Iter (α := α) β) := MeasurableSpace.comap Iter.internalState inferInstance

instance IterStep.instMeasurableSpace {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableSpace (IterStep α β) :=
  MeasurableSpace.map (fun p : α × β => .yield p.1 p.2) inferInstance ⊓
    MeasurableSpace.map .skip inferInstance

@[fun_prop] theorem IterStep.measurable_yield {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (fun p : α × β => IterStep.yield p.1 p.2) := fun _ hs => hs.1

@[fun_prop] theorem IterStep.measurable_skip {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] : Measurable (IterStep.skip (β := β) : α → _) :=
  fun _ hs => hs.2

@[fun_prop] theorem IterStep.measurable_fun {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : IterStep α β → γ}
    (hy : Measurable (fun p : α × β => f (.yield p.1 p.2)))
    (hs : Measurable (fun a => f (.skip a))) : Measurable f :=
  fun _ ht => ⟨hy ht, hs ht⟩

namespace Iterators.Types

instance ListIterator.instMeasurableSpace {α : Type u} [MeasurableSpace α] :
    MeasurableSpace (ListIterator α) := MeasurableSpace.comap ListIterator.list inferInstance

instance ArrayIterator.instMeasurableSpace {α : Type u} [MeasurableSpace α] :
    MeasurableSpace (ArrayIterator α) :=
  MeasurableSpace.comap (fun it => (it.array, it.pos)) inferInstance

instance FilterMap.instMeasurableSpace {α β γ : Type u}
    {m : Type u → Type v} {n : Type u → Type w}
    {lift : ⦃δ : Type u⦄ → m δ → n δ} {f : β → PostconditionT n (Option γ)}
    [MeasurableSpace α] : MeasurableSpace (FilterMap α m n lift f) :=
  MeasurableSpace.comap FilterMap.inner inferInstance

instance Map.instMeasurableSpace {α β γ : Type u}
    {m : Type u → Type v} {n : Type u → Type w} [Functor n]
    {lift : ⦃δ : Type u⦄ → m δ → n δ} {f : β → PostconditionT n γ}
    [MeasurableSpace α] : MeasurableSpace (Map α m n lift f) :=
  MeasurableSpace.comap (fun it => it.inner) inferInstance

instance Empty.instMeasurableSpace {m : Type u → Type v} {β : Type u} :
    MeasurableSpace (Empty m β) :=
  MeasurableSpace.comap (fun _ => ()) inferInstance

instance RepeatIterator.instMeasurableSpace {α : Type u} {f : α → α} [MeasurableSpace α] :
    MeasurableSpace (RepeatIterator α f) :=
  MeasurableSpace.comap RepeatIterator.next inferInstance

instance Append.instMeasurableSpace {α₁ α₂ β : Type u} {m : Type u → Type v}
    [MeasurableSpace α₁] [MeasurableSpace α₂] : MeasurableSpace (Append α₁ α₂ m β) :=
  MeasurableSpace.map (fun p : IterM (α := α₁) m β × IterM (α := α₂) m β =>
    Append.fst p.1 p.2) inferInstance ⊓
    MeasurableSpace.map Append.snd inferInstance

instance Attach.instMeasurableSpace {α β : Type u} {m : Type u → Type v}
    [Iterator α m β] {P : β → Prop} [MeasurableSpace α] :
    MeasurableSpace (Attach α m P) := MeasurableSpace.comap Attach.inner inferInstance

instance Flatten.instMeasurableSpace {α α₂ β : Type u} {m : Type u → Type v}
    [MeasurableSpace α] [MeasurableSpace α₂] : MeasurableSpace (Flatten α α₂ β m) :=
  MeasurableSpace.comap (fun it => (it.it₁, it.it₂)) inferInstance

instance Take.instMeasurableSpace {α β : Type u} {m : Type u → Type v}
    [Iterator α m β] [MeasurableSpace α] : MeasurableSpace (Take α m) :=
  MeasurableSpace.comap (fun it => (it.countdown, it.inner)) inferInstance

instance ULiftIterator.instMeasurableSpace {α β : Type u} {m : Type u → Type v}
    {n : Type (max u w) → Type x} {lift : ⦃γ : Type u⦄ → m γ → Std.Iterators.ULiftT n γ}
    [MeasurableSpace α] : MeasurableSpace (ULiftIterator α m n β lift) :=
  MeasurableSpace.comap ULiftIterator.inner inferInstance

instance Drop.instMeasurableSpace {α β : Type u} {m : Type u → Type v}
    [MeasurableSpace α] : MeasurableSpace (Drop α m β) :=
  MeasurableSpace.comap (fun it => (it.remaining, it.inner)) inferInstance

instance DropWhile.instMeasurableSpace {α β : Type u} {m : Type u → Type v}
    {P : β → PostconditionT m (ULift Bool)} [MeasurableSpace α] :
    MeasurableSpace (DropWhile α m β P) :=
  MeasurableSpace.comap (fun it => (it.dropping, it.inner)) inferInstance

instance TakeWhile.instMeasurableSpace {α β : Type u} {m : Type u → Type v}
    {P : β → PostconditionT m (ULift Bool)} [MeasurableSpace α] :
    MeasurableSpace (TakeWhile α m β P) := MeasurableSpace.comap TakeWhile.inner inferInstance

instance StepSizeIterator.instMeasurableSpace {α β : Type u} {m : Type u → Type v}
    [MeasurableSpace α] : MeasurableSpace (StepSizeIterator α m β) :=
  MeasurableSpace.comap (fun it => (it.nextIdx, it.n, it.inner)) inferInstance

instance Zip.instMeasurableSpace {α₁ β₁ α₂ β₂ : Type u} {m : Type u → Type v}
    [Iterator α₁ m β₁] [MeasurableSpace α₁] [MeasurableSpace β₁] [MeasurableSpace α₂] :
    MeasurableSpace (Zip α₁ m α₂ β₂) :=
  MeasurableSpace.comap (fun it => (it.left, it.memoizedLeft, it.right)) inferInstance

end Iterators.Types

instance Rxc.Iterator.instMeasurableSpace {α : Type u} [MeasurableSpace α] :
    MeasurableSpace (Rxc.Iterator α) :=
  MeasurableSpace.comap (fun it => (it.next, it.upperBound)) inferInstance

instance Rxo.Iterator.instMeasurableSpace {α : Type u} [MeasurableSpace α] :
    MeasurableSpace (Rxo.Iterator α) :=
  MeasurableSpace.comap (fun it => (it.next, it.upperBound)) inferInstance

instance Rxi.Iterator.instMeasurableSpace {α : Type u} [MeasurableSpace α] :
    MeasurableSpace (Rxi.Iterator α) := MeasurableSpace.comap Rxi.Iterator.next inferInstance

end Std

instance SubarrayIterator.instMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (SubarrayIterator α) :=
  MeasurableSpace.comap SubarrayIterator.xs inferInstance
