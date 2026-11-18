/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.CoreLoop
public import Std.Data.Iterators
public import Std.Data.DHashMap.Iterator
public import Std.Data.DTreeMap.Iterator
public import Std.Data.DTreeMap.Slice
public import Init.Data.String.Slice
public import Init.Data.String.Iterate
public import Init.Data.Slice.Array.Iterator

/-!
# Measurable loop instances for standard iterators

These instances follow the explicit `IteratorLoop` instances of Lean's standard producers and
combinators. Each opts into `MeasurableSpaceIteratorLoop.defaultImplementation`; there is no
fallback for an arbitrary `Iterator`. A custom producer must choose its loop implementation,
just as in core. The specialized range implementations are in `ForInInstances.Ranges`.

Core producer instances are reused through the conversions in `Iterators.Core`.
The state and output spaces are supplied by the caller.
The instances retain core's producer prerequisites and inlining attributes, and additionally
require measurable spaces on the state and output. They are grouped
by their core source modules: producers, combinators, then collection iterators. Core's internal
string searchers run in `Id` and are used unchanged by the public string iterators.
-/

@[expose] public section

namespace MeasureTheory

open Std Std.Iterators Std.Iterators.Types

universe u u' v v' w w' w'' x x'

#check Std.Iterators.Types.ListIterator.instIteratorLoop

@[always_inline, inline]
instance Iterators.Types.ListIterator.instMeasurableSpaceIteratorLoop
    {m : Type w → Type w'} {α : Type w} [Monad m]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    [MeasurableSpace (ListIterator α)] [MeasurableSpace α] :
    MeasurableSpaceIteratorLoop (ListIterator α) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.ArrayIterator.instIteratorLoop

@[always_inline, inline]
instance Iterators.Types.ArrayIterator.instMeasurableSpaceIteratorLoop
    {m : Type w → Type w'} {α : Type w} [Monad m]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    [MeasurableSpace (ArrayIterator α)] [MeasurableSpace α] :
    MeasurableSpaceIteratorLoop (ArrayIterator α) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.Empty.instIteratorLoop

instance Iterators.Types.Empty.instMeasurableSpaceIteratorLoop
    {m : Type w → Type w'} {β : Type w}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [Monad m] [MeasurableSpaceMonad n]
    [MeasurableSpace (Std.Iterators.Types.Empty m β)] [MeasurableSpace β] :
    MeasurableSpaceIteratorLoop (Std.Iterators.Types.Empty m β)
    (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.RepeatIterator.instIteratorLoop

instance Iterators.Types.RepeatIterator.instMeasurableSpaceIteratorLoop
    {α : Type w} {f : α → α}
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w'} [MeasurableSpaceMonad n]
    [MeasurableSpace (RepeatIterator α f)] [MeasurableSpace α] :
    MeasurableSpaceIteratorLoop (RepeatIterator α f) MId n :=
  .defaultImplementation

#check Std.Iterators.Types.Append.instIteratorLoop

instance Iterators.Types.Append.instMeasurableSpaceIteratorLoop
    {m : Type w → Type w'} {β α₁ α₂ : Type w}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [Monad m] [MeasurableSpaceMonad n]
    [Iterator α₁ m β] [Iterator α₂ m β]
    [MeasurableSpace (Std.Iterators.Types.Append α₁ α₂ m β)] [MeasurableSpace β] :
    MeasurableSpaceIteratorLoop (Std.Iterators.Types.Append α₁ α₂ m β)
    (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.Attach.instIteratorLoop

instance Iterators.Types.Attach.instMeasurableSpaceIteratorLoop
    {α β : Type w} {m : Type w → Type w'} [Monad m]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    {P : β → Prop} [Iterator α m β]
    [MeasurableSpace (Attach α m P)] [MeasurableSpace ({b : β // P b})] :
    MeasurableSpaceIteratorLoop (Attach α m P) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.FilterMap.instIteratorLoop

instance Iterators.Types.FilterMap.instMeasurableSpaceIteratorLoop
    {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    {o : (δ : Type x) → [MeasurableSpace δ] → Type x'} [Monad n] [MeasurableSpaceMonad o]
    [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n (Option γ)}
    [MeasurableSpace (FilterMap α m n lift f)] [MeasurableSpace γ] :
    MeasurableSpaceIteratorLoop (FilterMap α m n lift f) (Monad.toMeasurableSpaceMonad n) o :=
  .defaultImplementation

#check Std.Iterators.Types.Map.instIteratorLoop

instance Iterators.Types.Map.instMeasurableSpaceIteratorLoop
    {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    {o : (δ : Type x) → [MeasurableSpace δ] → Type x'} [Monad n] [MeasurableSpaceMonad o]
    [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n γ}
    [MeasurableSpace (Map α m n lift f)] [MeasurableSpace γ] :
    MeasurableSpaceIteratorLoop (Map α m n lift f) (Monad.toMeasurableSpaceMonad n) o :=
  .defaultImplementation

#check Std.Iterators.Types.Flatten.instIteratorLoop

instance Iterators.Types.Flatten.instMeasurableSpaceIteratorLoop
    {α α₂ β : Type w} {m : Type w → Type w'}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [Monad m] [MeasurableSpaceMonad n]
    [Iterator α m (Std.IterM (α := α₂) m β)] [Iterator α₂ m β]
    [MeasurableSpace (Flatten α α₂ β m)] [MeasurableSpace β] :
    MeasurableSpaceIteratorLoop (Flatten α α₂ β m) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.Take.instIteratorLoop

instance Iterators.Types.Take.instMeasurableSpaceIteratorLoop
    {α : Type w} {m : Type w → Type w'} {β : Type w}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [Monad m] [MeasurableSpaceMonad n]
    [Iterator α m β]
    [MeasurableSpace (Take α m)] [MeasurableSpace β] :
    MeasurableSpaceIteratorLoop (Take α m) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.ULiftIterator.instIteratorLoop

instance Iterators.Types.ULiftIterator.instMeasurableSpaceIteratorLoop
    {α : Type u} {m : Type u → Type u'} {n : Type (max u v) → Type v'} {β : Type u}
    {lift : ⦃γ : Type u⦄ → m γ → Std.Iterators.ULiftT n γ}
    {o : (γ : Type x) → [MeasurableSpace γ] → Type x'} [Monad n] [MeasurableSpaceMonad o]
    [Iterator α m β]
    [MeasurableSpace (ULiftIterator α m n β lift)] [MeasurableSpace (ULift.{v} β)] :
    MeasurableSpaceIteratorLoop (ULiftIterator α m n β lift) (Monad.toMeasurableSpaceMonad n) o :=
  .defaultImplementation

#check Std.Iterators.Types.Drop.instIteratorLoop

instance Iterators.Types.Drop.instMeasurableSpaceIteratorLoop
    {α : Type w} {m : Type w → Type w'} {β : Type w}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [Monad m] [MeasurableSpaceMonad n]
    [Iterator α m β]
    [MeasurableSpace (Drop α m β)] [MeasurableSpace β] :
    MeasurableSpaceIteratorLoop (Drop α m β) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.DropWhile.instIteratorLoop

instance Iterators.Types.DropWhile.instMeasurableSpaceIteratorLoop
    {α : Type w} {m : Type w → Type w'} {β : Type w}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} {P : β → PostconditionT m (ULift Bool)}
    [Monad m] [MeasurableSpaceMonad n] [Iterator α m β]
    [MeasurableSpace (DropWhile α m β P)] [MeasurableSpace β] :
    MeasurableSpaceIteratorLoop (DropWhile α m β P) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.TakeWhile.instIteratorLoop

-- Retain core's prerequisite even though its current default implementation does not use it.
@[nolint unusedArguments]
instance Iterators.Types.TakeWhile.instMeasurableSpaceIteratorLoop
    {α : Type w} {m : Type w → Type w'} {β : Type w}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} {P : β → PostconditionT m (ULift Bool)}
    [Monad m] [MeasurableSpaceMonad n] [Iterator α m β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α (Monad.toMeasurableSpaceMonad m) n]
    [MeasurableSpace (TakeWhile α m β P)] :
    MeasurableSpaceIteratorLoop (TakeWhile α m β P) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.StepSizeIterator.instIteratorLoop

instance Iterators.Types.StepSizeIterator.instMeasurableSpaceIteratorLoop
    {α β : Type u} {m : Type u → Type v}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [Iterator α m β]
    [IteratorAccess α m] [Monad m] [MeasurableSpaceMonad n]
    [MeasurableSpace (StepSizeIterator α m β)] [MeasurableSpace β] :
    MeasurableSpaceIteratorLoop (StepSizeIterator α m β) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.Iterators.Types.Zip.instIteratorLoop

instance Iterators.Types.Zip.instMeasurableSpaceIteratorLoop
    {m : Type w → Type w'} {α₁ β₁ : Type w} [Iterator α₁ m β₁]
    {α₂ β₂ : Type w} [Iterator α₂ m β₂]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [Monad m] [MeasurableSpaceMonad n]
    [MeasurableSpace (Zip α₁ m α₂ β₂)] [MeasurableSpace (β₁ × β₂)] :
    MeasurableSpaceIteratorLoop (Zip α₁ m α₂ β₂) (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check instIteratorLoopSubarrayIteratorIdOfMonad

instance {α : Type u} {m : (γ : Type x) → [MeasurableSpace γ] → Type x'}
    [MeasurableSpaceMonad m]
    [MeasurableSpace (SubarrayIterator α)] [MeasurableSpace α] :
    MeasurableSpaceIteratorLoop (SubarrayIterator α) MId m :=
  .defaultImplementation

#check String.Slice.PosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad

instance {m : Type → Type u} {n : (γ : Type x) → [MeasurableSpace γ] → Type x'}
    {s : String.Slice} [Monad m] [MeasurableSpaceMonad n]
    [MeasurableSpace s.PosIterator] [MeasurableSpace ({p : s.Pos // p ≠ s.endPos})] :
    MeasurableSpaceIteratorLoop s.PosIterator (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check String.Slice.RevPosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad

instance {m : Type → Type u} {n : (γ : Type x) → [MeasurableSpace γ] → Type x'}
    {s : String.Slice} [Monad m] [MeasurableSpaceMonad n]
    [MeasurableSpace s.RevPosIterator] [MeasurableSpace ({p : s.Pos // p ≠ s.endPos})] :
    MeasurableSpaceIteratorLoop s.RevPosIterator (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check String.Slice.ByteIterator.instIteratorLoopUInt8OfMonad

instance {m : Type → Type u} {n : (γ : Type x) → [MeasurableSpace γ] → Type x'}
    [Monad m] [MeasurableSpaceMonad n]
    [MeasurableSpace String.Slice.ByteIterator] [MeasurableSpace UInt8] :
    MeasurableSpaceIteratorLoop String.Slice.ByteIterator (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check String.Slice.RevByteIterator.instIteratorLoopUInt8OfMonad

instance {m : Type → Type u} {n : (γ : Type x) → [MeasurableSpace γ] → Type x'}
    [Monad m] [MeasurableSpaceMonad n]
    [MeasurableSpace String.Slice.RevByteIterator] [MeasurableSpace UInt8] :
    MeasurableSpaceIteratorLoop String.Slice.RevByteIterator (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check String.Slice.SplitIterator.instIteratorLoopIdSubsliceOfMonad

instance {ρ : Type} {σ : String.Slice → Type}
    [∀ s, Iterator (σ s) Id (String.Slice.Pattern.SearchStep s)]
    {pat : ρ} [String.Slice.Pattern.ToForwardSearcher pat σ]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} {s : String.Slice}
    [MeasurableSpaceMonad n]
    [MeasurableSpace (String.Slice.SplitIterator pat s)] [MeasurableSpace s.Subslice] :
    MeasurableSpaceIteratorLoop (String.Slice.SplitIterator pat s) MId n :=
  .defaultImplementation

#check String.Slice.SplitInclusiveIterator.instIteratorLoopIdOfMonad

instance {ρ : Type} {σ : String.Slice → Type}
    [∀ s, Iterator (σ s) Id (String.Slice.Pattern.SearchStep s)]
    {pat : ρ} [String.Slice.Pattern.ToForwardSearcher pat σ]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    {s : String.Slice}
    [MeasurableSpace (String.Slice.SplitInclusiveIterator pat s)] [MeasurableSpace String.Slice] :
    MeasurableSpaceIteratorLoop (String.Slice.SplitInclusiveIterator pat s) MId n :=
  .defaultImplementation

#check String.Slice.RevSplitIterator.instIteratorLoopOfMonad

instance {ρ : Type} {pat : ρ} {σ : String.Slice → Type}
    [∀ s, Iterator (σ s) Id (String.Slice.Pattern.SearchStep s)]
    [String.Slice.Pattern.ToBackwardSearcher pat σ]
    {m : Type → Type u} {n : (γ : Type x) → [MeasurableSpace γ] → Type x'}
    {s : String.Slice} [Monad m] [MeasurableSpaceMonad n]
    [MeasurableSpace (String.Slice.RevSplitIterator pat s)] [MeasurableSpace String.Slice] :
    MeasurableSpaceIteratorLoop (String.Slice.RevSplitIterator pat s)
    (Monad.toMeasurableSpaceMonad m) n :=
  .defaultImplementation

#check Std.DHashMap.Internal.AssocList.instIteratorLoopAssocListIteratorIdSigmaOfMonad

instance {α : Type u} {β : α → Type v}
    {m : (γ : Type (max u v)) → [MeasurableSpace γ] → Type w''} [MeasurableSpaceMonad m]
    [MeasurableSpace (Std.DHashMap.Internal.AssocList.AssocListIterator α β)] [MeasurableSpace
    ((a : α) × β a)] :
    MeasurableSpaceIteratorLoop (Std.DHashMap.Internal.AssocList.AssocListIterator α β) MId m :=
  .defaultImplementation

#check Std.DTreeMap.Internal.Zipper.instIteratorLoop

instance DTreeMap.Internal.Zipper.instMeasurableSpaceIteratorLoop {α : Type u} {β : α → Type v}
    {m : (γ : Type (max u v)) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]
    [MeasurableSpace (Std.DTreeMap.Internal.Zipper α β)] [MeasurableSpace ((a : α) × β a)] :
    MeasurableSpaceIteratorLoop (Std.DTreeMap.Internal.Zipper α β) MId m :=
  .defaultImplementation

#check Std.DTreeMap.Internal.RxcIterator.instIteratorLoop

instance DTreeMap.Internal.RxcIterator.instMeasurableSpaceIteratorLoop
    {α : Type u} {β : α → Type v} [Ord α]
    {m : (γ : Type (max u v)) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]
    [MeasurableSpace (Std.DTreeMap.Internal.RxcIterator α β)] [MeasurableSpace ((a : α) × β a)] :
    MeasurableSpaceIteratorLoop (Std.DTreeMap.Internal.RxcIterator α β) MId m :=
  .defaultImplementation

#check Std.DTreeMap.Internal.RxoIterator.instIteratorLoop

instance DTreeMap.Internal.RxoIterator.instMeasurableSpaceIteratorLoop
    {α : Type u} {β : α → Type v} [Ord α]
    {m : (γ : Type (max u v)) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]
    [MeasurableSpace (Std.DTreeMap.Internal.RxoIterator α β)] [MeasurableSpace ((a : α) × β a)] :
    MeasurableSpaceIteratorLoop (Std.DTreeMap.Internal.RxoIterator α β) MId m :=
  .defaultImplementation

end MeasureTheory
