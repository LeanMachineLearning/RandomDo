/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.Defs

/-!
# Lifting between measurable space monads

This file defines classes `MeasurableSpaceMonadLift` and `MeasurableSpaceMonadLiftT` for lifting
computations from one measurable space monad to another. They play the role of Lean core's
`MonadLift` and `MonadLiftT`.

## Main definitions

* `MeasurableSpaceMonadLift`: a lifting operation between two measurable space monads.
* `MeasurableSpaceMonadLiftT`: the reflexive, transitive lifting interface.
* `LawfulMeasurableSpaceMonadLift`: A `Prop`-valued typeclass which asserts that the `mMonadLift`
of a `MeasurableSpaceMonadLift` is measurable and preserves the monad operations.
* `LawfulMeasurableSpaceMonadLiftT`: A `Prop`-valued typeclass which asserts that the `mMonadLift`
of a `MeasurableSpaceMonadLiftT` is measurable and preserves the monad operations.
-/

@[expose] public section

namespace MeasureTheory

universe u v w

/-- Computations in the measurable space monad `m` can be run in the measurable space monad `n`. -/
class MeasurableSpaceMonadLift
    (m : semiOutParam ((α : Type u) → [MeasurableSpace α] → Type v))
    (n : (α : Type u) → [MeasurableSpace α] → Type w) where
  /-- Translates an action from `m` into `n`. -/
  mMonadLift {α : Type u} [MeasurableSpace α] : m α → n α

/-- Computations in the measurable space monad `m` can be run in the measurable monad `n`.
Unlike `do` notation, `rdo` notation can't currently automatically insert these translations.

This is the reflexive, transitive closure of `MeasurableSpaceMonadLift`. Clients that require one
measurable space monad to be liftable into another should request an instance of
`MeasurableSpaceMonadLiftT`. New instances should instead be defined for `MeasurableSpaceMonadLift`
itself. -/
class MeasurableSpaceMonadLiftT
    (m : (α : Type u) → [MeasurableSpace α] → Type v)
    (n : (α : Type u) → [MeasurableSpace α] → Type w) where
  /-- Translates an action from `m` into `n`. -/
  mMonadLift {α : Type u} [MeasurableSpace α] : m α → n α

export MeasurableSpaceMonadLiftT (mMonadLift)

@[inherit_doc mMonadLift]
abbrev mLiftM := @mMonadLift

@[always_inline]
instance (m n o) [MeasurableSpaceMonadLift n o] [MeasurableSpaceMonadLiftT m n] :
    MeasurableSpaceMonadLiftT m o where
  mMonadLift x := MeasurableSpaceMonadLift.mMonadLift (m := n) (mMonadLift x)

@[always_inline]
instance (m) : MeasurableSpaceMonadLiftT m m where
  mMonadLift x := x

-- This instance is set to low priority so that the composition and identity instances
-- are preferred.
instance (priority := low) {m : Type u → Type v} {n : Type u → Type w} [MonadLiftT m n] :
    MeasurableSpaceMonadLiftT (Monad.toMeasurableSpaceMonad m)
      (Monad.toMeasurableSpaceMonad n) where
  mMonadLift := monadLift

instance {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpacePure m] :
    MeasurableSpaceMonadLiftT (Monad.toMeasurableSpaceMonad Id) m where
  mMonadLift x := MeasurableSpacePure.mPure x.run

section Lawful

/-- Asserts that the `mMonadLift` of a `MeasurableSpaceMonadLift` is measurable and preserves
`mPure` and `mBind` of measurable functions. -/
class LawfulMeasurableSpaceMonadLift
    (m : semiOutParam ((α : Type u) → [MeasurableSpace α] → Type v))
    (n : (α : Type u) → [MeasurableSpace α] → Type w)
    [MeasurableSpaceMonad m] [MeasurableSpaceMonad n]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
    [inst : MeasurableSpaceMonadLift m n] : Prop where
  /-- `mMonadLift` is a measurable function. -/
  measurable_mMonadLift {α : Type u} [MeasurableSpace α] :
    Measurable (inst.mMonadLift : m α → n α)
  /-- Lifting preserves `mPure`. -/
  mMonadLift_mPure {α : Type u} [MeasurableSpace α] (a : α) :
    inst.mMonadLift (mPure a) = mPure a
  /-- Lifting preserves `mBind` of measurable functions. -/
  mMonadLift_mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      (ma : m α) (f : α → m β) (hf : Measurable f) :
    inst.mMonadLift (ma >>=ₘ f) = inst.mMonadLift ma >>=ₘ (fun a => inst.mMonadLift (f a))

/-- Asserts that the `mMonadLift` of a `MeasurableSpaceMonadLiftT` is measurable and preserves
`mPure` and `mBind` of measurable functions. -/
class LawfulMeasurableSpaceMonadLiftT
    (m : (α : Type u) → [MeasurableSpace α] → Type v)
    (n : (α : Type u) → [MeasurableSpace α] → Type w)
    [MeasurableSpaceMonad m] [MeasurableSpaceMonad n]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
    [inst : MeasurableSpaceMonadLiftT m n] : Prop where
  /-- Lifting is a measurable function. -/
  measurable_mMonadLift {α : Type u} [MeasurableSpace α] :
    Measurable (mMonadLift : m α → n α)
  /-- Lifting preserves `mPure`. -/
  mMonadLift_mPure {α : Type u} [MeasurableSpace α] (a : α) :
    inst.mMonadLift (mPure a) = mPure a
  /-- Lifting preserves `mBind` of measurable functions. -/
  mMonadLift_mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      (ma : m α) (f : α → m β) (hf : Measurable f) :
    inst.mMonadLift (ma >>=ₘ f) = mMonadLift ma >>=ₘ (fun a => mMonadLift (f a))

export LawfulMeasurableSpaceMonadLiftT (measurable_mMonadLift mMonadLift_mPure mMonadLift_mBind)

attribute [fun_prop] LawfulMeasurableSpaceMonadLift.measurable_mMonadLift measurable_mMonadLift

section

variable {m : (α : Type u) → [MeasurableSpace α] → Type v}
  {n : (α : Type u) → [MeasurableSpace α] → Type w}
  [MeasurableSpaceMonad m] [MeasurableSpaceMonad n]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
  [MeasurableSpaceMonadLiftT m n] [LawfulMeasurableSpaceMonadLiftT m n]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

-- As in core, duplicate the laws for the alias so that `rw` matches either spelling.
@[simp] theorem mLiftM_mPure (a : α) : mLiftM (mPure a : m α) = mPure (f := n) a :=
  mMonadLift_mPure _

@[simp] theorem mLiftM_mBind (ma : m α) (f : α → m β) (hf : Measurable f) :
    mLiftM (n := n) (ma >>=ₘ f) = mLiftM ma >>=ₘ fun a => mLiftM (f a) :=
  mMonadLift_mBind _ _ hf

end

instance (m n o) [MeasurableSpaceMonad m] [MeasurableSpaceMonad n] [MeasurableSpaceMonad o]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (o α)]
    [MeasurableSpaceMonadLift n o] [MeasurableSpaceMonadLiftT m n]
    [LawfulMeasurableSpaceMonadLift n o] [LawfulMeasurableSpaceMonadLiftT m n] :
    LawfulMeasurableSpaceMonadLiftT m o where
  measurable_mMonadLift {_} _ :=
    LawfulMeasurableSpaceMonadLift.measurable_mMonadLift.comp measurable_mMonadLift
  mMonadLift_mPure a := by
    simp [mMonadLift, LawfulMeasurableSpaceMonadLift.mMonadLift_mPure]
  mMonadLift_mBind ma f hf := by
    simp only [mMonadLift, mLiftM_mBind ma f hf]
    exact LawfulMeasurableSpaceMonadLift.mMonadLift_mBind _ _ (by fun_prop)

instance (m) [MeasurableSpaceMonad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] :
    LawfulMeasurableSpaceMonadLiftT m m where
  measurable_mMonadLift {_} _ := measurable_id
  mMonadLift_mPure _ := rfl
  mMonadLift_mBind _ _ _ := rfl

end Lawful

end MeasureTheory
