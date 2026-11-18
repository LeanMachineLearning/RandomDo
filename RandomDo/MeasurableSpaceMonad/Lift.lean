/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.Instances.Id
import Init.Data.Iterators.Internal.LawfulMonadLiftFunction

/-!
# Lifting between measurable space monads

This file defines classes `MeasurableSpaceMonadLift` and `MeasurableSpaceMonadLiftT` for lifting
computations from one measurable space monad to another. They play the role of Lean core's
`MonadLift` and `MonadLiftT`.

Users should specify new liftings from one measurable space monad to another by defining an
instance of `MeasurableSpaceMonadLift`, but `MeasurableSpaceMonadLiftT` (which is the reflexive,
transitive closure of `MeasurableSpaceMonadLift`) should be the instance used in a computation
when lifting from one measurable space monad to another.

It also defines classes `Internal.LawfulMeasurableSpaceMonadLiftBindFunction` and
`Internal.LawfulMeasurableSpaceMonadLiftFunction` which are measurable space monad
analogues of `Std.Internal.LawfulMonadLiftBindFunction` and `Std.Internal.LawfulMonadLiftFunction`
respectively. These describe explicitly supplied lifting functions, using the measurable spaces
on their source and target types. Their bind laws require measurable functions, just as the laws
of `LawfulMeasurableSpaceMonad` do.

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
    MeasurableSpaceMonadLiftT MId m where
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

instance {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] [LawfulMeasurableSpaceMonad m] :
    LawfulMeasurableSpaceMonadLiftT MId m where
  measurable_mMonadLift {_} _ := LawfulMeasurableSpaceMonad.measurable_mPure
  mMonadLift_mPure _ := rfl
  mMonadLift_mBind a _ hf :=
    (LawfulMeasurableSpaceMonad.mPure_mBind a.run
      (LawfulMeasurableSpaceMonad.measurable_mPure.comp hf)).symm

end Lawful

namespace Internal

universe w' w'' x x'

/-- Asserts that `liftBind` takes measurable functions to measurable functions and satisfies
the `mPure` and `mBind` laws for measurable functions. -/
class LawfulMeasurableSpaceMonadLiftBindFunction
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (δ : Type x) → [MeasurableSpace δ] → Type x'}
    [MeasurableSpaceMonad m] [MeasurableSpaceMonad n]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]
    [∀ δ, [MeasurableSpace δ] → MeasurableSpace (n δ)]
    (liftBind : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → m γ → n δ) where
  /-- `liftBind` of a measurable function is a measurable function. -/
  measurable_liftBind {γ δ} [MeasurableSpace γ] [MeasurableSpace δ]
      (f : γ → n δ) (hf : Measurable f) : Measurable (liftBind γ δ f)
  /-- Lifting and binding `mPure a` to a measurable function `f` is equivalent to applying
  `f` to `a`. -/
  liftBind_mPure {γ δ} [MeasurableSpace γ] [MeasurableSpace δ]
      (f : γ → n δ) (a : γ) (hf : Measurable f) : liftBind γ δ f (mPure a) = f a
  /-- `liftBind` is associative with `mBind` on measurable functions. -/
  liftBind_mBind {β γ δ} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
      (f : γ → n δ) (x : m β) (g : β → m γ) (hf : Measurable f) (hg : Measurable g) :
    liftBind γ δ f (x >>=ₘ g) = liftBind β δ (fun b => liftBind γ δ f (g b)) x

/-- Asserts that the lifting function `lift` is measurable and preserves `mPure` and `mBind`
of measurable functions. -/
class LawfulMeasurableSpaceMonadLiftFunction
    {m : (α : Type u) → [MeasurableSpace α] → Type v}
    {n : (α : Type u) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] [MeasurableSpaceMonad n]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
    (lift : ⦃α : Type u⦄ → [MeasurableSpace α] → m α → n α) where
  /-- `lift` is a measurable function. -/
  measurable_lift {α : Type u} [MeasurableSpace α] : Measurable (lift (α := α) : m α → n α)
  /-- Lifting preserves `mPure`. -/
  lift_mPure {α : Type u} [MeasurableSpace α] (a : α) : lift (mPure a) = mPure a
  /-- Lifting preserves `mBind` of measurable functions. -/
  lift_mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      (ma : m α) (f : α → m β) (hf : Measurable f) :
    lift (ma >>=ₘ f) = lift ma >>=ₘ (fun a => lift (f a))


instance {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] :
    LawfulMeasurableSpaceMonadLiftFunction (fun ⦃α⦄ _ => (id : m α → m α)) where
  measurable_lift := by fun_prop
  lift_mPure := by simp
  lift_mBind := by simp

instance {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {n : (α : Type u) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad n]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
    [MeasurableSpaceMonadLiftT m n] [LawfulMeasurableSpaceMonadLiftT m n] :
    LawfulMeasurableSpaceMonadLiftFunction
      (fun ⦃α⦄ _ => (mMonadLift : m α → n α)) where
  measurable_lift := by fun_prop
  lift_mPure := mMonadLift_mPure
  lift_mBind := mMonadLift_mBind

variable {m : (α : Type u) → [MeasurableSpace α] → Type v}
  {n : (α : Type u) → [MeasurableSpace α] → Type w}
  [MeasurableSpaceMonad m] [MeasurableSpaceMonad n]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
  {lift : ⦃α : Type u⦄ → [MeasurableSpace α] → m α → n α}

theorem LawfulMeasurableSpaceMonadLiftFunction.lift_mMap
    [LawfulMeasurableSpaceMonad m] [LawfulMeasurableSpaceMonad n]
    [LawfulMeasurableSpaceMonadLiftFunction lift]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (ma : m α) (hf : Measurable f) :
    lift (f <$>ₘ ma) = f <$>ₘ (lift ma : n α) := by
  rw [← mBind_mPure_comp hf, ← mBind_mPure_comp hf, lift_mBind (lift := lift) _ _ (by fun_prop)]
  simp [lift_mPure]

/-- Lift an identity computation using `mPure`. -/
abbrev idToMonad ⦃α : Type u⦄ [MeasurableSpace α] (x : Id α) : m α :=
  mPure x.run

theorem LawfulMeasurableSpaceMonadLiftFunction.idToMonad [LawfulMeasurableSpaceMonad m] :
    LawfulMeasurableSpaceMonadLiftFunction (m := MId) (n := m)
      idToMonad where
  measurable_lift := by fun_prop
  lift_mPure := by simp [Internal.idToMonad, mPure]
  lift_mBind := by
    intro α β _ _ ma f hf
    exact (mPure_mBind ma.run (measurable_mPure.comp hf)).symm

instance [LawfulMeasurableSpaceMonadLiftFunction lift] :
    letI : MeasurableSpaceMonadLift m n := ⟨lift (α := _)⟩
    LawfulMeasurableSpaceMonadLift m n :=
  letI : MeasurableSpaceMonadLift m n := ⟨lift (α := _)⟩
  { measurable_mMonadLift {_} _ := LawfulMeasurableSpaceMonadLiftFunction.measurable_lift
    mMonadLift_mPure := LawfulMeasurableSpaceMonadLiftFunction.lift_mPure
    mMonadLift_mBind := LawfulMeasurableSpaceMonadLiftFunction.lift_mBind }

section LiftBind

theorem LawfulMeasurableSpaceMonadLiftBindFunction.id
    {m : (α : Type w) → [MeasurableSpace α] → Type x} [MeasurableSpaceMonad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] :
    LawfulMeasurableSpaceMonadLiftBindFunction (m := MId) (n := m)
      (fun _ _ _ _ f x => f x.run) where
  measurable_liftBind _ hf := hf
  liftBind_mPure _ _ _ := rfl
  liftBind_mBind _ _ _ _ _ := rfl

instance {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    [MeasurableSpaceMonad m] [MeasurableSpaceMonad n]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (n γ)]
    [MeasurableSpaceMonadLiftT m n] [LawfulMeasurableSpaceMonadLiftT m n]
    [LawfulMeasurableSpaceMonad n] :
    LawfulMeasurableSpaceMonadLiftBindFunction (m := m) (n := n)
      (fun _ _ _ _ f x => mMonadLift x >>=ₘ f) where
  measurable_liftBind _ hf := (measurable_mBind hf).comp measurable_mMonadLift
  liftBind_mPure f a hf := by rw [mMonadLift_mPure, mPure_mBind _ hf]
  liftBind_mBind f x g hf hg := by
    rw [mMonadLift_mBind _ _ hg]
    exact mBind_assoc _ (measurable_mMonadLift.comp hg) hf

instance {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (n γ)] :
    LawfulMeasurableSpaceMonadLiftBindFunction (m := MId) (n := n)
      (fun _ _ _ _ f x => f x.run) := .id

instance {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] [LawfulMeasurableSpaceMonad m] :
    LawfulMeasurableSpaceMonadLiftBindFunction (m := m) (n := m)
      (fun _ _ _ _ f x => x >>=ₘ f) where
  measurable_liftBind _ hf := measurable_mBind hf
  liftBind_mPure _ _ hf := mPure_mBind _ hf
  liftBind_mBind _ _ _ hf hg := mBind_assoc _ hg hf

end LiftBind

end Internal

end MeasureTheory
