/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Constructions
public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.StdGen
public import RandomDo.MeasurableSpaceMonad.Lift
public import Mathlib.Control.Random

/-!
# Measurable space monads for pseudorandom sampling

## Main definitions

* `PseudoRandT`: Mathlib's `RandGT` monad transformer, adapted to take a `MeasurableSpace`
argument, with a configurable generator state and base monad.
* `PseudoRand`: The pure specialization of `PseudoRandT`, with base monad `Id`.

When the base monad has a `Monad` instance, `PseudoRandT` inherits a `MeasurableSpaceMonad`
instance through `Monad.toMeasurableSpaceMonad`. This file also equips `PseudoRandT` with a
measurable space on its computations whenever the adapted base monad has measurable spaces on
its output types. It inherits a `LawfulMeasurableSpaceMonad` instance when the adapted base monad
is lawful and the state type is countable with measurable singletons. The pure specialization
`PseudoRand` inherits this instance through `Id`; in particular, this applies to `StdGen`.
Under the same assumptions, the lift from the adapted base monad into `PseudoRandT` is lawful.

## Implementation details

`PseudoRandT σ m α` is a state computation `ULift σ → m (α × ULift σ)`. It is an abbreviation
for the adapted `RandGT σ m`, so it uses the same state representation and operations. Sampling
operations determine how the state is advanced.

For `PseudoRandT σ m`, computations carry the product σ-algebra on the function space
`ULift σ → m (α × ULift σ)`, using the measurable spaces of the adapted base monad. When `σ`
is countable and has measurable singletons, evaluating a measurable family of computations at
a varying state is measurable. Together with the base monad's measurable bind, this establishes
the measurability of bind for the transformer. The algebraic laws follow pointwise from those
of the adapted base monad. These assumptions are needed for the lawful instance, not for
executing `PseudoRandT` computations.
-/

@[expose] public section

universe u v

namespace MeasureTheory

/-- A measurable space monad transformer for pseudorandom sampling with state `σ` and base
monad `m`. -/
abbrev PseudoRandT (σ : Type) (m : Type u → Type v) :=
  Monad.toMeasurableSpaceMonad (RandGT σ m)

/-- A pure measurable space monad for pseudorandom sampling with state `σ`. -/
abbrev PseudoRand (σ : Type) := PseudoRandT σ Id

instance {σ : Type} [MeasurableSpace σ] {m : Type u → Type v}
    [∀ α, [MeasurableSpace α] → MeasurableSpace (Monad.toMeasurableSpaceMonad m α)]
    {α : Type u} [MeasurableSpace α] : MeasurableSpace (PseudoRandT σ m α) :=
  inferInstanceAs (MeasurableSpace (ULift σ → Monad.toMeasurableSpaceMonad m (α × ULift σ)))

namespace PseudoRandT

variable {σ : Type} {m : Type u → Type v} {α β : Type u}
  [MeasurableSpace α] [MeasurableSpace β]

/-- Running pure preserves the state. -/
@[simp, grind =] theorem run_mPure [Monad m] (a : α) (s : ULift σ) :
    (mPure a : PseudoRandT σ m α).run s = pure (a, s) := rfl

/-- Running bind threads the state through both computations. -/
@[simp, grind =] theorem run_mBind [Monad m] (x : PseudoRandT σ m α) (f : α → PseudoRandT σ m β)
    (s : ULift σ) :
    (x >>=ₘ f).run s = x.run s >>= fun p => (f p.1).run p.2 := rfl

variable [MeasurableSpace σ]

/-- Pure returns its argument without changing the state. -/
theorem mPure_def [Monad m] : (mPure : α → PseudoRandT σ m α) =
    fun a s => (mPure (a, s) : Monad.toMeasurableSpaceMonad m (α × ULift σ)) := rfl

/-- Bind runs the second computation using the value and state produced by the first. -/
theorem mBind_def [Monad m] :
    (mBind : PseudoRandT σ m α → (α → PseudoRandT σ m β) → PseudoRandT σ m β) =
      fun x f s => (x.run s : Monad.toMeasurableSpaceMonad m (α × ULift σ)) >>=ₘ
        fun p => (f p.1).run p.2 := rfl

/-- Lifting a base computation preserves the state. Analogue of `StateT.run_monadLift`. -/
@[simp, grind =] theorem run_mMonadLift [Monad m] (x : Monad.toMeasurableSpaceMonad m α)
    (s : ULift σ) :
    (mMonadLift (m := Monad.toMeasurableSpaceMonad m) x : PseudoRandT σ m α).run s =
      x >>=ₘ fun a => (mPure (a, s) : Monad.toMeasurableSpaceMonad m (α × ULift σ)) := rfl

/-- Lifting a base computation runs it and pairs its result with the unchanged state. -/
theorem mMonadLift_def [Monad m] :
    (mMonadLift : Monad.toMeasurableSpaceMonad m α → PseudoRandT σ m α) =
      fun x s => x >>=ₘ fun a =>
        (mPure (a, s) : Monad.toMeasurableSpaceMonad m (α × ULift σ)) := rfl

/-- Lifting a base computation is measurable, without a countability assumption on the state. -/
@[fun_prop] theorem measurable_mMonadLift [Monad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (Monad.toMeasurableSpaceMonad m α)]
    [LawfulMeasurableSpaceMonad (Monad.toMeasurableSpaceMonad m)] :
    Measurable (mMonadLift : Monad.toMeasurableSpaceMonad m α → PseudoRandT σ m α) := by
  rw [mMonadLift_def]
  fun_prop

variable [Countable σ] [MeasurableSingletonClass σ]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (Monad.toMeasurableSpaceMonad m α)]

/-- Running a computation is jointly measurable in the computation and its initial state. -/
@[fun_prop] theorem measurable_run :
    Measurable (β := Monad.toMeasurableSpaceMonad m (α × ULift σ))
      (fun p : PseudoRandT σ m α × ULift σ => p.1.run p.2) :=
  measurable_id.uncurry

end PseudoRandT

instance {σ : Type} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    {m : Type u → Type v} [Monad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (Monad.toMeasurableSpaceMonad m α)]
    [LawfulMeasurableSpaceMonad (Monad.toMeasurableSpaceMonad m)] :
    LawfulMeasurableSpaceMonad (PseudoRandT σ m) where
  mMap_const := rfl
  id_mMap x := StateT.ext fun s => mBind_mPure (m := Monad.toMeasurableSpaceMonad m) (x.run s)
  measurable_mPure {_} _ := by
    rw [PseudoRandT.mPure_def]
    fun_prop
  measurable_mBind hf := by
    rw [PseudoRandT.mBind_def]
    fun_prop
  mBind_mPure_comp _ _ := rfl
  mPure_mBind x f hf := StateT.ext fun s =>
    mPure_mBind (m := Monad.toMeasurableSpaceMonad m)
      (x, s) (f := fun p => (f p.1).run p.2) (by fun_prop)
  mBind_assoc x f g hf hg := StateT.ext fun s =>
    mBind_assoc (m := Monad.toMeasurableSpaceMonad m)
      (x.run s) (f := fun p => (f p.1).run p.2) (g := fun p => (g p.1).run p.2)
        (by fun_prop) (by fun_prop)

/-- Lawfulness of the existing lift from the base monad, following `StateT.instLawfulMonadLift`
with measurable monad laws. -/
instance {σ : Type} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    {m : Type u → Type v} [Monad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (Monad.toMeasurableSpaceMonad m α)]
    [LawfulMeasurableSpaceMonad (Monad.toMeasurableSpaceMonad m)] :
    LawfulMeasurableSpaceMonadLiftT (Monad.toMeasurableSpaceMonad m) (PseudoRandT σ m) where
  measurable_mMonadLift := by fun_prop
  mMonadLift_mPure a := StateT.ext fun s =>
    mPure_mBind (m := Monad.toMeasurableSpaceMonad m) a
      (f := fun a => mPure (a, s)) (by fun_prop)
  mMonadLift_mBind {α} {β} _ _ x f hf := StateT.ext fun s => by
    have h : Measurable (β := Monad.toMeasurableSpaceMonad m (β × ULift σ))
        (fun p : α × ULift σ =>
          (mMonadLift (m := Monad.toMeasurableSpaceMonad m) (f p.1) :
            PseudoRandT σ m β).run p.2) := by
      fun_prop
    exact (mBind_assoc x (g := fun a => mPure (a, s)) hf (by fun_prop)).trans
      ((MeasurableSpaceBind.bind_congr (fun a => (mPure_mBind (a, s) h).symm)).trans
        (mBind_assoc x (f := fun a => mPure (a, s)) (by fun_prop) h).symm)

end MeasureTheory
