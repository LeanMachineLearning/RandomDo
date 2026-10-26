/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Operations on measurable-space monads

A measurable-space monad takes a result type together with its measurable-space instance:
`m : (α : Type u) → [MeasurableSpace α] → Type v`. The classes in this file follow the separation
of `Functor`, `Pure`, `Bind`, and `Monad` in `Init/Core.lean`.

The operations accept ordinary functions. Measurability assumptions belong to the laws in
`RandomDoNext.MeasurableSpaceMonad.Core.Lawful`, so constructing a program does not require
proving its measurability. The operational classes alone assert no laws.

Declarations live in `RandomDo`. Opening this namespace also enables the scoped mapping
notation `<$>ₘ` and sequencing notation `>>=ₘ`.

Adapted from `RandomDo/Monad/MeasurableSpace.lean` at main commit `150ecab`.
-/

@[expose] public section

namespace RandomDo

open Function

universe u v

/-- A functor on types with a `MeasurableSpace` instance. The `mMap` operator `<$>ₘ` is overloaded
via instances of this class. This class does not require proofs of the `MeasurableSpaceFunctor`
axioms. Proofs may be provided or required via the `LawfulMeasurableSpaceFunctor` class. -/
class MeasurableSpaceFunctor (f : (α : Type u) → [MeasurableSpace α] → Type v) :
    Type (max (u+1) v) where
  /--
  Applies a function inside a functor on measurable spaces. This is used to overload the
  `<$>ₘ` operator.

  When mapping a constant function (if one cares about executing the code), use
  `MeasurableSpaceFunctor.mMapConst` instead, because it may be more efficient.
  -/
  mMap {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] : (α → β) → f α → f β
  /--
  Mapping a constant function.

  Given `a : α` and `v : f β`, `mMapConst a v` is equivalent to `(fun _ => a) <$>ₘ v`. For some
  functors, this can be implemented more efficiently; for all other functors, the default
  implementation may be used.
  -/
  mMapConst {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] : α → f β → f α :=
    mMap ∘ (const _)

@[inherit_doc] scoped infixr:100 " <$>ₘ " => MeasurableSpaceFunctor.mMap

/--
The `mPure` function is overloaded via `MeasurableSpacePure` instances.

`MeasurableSpacePure` is typically accessed via `MeasurableSpaceMonad` instances, which extend it.
-/
class MeasurableSpacePure (f : (α : Type u) → [MeasurableSpace α] → Type v) where
  /-- Given `a : α` where `α` has a `MeasurableSpace` instance, `mPure a : f α` represents an
  action that does nothing and returns `a`. -/
  mPure {α : Type u} [MeasurableSpace α] : α → f α

/--
The `>>=ₘ` operator is overloaded via instances of `MeasurableSpaceBind`.

`MeasurableSpaceBind` is typically used via `MeasurableSpaceMonad`, which extends it.
-/
class MeasurableSpaceBind (m : (α : Type u) → [MeasurableSpace α] → Type v) where
  /--
  Sequences two computations, allowing the second to depend on the value computed by the first.

  If `x : m α` and `f : α → m β`, then `x >>=ₘ f : m β` represents the result of executing `x`
  to get a value of type `α` and then passing it to `f`.
  -/
  mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] : m α → (α → m β) → m β

@[inherit_doc] scoped infixl:55  " >>=ₘ " => MeasurableSpaceBind.mBind

/-- Return, sequencing, and mapping for computations indexed by measurable result types.
By default, mapping sequences a computation with return. The operations accept ordinary functions;
measurability assumptions and laws are supplied separately by `LawfulMeasurableSpaceMonad`. -/
class MeasurableSpaceMonad (m : (α : Type u) → [MeasurableSpace α] → Type v) :
    Type (max (u+1) v)
    extends MeasurableSpaceFunctor m, MeasurableSpacePure m, MeasurableSpaceBind m where
  mMap f μ := mBind μ (Function.comp mPure f)

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} {α β : Type u}
  [MeasurableSpace α] [MeasurableSpace β]

theorem MeasurableSpaceBind.bind_congr [MeasurableSpaceBind m] {x : m α} {f g : α → m β}
    (h : ∀ a, f a = g a) : x >>=ₘ f = x >>=ₘ g := by
  simp [funext h]

theorem MeasurableSpaceFunctor.map_congr [MeasurableSpaceFunctor m] {x : m α} {f g : α → β}
    (h : ∀ a, f a = g a) : (f <$>ₘ x : m β) = g <$>ₘ x := by
  simp [funext h]

end RandomDo
