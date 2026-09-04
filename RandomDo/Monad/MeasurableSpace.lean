/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Control.Random
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Measurable Space Monad

**TODO**

## Main definitions

* `MeasurableSpaceFunctor f`: **TODO**
* `MeasurableSpaceMonad m`: **TODO**
* `LawfulMeasurableSpaceFunctor f`: **TODO**
* `LawfulMeasurableSpaceMonad m`: **TODO**
* `MeasurableSpaceForIn`: **TODO**
* `MeasurableSpaceForIn'`: **TODO**

-/

@[expose] public section

open Function

section

universe u v

section MeasurableSpaceMonad

/-- A functor on types with a `MeasurableSpace` instance. The `mMap` operator `<$>ₘ` is overloaded
via instances of this class. This class does not require proofs of the `MeasurableSpaceFunctor`
axioms. Proofs may be provided or required via the `LawfulMeasurableSpaceFunctor` class. -/
class MeasurableSpaceFunctor (f : (α : Type u) → [MeasurableSpace α] → Type v) :
    Type (max (u+1) v) where
  /--
  Applies a function inside a functor on measurable spaces. This is used to overload the
  `<$>ₘ` operator.

  When mapping a constant function (if one cares about executing the code), use
  `Functor.mMapConst` instead, because it may be more efficient.
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

@[inherit_doc] infixr:100 " <$>ₘ " => MeasurableSpaceFunctor.mMap

/--
The `mPure` function is overloaded via `MeasurableSpacePure` instances.

`MeasurableSpacePure` is typically accessed via `MeasurableSpaceMonad` instances, which extend it.
-/
class MeasurableSpacePure (f : (α : Type u) → [MeasurableSpace α] → Type v) where
  /-- Given `a : α` where `α` has a `MeasurableSpace` instance, `mPure a : f α` represents an
  action that does nothing and returns a -/
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

@[inherit_doc] infixl:55  " >>=ₘ " => MeasurableSpaceBind.mBind

/-- A monad on types with a `MeasurableSpace` instance. This abstraction allows the user to write
code that depends on "random" side-effects -/
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

end MeasurableSpaceMonad

section Lawful

open MeasurableSpaceFunctor

/-- A `MeasurableSpaceFunctor` satisfies the measurable space functor laws. -/
class LawfulMeasurableSpaceFunctor
    (f : (α : Type u) → [MeasurableSpace α] → Type v) [MeasurableSpaceFunctor f]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (f α)] : Prop where
  /-- `mMap` of a measurable function is a measurable function. -/
  measurable_mMap {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    {g : α → β} (hg : Measurable g) : Measurable ((g <$>ₘ ·) : f α → f β)
  /-- The `mMapConst` implementation is equivalent to the default implementation. -/
  mMap_const {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] :
    (mMapConst : α → f β → f α) = mMap ∘ const β
  /-- `mMap` preserves identity. -/
  id_mMap {α : Type u} [MeasurableSpace α] (x : f α) : id <$>ₘ x = x
  /-- `mMap` preserves function composition of measurable functions. -/
  comp_mMap {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {g₀ : α → β} {g₁ : β → γ} (x : f α) (hg₀ : Measurable g₀) (hg₁ : Measurable g₁) :
    (g₁ ∘ g₀) <$>ₘ x = g₁ <$>ₘ g₀ <$>ₘ x

open LawfulMeasurableSpaceFunctor

attribute [fun_prop] measurable_mMap
attribute [simp] id_mMap

variable {f : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceFunctor f]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (f α)] [LawfulMeasurableSpaceFunctor f]
  {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

@[simp] theorem id_mMap' (x : f α) : (fun a => a) <$>ₘ x = x := id_mMap x

@[simp] theorem mMap_mMap {g₀ : α → β} {g₁ : β → γ} (x : f α)
    (hg₀ : Measurable g₀) (hg₁ : Measurable g₁) :
    g₁ <$>ₘ g₀ <$>ₘ x = (fun a => g₁ (g₀ a)) <$>ₘ x :=
  (comp_mMap x hg₀ hg₁).symm

open MeasurableSpaceBind MeasurableSpacePure MeasurableSpaceFunctor

/-- A `MeasurableSpaceMonad` satisfies the measurable space monad laws. -/
class LawfulMeasurableSpaceMonad
    (m : (α : Type u) → [MeasurableSpace α] → Type v) [MeasurableSpaceMonad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] : Prop
    extends LawfulMeasurableSpaceFunctor m where
  /-- `mPure` is a measurable function. -/
  measurable_mPure {α : Type u} [MeasurableSpace α] : Measurable (mPure : α → m α)
  /-- `mBind` of a measurable function is a measurable function. -/
  measurable_mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      {f : α → m β} (hf : Measurable f) : Measurable (fun x : m α => x >>=ₘ f)
  /-- A `mBind` followed by `mPure` composed with a measurable function is equivalent to a
  functorial map. -/
  mBind_mPure_comp {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      {f : α → β} (hf : Measurable f) (x : m α) :
    x >>=ₘ (fun a => mPure (f a)) = f <$>ₘ x
  /-- `mPure` followed by `mBind` of a function application is equivalent to function
  application. -/
  mPure_mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      (x : α) {f : α → m β} (hf : Measurable f) :
    mPure x >>=ₘ f = f x
  /-- `mBind` is associative on measurable functions. -/
  mBind_assoc {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
      (x : m α) {f : α → m β} {g : β → m γ} (hf : Measurable f) (hg : Measurable g) :
    x >>=ₘ f >>=ₘ g = x >>=ₘ fun x => f x >>=ₘ g
  measurable_mMap hg := (by
    convert measurable_mBind (measurable_mPure.comp hg)
    exact (mBind_mPure_comp hg _).symm)
  comp_mMap x g_meas h_meas := (by
    rw [← mBind_mPure_comp (by fun_prop), ← mBind_mPure_comp h_meas,
      ← mBind_mPure_comp g_meas, mBind_assoc _ (by fun_prop) (by fun_prop)]
    congr with _
    exact (mPure_mBind _ (measurable_mPure.comp h_meas)).symm)

open LawfulMeasurableSpaceMonad

attribute [fun_prop] measurable_mPure measurable_mBind
attribute [simp] pure_bind bind_assoc bind_pure_comp
attribute [grind <=] pure_bind

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)] [LawfulMeasurableSpaceMonad m]
  {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

@[simp] theorem mMap_mPure {f : α → β} (hf : Measurable f) (x : α) :
    f <$>ₘ (mPure x : m α) = mPure (f x) := by
  rw [← mBind_mPure_comp hf, mPure_mBind _ (by fun_prop)]

@[simp] theorem mBind_mPure (x : m α) : x >>=ₘ mPure = x := by
  change x >>=ₘ (fun a => (mPure (id a))) = x
  rw [mBind_mPure_comp (by fun_prop), id_mMap]

theorem mMap_eq_mPure_mBind {f : α → β} (hf : Measurable f) (x : m α) :
    f <$>ₘ x = x >>=ₘ fun a => mPure (f a) := by
  rw [← mBind_mPure_comp hf x]

theorem mBind_mPure_unit {x : m PUnit} : (x >>=ₘ fun _ => mPure ⟨⟩) = x := by rw [mBind_mPure]

@[simp] theorem mMap_mBind {f : β → γ} (hf : Measurable f) (x : m α)
      {g : α → m β} (hg : Measurable g) :
    f <$>ₘ (x >>=ₘ g) = x >>=ₘ fun a => f <$>ₘ g a := by
  rw [← mBind_mPure_comp hf, mBind_assoc _ hg (by fun_prop)]
  simp (disch := fun_prop) [mBind_mPure_comp]

@[simp] theorem mBind_mMap_left {f : α → β} (hf : Measurable f) (x : m α)
    {g : β → m γ} (hg : Measurable g) :
    ((f <$>ₘ x) >>=ₘ fun b => g b) = (x >>=ₘ fun a => g (f a)) := by
  rw [← mBind_mPure_comp hf]
  simp (disch := fun_prop) [mBind_assoc, mPure_mBind]

end Lawful

end

section MeasurableSpaceFor

universe uρ uα u v

variable {α : Type u} [mα : MeasurableSpace α] (m : (α : Type u) → [MeasurableSpace α] → Type v)
  {m' : (α : Type u) → Type v}

instance instMeasurableSpace {β : Type u} [mβ : MeasurableSpace β] :
    MeasurableSpace (ForInStep β) := mβ.map ForInStep.yield ⊓ mβ.map ForInStep.done

/--
Monadic iteration in `rdo`-blocks, using the `for x in xs` notation.
-/
class MeasurableSpaceForIn (ρ : Type uρ) (α : outParam (Type uα)) where
  /--
  Monadically iterates over the contents of a collection `xs`, with a local state `b` and the
  possibility of early termination.
  -/
  forIn {β : Type u} [MeasurableSpace β] (xs : ρ) (b : β)
    (f : α → β → m (ForInStep β)) : m β

/--
Monadic iteration in `rdo`-blocks with a membership proof, using the `for h : x in xs` notation.
-/
class MeasurableSpaceForIn' (ρ : Type uρ) (α : outParam (Type uα))
    (d : outParam (Membership α ρ)) where
  /--
  Monadically iterates over the contents of a collection `xs`, with a local state `b` and the
  possibility of early termination. At each iteration, the body of the loop is provided with a proof
  that the current element is in the collection.
  -/
  forIn' {β : Type u} [MeasurableSpace β] (xs : ρ) (b : β)
    (f : (a : α) → a ∈ xs → β → m (ForInStep β)) : m β

@[simps]
instance (priority := 500) instMeasurableSpaceForInOfForIn'
    {ρ : Type uρ} {α : Type uα} {d : Membership α ρ} [MeasurableSpaceForIn' m ρ α d] :
    MeasurableSpaceForIn m ρ α where
  forIn x b f := MeasurableSpaceForIn'.forIn' x b fun a _ s => f a s

end MeasurableSpaceFor
