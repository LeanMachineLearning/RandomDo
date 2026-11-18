/-
Copyright (c) 2026 David Ledvinka, Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.Defs
public import Init.Internal.Order.While

/-!
# Iteration in measurable space monads

This file defines the typeclasses `MeasurableSpaceForIn` and `MeasurableSpaceForIn'`, the
`MeasurableSpaceMonad` analogues of Lean core's `ForIn` and `ForIn'`, respectively.

Instances of `MeasurableSpaceForIn` specify how to iterate over a collection of
elements, running a monadic loop body at each step while carrying a local state and allowing
early termination. These instances enable the use of `for x in xs rdo ...` in `rdo` notation.
`MeasurableSpaceForIn'` provides the same operation, but also passes the loop body a proof that the
current element belongs to the collection. It enables the use of `for h : x in xs rdo ...` in
`rdo` notation (as well as `for x in xs rdo ...` since a `MeasurableSpaceForIn'` instance also
provides a `MeasurableSpaceForIn` instance).

For unbounded loops, a `MeasurableSpaceForIn m Lean.Loop Unit` instance enables the use of
`while p rdo` and `repeat rdo` in `rdo` notation. The class `LawfulMeasurableSpaceLoop` states
that the solution provided in the instance is a valid solution to the loop equation.

## Implementation details

The approach to unbounded loops diverges more substantially from core than most other aspects
of `MeasurableSpaceMonad`s and `rdo` notation. The core approach is to define a generic
`ForIn m Lean.Loop Unit` instance for every monad and its "lawfulness" is given by an instance
of the class `Lean.Order.MonadTail` which is sufficient to guarantee that the loop instance is
a valid solution to the loop equation. This is problematic for `MeasurableSpaceMonad`s for two
reasons. Firstly, the analogue of condition `Lean.Order.MonadTail` does not hold for `Measure`
even though solutions to loop equations exist for `Measure`. Secondly, when solutions to the
loop equation are not unique it is important for our applications that specific solutions are
chosen. To make it concrete consider the program:

```
noncomputable def sample : Measure ℕ := rdo
  repeat rdo
    let heads ← HasBernoulli.bernoulli (1 / 2 : ℝ)
    if heads then return 0
```

Here the loop equation is `μ = (1/2)δ₀ + (1/2)μ` which gives both `μ = δ₀` and `μ = ∞ • δ₀`
as solutions, but clearly we want the solution to be `μ = δ₀` (since this program should
terminate and return `0` with probability 1).

Therefore our approach is that each `MeasurableSpaceMonad` supplies its own instance of
`MeasurableSpaceForIn m Lean.Loop Unit` (but ones that arise from `Monad.toMeasurableSpaceMonad`
can inherit the core one), and an instance of the class `LawfulMeasurableSpaceLoop` is
used to assert that the instance satisfies the loop equation.
-/

@[expose] public section

namespace MeasureTheory

universe uρ uα u v

instance instMeasurableSpaceForInStep {β : Type u} [mβ : MeasurableSpace β] :
    MeasurableSpace (ForInStep β) :=
  mβ.map ForInStep.yield ⊓ mβ.map ForInStep.done

@[fun_prop]
theorem measurable_forInStep_yield {β : Type*} [MeasurableSpace β] :
    Measurable (@ForInStep.yield β) := fun _ hs => hs.1

@[fun_prop]
theorem measurable_forInStep_done {β : Type*} [MeasurableSpace β] :
    Measurable (@ForInStep.done β) := fun _ hs => hs.2

@[fun_prop]
theorem measurable_fun_forInStep {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {f : ForInStep β → γ} (hd : Measurable (fun b => f (.done b)))
    (hy : Measurable (fun b => f (.yield b))) : Measurable f :=
  fun _ hs => ⟨hy hs, hd hs⟩

/-- Extracting the value from either loop step is measurable. -/
@[fun_prop] theorem measurable_forInStep_value {β : Type*} [MeasurableSpace β] :
    Measurable (@ForInStep.value β) :=
  measurable_fun_forInStep measurable_id measurable_id

/--
Monadic iteration in `rdo` blocks, using the `for x in xs rdo ...` notation.

The parameter `m` is the monad of the `rdo` block in which iteration is performed, `ρ` is the type
of the collection being iterated over, and `α` is the type of elements.

This is the measurable space analogue of `ForIn`.
-/
class MeasurableSpaceForIn (m : (α : Type u) → [MeasurableSpace α] → Type v)
    (ρ : Type uρ) (α : outParam (Type uα)) where
  /--
  Monadically iterates over the contents of a collection `xs`, with a local state `b` and the
  possibility of early termination. This is the measurable space analogue of `ForIn.forIn`.
  -/
  mForIn {β : Type u} [MeasurableSpace β] (xs : ρ) (b : β) (f : α → β → m (ForInStep β)) : m β

export MeasurableSpaceForIn (mForIn)

/--
Monadic iteration in `rdo` blocks with a membership proof, using the `for h : x in xs rdo ...`
notation.

The parameter `m` is the monad of the `rdo` block in which iteration is performed, `ρ` is the type
of the collection being iterated over, `α` is the type of elements, and `d` is the specific
membership predicate to provide.

This is the measurable space analogue of `ForIn'`.
-/
class MeasurableSpaceForIn' (m : (α : Type u) → [MeasurableSpace α] → Type v)
    (ρ : Type uρ) (α : outParam (Type uα)) (d : outParam (Membership α ρ)) where
  /--
  Monadically iterates over the contents of a collection `xs`, with a local state `b` and the
  possibility of early termination. At each iteration, the body of the loop is provided with a
  proof that the current element is in the collection. This is the measurable space analogue of
  `ForIn'.forIn'`.
  -/
  mForIn' {β : Type u} [MeasurableSpace β] (xs : ρ) (b : β)
    (f : (a : α) → a ∈ xs → β → m (ForInStep β)) : m β

export MeasurableSpaceForIn' (mForIn')

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} {ρ : Type uρ} {α : Type uα}

/--
A `MeasurableSpaceForIn'` instance also provides a `MeasurableSpaceForIn` instance by ignoring the
membership proof. We set the priority to 500 so it is below the default.
-/
@[default_instance]
instance (priority := 500) instMeasurableSpaceForInOfForIn' {d : Membership α ρ}
    [MeasurableSpaceForIn' m ρ α d] : MeasurableSpaceForIn m ρ α where
  mForIn xs b f := mForIn' xs b fun a _ => f a

@[simp] theorem mForIn'_eq_mForIn [d : Membership α ρ] [MeasurableSpaceForIn' m ρ α d]
    {β : Type u} [MeasurableSpace β] (xs : ρ) (b : β)
    (f : (a : α) → a ∈ xs → β → m (ForInStep β)) (g : (a : α) → β → m (ForInStep β))
    (h : ∀ a h b, f a h b = g a b) :
    mForIn' xs b f = mForIn xs b g := by
  simp only [mForIn]
  congr
  funext a ha b
  exact h a ha b

@[wf_preprocess] theorem mForIn_eq_mForIn' [d : Membership α ρ] [MeasurableSpaceForIn' m ρ α d]
    {β : Type u} [MeasurableSpace β] (xs : ρ) (b : β) (f : α → β → m (ForInStep β)) :
    mForIn xs b f = mForIn' xs b (fun x h => binderNameHint x f <| binderNameHint h () <| f x) := by
  rfl

section Loop

/--
Asserts that the `MeasurableSpaceForIn m Lean.Loop Unit` instance satisfies the loop equation for
measurable loop bodies.
-/
class LawfulMeasurableSpaceLoop (m : (α : Type u) → [MeasurableSpace α] → Type v)
    [MeasurableSpaceMonad m] [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    [MeasurableSpaceForIn m Lean.Loop Unit] : Prop where
  /--
  The loop satisfies its recursive equation whenever `f` is measurable. The result of
  `f b` is bound to `mPure` for a `.done` step and to the loop with the updated state for a
  `.yield` step.
  -/
  mForIn_eq {β : Type u} [MeasurableSpace β] (l : Lean.Loop) (b : β)
    (f : β → m (ForInStep β)) (hf : Measurable f) :
    mForIn l b (fun _ => f) = f b >>=ₘ fun
      | .done b' => mPure b'
      | .yield b' => mForIn l b' (fun _ => f)

instance {m : Type u → Type v} [Monad m] :
    MeasurableSpaceForIn (Monad.toMeasurableSpaceMonad m) Lean.Loop Unit where
  mForIn := Lean.Loop.forIn

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (Monad.toMeasurableSpaceMonad m α)] :
    LawfulMeasurableSpaceLoop (Monad.toMeasurableSpaceMonad m) where
  mForIn_eq _ _ _ _ := Lean.Loop.forIn_eq_of_monadTail

end Loop

end MeasureTheory
