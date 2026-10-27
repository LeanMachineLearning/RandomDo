/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.Defs

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

-/

@[expose] public section

namespace MeasureTheory

universe uρ uα u v

instance instMeasurableSpaceForInStep {β : Type u} [mβ : MeasurableSpace β] :
    MeasurableSpace (ForInStep β) :=
  mβ.map ForInStep.yield ⊓ mβ.map ForInStep.done

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
  forIn {β : Type u} [MeasurableSpace β] (xs : ρ) (b : β) (f : α → β → m (ForInStep β)) : m β

export MeasurableSpaceForIn (forIn)

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
  forIn' {β : Type u} [MeasurableSpace β] (x : ρ) (b : β)
    (f : (a : α) → a ∈ x → β → m (ForInStep β)) : m β

export MeasurableSpaceForIn' (forIn')

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} {ρ : Type uρ} {α : Type uα}

/--
A `MeasurableSpaceForIn'` instance also provides a `MeasurableSpaceForIn` instance by ignoring the
membership proof. We set the priority to 500 so it is below the default.
-/
@[default_instance]
instance (priority := 500) instMeasurableSpaceForInOfForIn' {d : Membership α ρ}
    [MeasurableSpaceForIn' m ρ α d] : MeasurableSpaceForIn m ρ α where
  forIn x b f := forIn' x b fun a _ => f a

@[simp] theorem forIn'_eq_forIn [d : Membership α ρ] [MeasurableSpaceForIn' m ρ α d]
    {β : Type u} [MeasurableSpace β] (x : ρ) (b : β)
    (f : (a : α) → a ∈ x → β → m (ForInStep β)) (g : (a : α) → β → m (ForInStep β))
    (h : ∀ a h b, f a h b = g a b) :
    forIn' x b f = forIn x b g := by
  simp only [forIn]
  congr
  funext a ha b
  exact h a ha b

@[wf_preprocess] theorem forIn_eq_forIn' [d : Membership α ρ] [MeasurableSpaceForIn' m ρ α d]
    {β : Type u} [MeasurableSpace β] (x : ρ) (b : β) (f : α → β → m (ForInStep β)) :
    forIn x b f = forIn' x b (fun x h => binderNameHint x f <| binderNameHint h () <| f x) := by
  rfl

end MeasureTheory
