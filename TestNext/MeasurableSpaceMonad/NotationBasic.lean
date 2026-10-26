/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDoNext.MeasurableSpaceMonad.Notation.Basic

/-!
# Basic notation as a standalone import

Updating two mutable variables across a branch requires a measurable space on their product.
This example must elaborate without importing the collection-loop notation or an interpretation.
-/

open RandomDo

@[expose] public section

namespace TestNext.MeasurableSpaceMonad

universe u v

/-- Branching carries both abstract mutable values. -/
def branchPair {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (a : α) (b : β) (choose : Bool) (left : α → m α) (right : β → m β) : m (α × β) := rdo
  let mut x := a
  let mut y := b
  if choose then
    x ← left x
    y ← right y
  return (x, y)

end TestNext.MeasurableSpaceMonad
