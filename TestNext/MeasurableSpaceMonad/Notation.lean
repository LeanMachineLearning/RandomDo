/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.Notation

/-!
# Elaboration without a concrete interpretation

The programs below use only abstract operation and iteration instances. They check the
notation import, mutable state, membership proofs, nested loops, and early control flow.
-/

open RandomDo MeasurableSpacePure MeasurableSpaceBind

@[expose] public section

namespace TestNext.MeasurableSpaceMonad

universe u v

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

example (a : α) : (rdo return a : m α) = mPure a := rfl

example (x : m α) (f : α → m β) : (rdo
    let a ← x
    f a : m β) = x >>=ₘ f := rfl

/-- Branching and mutation only require the abstract monad operations. -/
def branch (x : m α) (p : α → Bool) (f : α → m α) : m α := rdo
  let mut a ← x
  if p a then
    a ← f a
  return a

/-- An abstract collection loop can update its accumulator. -/
def accumulate [MeasurableSpaceForIn m (List α) α]
    (xs : List α) (initial : α) (step : α → α → m α) : m α := rdo
  let mut acc := initial
  for x in xs rdo
    acc ← step x acc
  return acc

/-- Nested loops retain mutations of the outer accumulator. -/
def nested [MeasurableSpaceForIn m (List α) α]
    (xs : List α) (initial : α) (step : α → α → α → m α) : m α := rdo
  let mut acc := initial
  for x in xs rdo
    for y in xs rdo
      acc ← step x y acc
  return acc

/-- Membership-aware iteration passes the proof to the body. -/
def withMembership [MeasurableSpaceForIn' m (List α) α inferInstance]
    (xs : List α) (initial : α) (step : (x : α) → x ∈ xs → α → m α) : m α := rdo
  let mut acc := initial
  for h : x in xs rdo
    acc ← step x h acc
  return acc

/-- A membership-aware instance also supplies ordinary iteration. -/
def forgetMembership [MeasurableSpaceForIn' m (List α) α inferInstance]
    (xs : List α) (initial : α) (step : α → α → m α) : m α :=
  accumulate xs initial step

/-- A nested loop can return from the whole block. -/
def firstMatch [MeasurableSpaceForIn m (List α) α]
    (xs : List α) (fallback : α) (p : α → α → Bool) : m α := rdo
  for x in xs rdo
    for y in xs rdo
      if p x y then
        return y
  return fallback

/-- `break` and `continue` preserve the loop's accumulated state. -/
def control [MeasurableSpaceForIn m (List α) α]
    (xs : List α) (initial : α) (skip stop : α → Bool) (step : α → α → m α) : m α := rdo
  let mut acc := initial
  for x in xs rdo
    if stop x then break
    if skip x then continue
    acc ← step x acc
  return acc

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
