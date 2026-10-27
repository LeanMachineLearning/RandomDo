/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.Notation

/-!
# Elaboration without a concrete interpretation

The programs below use only abstract monad operations. They check return, binding, branching,
and mutable state through the notation import.
-/

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

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

/--
warning: This `do` element and its control-flow region are dead code. Consider removing it.
-/
#guard_msgs in
example (a : α) : (rdo
    return a
    return true : m α) = mPure a := rfl

-- Warning-only traversal must not typecheck the discarded value or require `mPure`.
open Lean Meta Elab Term Do in
omit [MeasurableSpaceMonad m] in
example (x : m α) : x = x := by_elab
  let x ← getFVarFromUserName `x
  let expectedType ← inferType x
  let ctx ← mkContext expectedType RDo.randOps
  let e ← RDo.randOps.mkPureApp ctx.doBlockResultType (mkConst ``Bool.true) |>.run
    { ctx with deadCode := .deadSyntactically }
  unless e.isMVar do
    throwError "Expected a fresh metavariable for syntactically dead code"
  unless ← isDefEq (← inferType e) expectedType do
    throwError "Incorrect monad application for syntactically dead code"
  mkEqRefl x

end TestNext.MeasurableSpaceMonad
