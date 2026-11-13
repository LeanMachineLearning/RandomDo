/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.RDo.Core

/-!
# Translation and dead-code regressions for `rdo`

The equalities below use an abstract monad without laws. They check the generated operations,
so a dropped action or an accidental use of ordinary `pure`/`bind` cannot pass by reduction in
an `Id` instance. Independent universes also exercise construction of computation types.
-/

set_option linter.privateModule false

assert_not_exists MeasureTheory.MeasurableSpaceForIn RDo.rdoFor

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

universe u v

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

example (a : α) : (rdo return a : m α) = mPure a := rfl

example (x : m α) (f : α → m β) : (rdo
    let a ← x
    f a : m β) = x >>=ₘ f := rfl

-- An action whose result is discarded must still be sequenced, exactly once and before `next`.
example (action : m PUnit) (next : m α) : (rdo
    action
    next : m α) = action >>=ₘ fun _ => next := rfl

-- Branches must preserve both mutable values and the order of their monadic updates.
example (a : α) (b : β) (choose : Bool) (left : α → m α) (right : β → m β) :
    (rdo
      let mut x := a
      let mut y := b
      if choose then
        x ← left x
        y ← right y
      return (x, y) : m (α × β)) =
    (if choose then
      left a >>=ₘ fun x => right b >>=ₘ fun y => mPure (x, y)
    else mPure (a, b)) := by
  cases choose <;> rfl

/--
warning: This `do` element and its control-flow region are dead code. Consider removing it.
-/
#guard_msgs in
example (a : α) : (rdo
    return a
    return true : m α) = mPure a := rfl

-- This directly exercises the `deadSyntactically` branch of `mkPureApp`: warning traversal
-- must neither typecheck the discarded Bool at α nor request a missing monad instance.
open Lean Meta Elab Term Do in
omit [MeasurableSpaceMonad m] in
example (x : m α) : x = x := by_elab
  let x ← getFVarFromUserName `x
  let expectedType ← inferType x
  let ctx ← mkContext expectedType MeasureTheory.RDo.randOps
  let e ← MeasureTheory.RDo.randOps.mkPureApp ctx.doBlockResultType (mkConst ``Bool.true) |>.run
    { ctx with deadCode := .deadSyntactically }
  unless e.isMVar do
    throwError "Expected a fresh metavariable for syntactically dead code"
  unless ← isDefEq (← inferType e) expectedType do
    throwError "Incorrect monad application for syntactically dead code"
  mkEqRefl x

-- An alias's arguments need not be the result type and its measurable-space instance.
private abbrev TaggedResult (_tag : Type)
    (n : (α : Type) → [MeasurableSpace α] → Type v) := n Nat

example {n : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad n] :
    (rdo return 1 : TaggedResult Unit n) = (mPure 1 : n Nat) := rfl

-- Recognizing the instance argument must also allow aliases for its type.
private abbrev SpaceAlias (α : Type u) := MeasurableSpace α

example {γ : Type u} [SpaceAlias γ] (a : γ) :
    (rdo return a : m γ) = mPure a := rfl
