/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.RDo.Core
import RandomDo.MeasurableSpaceMonad.Lift
import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Option

/-!
# Known differences between `do` and `rdo`

These are small reproducers for the deferred notation work, checked against Lean v4.35.0.
Each case pairs a working ordinary `do` example with the corresponding `rdo` failure. No concrete
monad implementation is needed. Core paths and declarations identify where to investigate;
these notes do not imply that every difference is a core bug.

A core `do` bug involving assertion-type aliases is recorded separately in
`TestNext/RDo/CoreInvariantAliases.lean`, which imports only `Std.WP` for a standalone bug report.
The local fix in `MeasureTheory.RDo.assertionLanguage?` lets `rdo` handle these aliases.

The failure checks match diagnostic fragments, avoiding incidental metavariable numbers and
hints. If a feature starts working, replace its expected failure with a success test. Preserving
these failures is not part of the intended API.

The final cases require additional measurable-monad interfaces or control-flow machinery.
While/repeat and VCGen are deferred to their separate development.
-/

open MeasureTheory

variable {n : Type → Type} [Monad n]
  {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m]

/-! ## Terminal pattern bindings with fallback

`Lean/Elab/BuiltinDo/Let.lean`, `elabDoLetElse`, supplies ordinary `pure PUnit.unit` when the
success body is absent. Both pure and monadic pattern bindings reach this path, bypassing `DoOps`.
-/

example (x : Option Nat) (fallback : n PUnit) : n PUnit := do
  let some _ := x | fallback

/-- error: Type mismatch
  pure PUnit.unit -/
#guard_msgs (substring := true) in
example (x : Option Nat) (fallback : m PUnit) : m PUnit := rdo
  let some _ := x | fallback

example (x : n (Option Nat)) (fallback : n PUnit) : n PUnit := do
  let some _ ← x | fallback

/-- error: Type mismatch
  pure PUnit.unit -/
#guard_msgs (substring := true) in
example (x : m (Option Nat)) (fallback : m PUnit) : m PUnit := rdo
  let some _ ← x | fallback

-- An explicit success body already works; the failure is not general pattern matching.
example (x : Option Nat) (fallback : m PUnit) :
    (rdo
      let some _ := x | fallback
      return : m PUnit) =
    (match x with | some _ => mPure PUnit.unit | none => fallback) := by
  cases x <;> rfl

/-! ## Inferring the monad without an expected result type

`Lean/Elab/Do/Basic.lean`, `extractMonadInfo.mkUnknownMonadResult`, creates a monad metavariable
of type `Type u → Type v`. A measurable monad also takes a measurable-space instance argument.
-/

example (x : n Nat) := do
  let a ← x
  return a + 1

/-- error: Type mismatch
  x
has type
  m ℕ
but is expected to have type -/
#guard_msgs (substring := true) in
example (x : m Nat) := rdo
  let a ← x
  return a + 1

-- Supplying the expected type allows `randOps.splitMonadApp?` to recognise the monad.
example (x : m Nat) : (rdo
    let a ← x
    return a + 1 : m Nat) = x >>=ₘ fun a => mPure (a + 1) := rfl

/-! ## Coercion of the value returned by an action

`Lean/Meta/Coe.lean`, `coerceMonadLift?`, uses the ordinary monad interfaces to map a coercion.
Extending this to measurable monads also requires deciding the measurability obligations.
-/

example (x : n Nat) : n Int := do
  let a : Int ← x
  return a

/-- error: Type mismatch
  x
has type
  m ℕ
but is expected to have type
  m ℤ -/
#guard_msgs (substring := true) in
example (x : m Nat) : m Int := rdo
  let a : Int ← x
  return a

-- The value-level coercion works after binding at the action's actual result type.
example (x : m Nat) : (rdo
    let a ← x
    return (a : Int) : m Int) = x >>=ₘ fun a => mPure (a : Int) := rfl

/-! ## Parenthesized `return` as a term

`Lean/Elab/Do/Switch.lean`, `expandTermReturn`, expands the term into ordinary `do` notation.
That nested block does not inherit the surrounding `rdo` operations.
-/

example : n Nat := do
  let a ← (return 1)
  return a

/-- error: invalid `do` notation, expected type is not a monad application -/
#guard_msgs (substring := true) in
example : m Nat := rdo
  let a ← (return 1)
  return a

-- An explicit nested `rdo` supplies the operations to use.
example : (rdo
    let a ← (rdo return 1)
    return a : m Nat) = mPure 1 := rfl

/-! ## Automatic lifting between monads

`Lean/Meta/Coe.lean`, `coerceMonadLift?`, inserts lifts using core's `MonadLiftT`. Our
`MeasurableSpaceMonadLiftT` supports explicit lifting and inference of composite lifts, but the
elaborator does not consult it. `DoOps` has no hook for customizing this step.

The missing behavior is automatic insertion of the lift, even when the required instance is
available, as it is for `Id` below. Calling `mMonadLift` explicitly works. This limitation also
affects expressions outside `rdo`; polymorphic programs whose actions already use the surrounding
monad need no lift.
-/

example (x : Id Nat) : n Nat := do
  let a ← x
  return a + 1

/-- error: Type mismatch
  x
has type
  Id ℕ
but is expected to have type -/
#guard_msgs (substring := true) in
example (x : Id Nat) : m Nat := rdo
  let a ← x
  return a + 1

-- The same action works with an explicit lift; instance inference supplies the operation.
example (x : Id Nat) : m Nat := rdo
  let a ← mMonadLift (m := MId) x
  return a + 1

/-! ## Effect forwarding with `do←`

`Lean/Elab/BuiltinDo/Forward.lean`, `tryElabForwardApp?`, uses `EffectForwarder` from
`Lean/Elab/Do/Control.lean`. Its control-flow encoding uses ordinary monad transformers.
The measurable-space assumption below removes a missing prerequisite from the example so the
remaining failure exposes the ordinary `Monad` dependency.
-/

example (wrap : ∀ {α : Type}, n α → n α) : n Nat := do
  wrap do←
    return 1
  return 2

/-- error: failed to synthesize instance of type class
  Monad m -/
#guard_msgs (substring := true) in
example [MeasurableSpace (Except Nat Unit)]
    (wrap : ∀ {α : Type} [MeasurableSpace α], m α → m α) : m Nat := rdo
  wrap do←
    return 1
  return 2

/-! ## Exceptions and finalization

`Lean/Elab/BuiltinDo/TryCatch.lean`, `elabDoTry`, shares that effect-forwarding machinery and uses
`MonadExceptOf`/`MonadExcept` and `MonadFinally`. Supporting these constructs requires appropriate
measurable-monad interfaces as well as changes to elaboration.
-/

example [MonadExceptOf Nat n] (x fallback : n Nat) : n Nat := do
  try x catch _e : Nat => fallback

/-- error: failed to synthesize instance of type class
  Monad m -/
#guard_msgs (substring := true) in
example (x fallback : m Nat) : m Nat := rdo
  try x catch _e : Nat => fallback

example [MonadFinally n] (x : n Nat) (cleanup : n Unit) : n Nat := do
  try x finally cleanup

/-- error: failed to synthesize instance of type class
  Monad m -/
#guard_msgs (substring := true) in
example (x : m Nat) (cleanup : m Unit) : m Nat := rdo
  try x finally cleanup
