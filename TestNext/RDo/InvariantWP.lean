/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.RDo.Loop
import RandomDo.WP.ForIn
import RandomDo.WP.MeasurableSpaceMonad

/-!
# Optional assertion-type inference for `rdo` invariants

The only WP interpretation used here is an abstract class assumption. No interpretation of
`Measure`, `PseudoRandT`, or an unbounded loop is needed to test the elaborator's interface.
-/

set_option linter.privateModule false
set_option experimental.intrinsic true

open MeasureTheory Std.WP

universe v w

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  {EPred : Type w} [Assertion EPred]

section State

variable [MeasurableSpace ((Nat × Nat) → Prop)]
  [WPMeasurableSpaceMonad m ((Nat × Nat) → Prop) EPred]

-- The pair pattern cannot be typed from its body alone. The optional WP lookup must supply
-- `Nat × Nat` as the state-binder type, while `total` is supplied by the loop-state tuple.
example (xs : List Nat) : m Nat := rdo
  let mut total := 0
  for x in xs
    invariant pref _ (lo, hi) => lo ≤ total ∧ total ≤ hi + pref.sum
  rdo
    total := total + x
  return total

-- The lambda form of `decreasing` uses the same assertion-state inference. This remains
-- polymorphic over the unbounded-loop implementation.
example [MeasurableSpaceForIn m Lean.Loop Unit] : m Nat := rdo
  let mut remaining := 5
  for _ in Lean.Loop.mk
    invariant done (lo, hi) => done → lo ≤ remaining ∧ remaining ≤ hi
    decreasing (lo, hi) => remaining + hi - lo
  rdo
    if remaining = 0 then break
    remaining := remaining - 1
  return remaining

/-- error: The invariant of a loop in this monad takes one argument, and this clause has
2 binders. The loop's mutable variables are named without binding them. -/
#guard_msgs (whitespace := lax) in
example : m Unit := rdo
  for _ in [1]
    invariant _ _ lo hi => lo ≤ hi
  rdo
    mPure ()

-- The public `wp` operation exposes the measurability law to `fun_prop` through the
-- generic WP instance, not only when spelling out the class field.
example {α : Type} [MeasurableSpace α] {post : α → (Nat × Nat) → Prop}
    (hpost : Measurable post) (epost : EPred) :
    Measurable (fun x : m α => wp x post epost) := by fun_prop

end State

-- Unfold both the outer alias and the alias in its result. The tuple pattern also checks
-- that the shared helper receives the argument types, not just the correct binder count.
private abbrev PairAssertions := (Nat × Nat) → Prop
private abbrev NestedAssertions := Nat → PairAssertions

section AssertionAliases

variable [MeasurableSpace NestedAssertions]
  [WPMeasurableSpaceMonad m NestedAssertions EPred]

example (xs : List Nat) : m Unit := rdo
  for _ in xs
    invariant _ _ n (lo, hi) => n ≤ lo ∧ lo ≤ hi
  rdo
    mPure ()

-- Unbounded-loop invariants and decreasing clauses use the same normalized assertion type.
example [MeasurableSpaceForIn m Lean.Loop Unit] : m Nat := rdo
  let mut remaining := 5
  for _ in Lean.Loop.mk
    invariant done n (lo, hi) => done → n ≤ lo ∧ lo ≤ remaining ∧ remaining ≤ hi
    decreasing n (lo, hi) => remaining + hi - lo + n
  rdo
    if remaining = 0 then break
    remaining := remaining - 1
  return remaining

/-- error: The invariant of a loop in this monad takes 2 arguments, and this clause has
3 binders. The loop's mutable variables are named without binding them. -/
#guard_msgs (whitespace := lax) in
example : m Unit := rdo
  for _ in [1]
    invariant _ _ n lo hi => n ≤ lo ∧ lo ≤ hi
  rdo
    mPure ()

end AssertionAliases

-- Importing the interface does not make it mandatory: a monad without a WP instance can
-- still carry an explicitly typed assertion.
example (xs : List Nat) : m Nat := rdo
  let mut total := 0
  for x in xs
    invariant pref _ (lo : Nat) => lo ≤ total + pref.sum
  rdo
    total := total + x
  return total
