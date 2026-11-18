/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import Std.WP

/-!
# Core bug: invariant binders reject assertion-type aliases

Recorded on 2026-11-17 with the installed `leanprover/lean4:v4.35.0` toolchain.
Status: reproduced locally; not reported upstream.

Expected: using `Assertions` and its definition `(Nat × Nat) → Prop` as the `WPMonad`
assertion type should permit the same invariant binders. Actual: the alias is rejected
as taking zero arguments. This file uses only `Std.WP`, with no RandomDo or mathlib imports.
Run `lake env lean TestNext/RDo/CoreInvariantAliases.lean` from the repository root.
Remove the `#guard_msgs` wrappers to see the failures directly when preparing a bug report.

In `Lean/Elab/BuiltinDo/For.lean`, `assertionLanguage?` returns the unreduced alias;
`checkAssertionBinders` counts arguments syntactically with `Expr.getForallArity`, and
`mkAssertionFun` likewise inspects the function type without unfolding aliases.
A single `whnf` is insufficient for aliases appearing after an argument, such as
`Nat → Assertions`. Unfolding the function arguments with `forallTelescopeReducing`
and rebuilding with `mkForallFVars` fixes both consumers without changing their code.

`RandomDo/RDo/Loop.lean` applies this fix in `assertionLanguage?`.
`TestNext/RDo/InvariantWP.lean` covers the corrected `rdo` behavior. This reproducer is
kept separate from the test-suite imports so an upstream fix does not preserve the bug
as a required behavior. Recheck it on the toolchain being reported before submitting.
-/

open Std.WP
open scoped Std.WP
set_option experimental.intrinsic true

abbrev Assertions := (Nat × Nat) → Prop

-- The expanded assertion type works.
example {m : Type → Type} [Monad m]
    [WPMonad m ((Nat × Nat) → Prop) EStack⟨⟩] (xs : List Nat) : m Unit := do
  for _ in xs
    invariant _ _ (lo, hi) => lo ≤ hi
  do
    pure ()

-- The definitionally equal alias is rejected by ordinary do notation.
/-- error: The invariant of a loop in this monad takes 0 arguments, and this clause has one binder.
The loop's mutable variables are named without binding them. -/
#guard_msgs (whitespace := lax) in
example {m : Type → Type} [Monad m]
    [WPMonad m Assertions EStack⟨⟩] (xs : List Nat) : m Unit := do
  for _ in xs
    invariant _ _ (lo, hi) => lo ≤ hi
  do
    pure ()

-- The same issue on a concrete state monad with its usual WP interpretation,
-- merely exposing that interpretation through the alias.
/-- error: The invariant of a loop in this monad takes 0 arguments, and this clause has one binder.
The loop's mutable variables are named without binding them. -/
#guard_msgs (whitespace := lax) in
example (xs : List Nat) : StateM (Nat × Nat) Unit :=
  letI : WPMonad (StateM (Nat × Nat)) Assertions EStack⟨⟩ :=
    inferInstanceAs (WPMonad (StateM (Nat × Nat)) ((Nat × Nat) → Prop) EStack⟨⟩)
  do
    for _ in xs
      invariant _ _ (lo, hi) => lo ≤ hi
    do
      pure ()
