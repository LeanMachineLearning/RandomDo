/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

import RandomDo.RDo.Loop
import RandomDo.WP.ForIn
meta import RandomDo.RDo.Loop
meta import RandomDo.WP.ForIn

/-!
# Annotation retention and execution in `rdo` loops

These checks exercise invariants without requiring a measurable WP instance. Definition
inspection checks that annotations survive elaboration; definitional and executable comparisons
check that they do not change execution. The unbounded-loop tests assume only an abstract iterator.
-/

set_option linter.privateModule false
set_option linter.hashCommand false
set_option experimental.intrinsic true

open MeasureTheory MeasureTheory.Internal

universe v uρ

namespace TestNext.RDo.Invariants

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]

-- Neither a measurable WP interpretation nor measurable elements are needed to retain an
-- invariant. The assertion type is inferred from the supplied invariant itself.
private def sum (xs : List Nat) : m Nat := rdo
  let mut total := 0
  for x in xs
    invariant pref _ => total = pref.sum
  rdo
    total := total + x
  return total

example (xs : List Nat) : sum (m := m) xs = (rdo
    let mut total := 0
    for x in xs rdo
      total := total + x
    return total : m Nat) := rfl

private def membershipSum (xs : List Nat) : m Nat := rdo
  let mut total := 0
  for h : x in xs
    invariant pref _ => total = pref.sum
  rdo
    have _ : x ∈ xs := h
    total := total + x
  return total

-- The invariant is not merely parsed and discarded, and the proof-binder path must choose
-- the membership-aware wrapper. Inspect the declarations before reduction erases the wrappers.
open Lean Elab Command in
run_elab do
  for (decl, gadget) in #[(``sum, ``MeasureTheory.WP.mForInPureWithInvariant),
      (``membershipSum, ``MeasureTheory.WP.mForInPureWithInvariant')] do
    let info ← getConstInfoDefn decl
    unless info.value.find? (·.isConstOf gadget) |>.isSome do
      throwError "{decl} did not retain its invariant in {gadget}"

-- Assertions need not be propositions. In particular, annotation storage does not impose
-- a logical assertion lattice before a verification interpretation is chosen.
example (xs : List Nat) : m Nat := rdo
  let mut total := 0
  for x in xs
    invariant pref _ => total + pref.sum
  rdo
    total := total + x
  return total

-- Test the macro's pattern-binder path as well as standalone annotated terms.
example (xs : List (Nat × Nat)) : m Unit :=
  for (x, y) in xs
    invariant _ _ => True
  rdo
    let _ := x + y

-- Early returns and erased mutable variables change the state tuple. Both must remain usable
-- by name in the invariant, without attempting to execute the erased projection.
private def erasedSum (xs : List Nat) : m Nat := rdo
  erased mut visited := 0
  erased mut ok : True := True.intro
  let mut total := 0
  for x in xs
    invariant pref _ => visited = pref.length ∧ total = pref.sum ∧ ok = True.intro
  rdo
    visited := visited + 1
    ok := True.intro
    total := total + x
    if total ≥ 4 then return total
  return total

#guard Id.run (erasedSum (m := MId) [1, 3, 8]) == 4

-- An early return with no mutable variables uses a separate return-slot/unit layout.
private def first (xs : List Nat) : m Nat := rdo
  for x in xs
    invariant _ _ => True
  rdo
    return x
  return 0

#guard Id.run (first (m := MId) [7, 8]) == 7
#guard Id.run (first (m := MId) []) == 0

-- Compare effects and control flow with core: updates before `continue` and `break` survive,
-- and each nested loop gets its own invariant and control-flow boundary.
private def coreControl (xs : List Nat) : StateM Nat Nat := do
  let mut total := 0
  for x in xs
    invariant _ _ => True
  do
    modify (· + 1)
    if x = 0 then continue
    for y in [x, x + 1]
      invariant _ _ => True
    do
      total := total + y
      if y = x then break
    if total ≥ 4 then return total
  return total

private def measurableControl (xs : List Nat) :
    Monad.toMeasurableSpaceMonad (StateM Nat) Nat := rdo
  let mut total := 0
  for x in xs
    invariant _ _ => True
  rdo
    (modify (· + 1) : StateM Nat Unit)
    if x = 0 then continue
    for y in [x, x + 1]
      invariant _ _ => True
    rdo
      total := total + y
      if y = x then break
    if total ≥ 4 then return total
  return total

#guard Id.run (measurableControl [1, 0, 3, 8] 0) == Id.run (coreControl [1, 0, 3, 8] 0)
#guard Id.run (measurableControl [1, 2] 0) == Id.run (coreControl [1, 2] 0)

-- Exercise each annotation branch while the unbounded-loop implementation remains abstract.
section Loop

variable [MeasurableSpaceForIn m Lean.Loop Unit]

private def loopInvariant : m Nat := rdo
  let mut remaining := 5
  for _ in Lean.Loop.mk
    invariant done => done → remaining = 0
  rdo
    if remaining = 0 then break
    remaining := remaining - 1
  return remaining

private def loopVariant : m Nat := rdo
  let mut remaining := 5
  for _ in Lean.Loop.mk
    decreasing remaining
  rdo
    if remaining = 0 then break
    remaining := remaining - 1
  return remaining

private def loopBoth : m Nat := rdo
  let mut remaining := 5
  for _ in Lean.Loop.mk
    invariant done => done → remaining = 0
    decreasing remaining
  rdo
    if remaining = 0 then break
    remaining := remaining - 1
  return remaining

open Lean Elab Command in
run_elab do
  for (decl, gadget) in
      #[(``loopInvariant, ``MeasureTheory.WP.mForInLoopWithInvariant),
        (``loopVariant, ``MeasureTheory.WP.mForInLoopWithVariant),
        (``loopBoth, ``MeasureTheory.WP.mForInLoopWithInvariantAndVariant)] do
    let info ← getConstInfoDefn decl
    unless info.value.find? (·.isConstOf gadget) |>.isSome do
      throwError "{decl} did not retain its annotations in {gadget}"

end Loop

-- These restrictions are core's, rather than restrictions imposed by a particular backend.
/-- error: The `invariant` clause takes a `for` loop over a single collection. -/
#guard_msgs in
example : m Unit := rdo
  for x in [1], y in [2]
    invariant _ _ => True
  rdo
    let _ := x + y

/-- error: A `for` loop terminates with the collection it iterates; `decreasing` states the
termination measure of a `repeat` or `while` loop. -/
#guard_msgs (whitespace := lax) in
example : m Unit := rdo
  for _ in [1]
    decreasing 1
  rdo
    mPure ()

/-- error: The `invariant` clause takes at least two binders: the elements consumed so far
and the elements remaining. -/
#guard_msgs (whitespace := lax) in
example : m Unit := rdo
  for _ in [1]
    invariant _ => True
  rdo
    mPure ()

/-- error: The `invariant` clause takes no type ascription covering all its binders; ascribe the
type on an individual binder, as in `invariant (pref : List α) suff => ...`. -/
#guard_msgs (whitespace := lax) in
example : m Unit := rdo
  for _ in [1]
    invariant pref suff : Prop => pref = suff
  rdo
    mPure ()

-- An arbitrary collection with a ForIn instance is not silently assumed to enumerate purely.
/-- error: failed to synthesize instance of type class
  PureMeasurableSpaceForIn -/
#guard_msgs (substring := true) in
example {ρ : Type uρ} [MeasurableSpaceForIn m ρ Nat] [ForIn Id ρ Nat] (xs : ρ) : m Unit := rdo
  for _ in xs
    invariant _ _ => True
  rdo
    mPure ()

end TestNext.RDo.Invariants
