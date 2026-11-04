/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.Monad.Notation
-- Executable checks also need interpreter access to the imported declarations.
meta import RandomDo.Monad.Notation

/-!
# State and control flow in `rdo` loops

Abstract translation checks cover the iteration interfaces without assuming measurable
collections or elements. Executable checks use a test-only state monad and core's list iterator:
the log makes dropped, duplicated, or reordered actions observable. These are tests of the
elaborator, not implementations of the production collection instances.
-/

-- This module intentionally contains private fixtures and executable test assertions.
set_option linter.privateModule false
set_option linter.hashCommand false

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

universe u v uρ uι

section Abstract

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {ρ : Type uρ} {ι : Type uι} {α : Type u} [MeasurableSpace α]

-- Only the loop state needs a measurable-space instance; collection and element universes
-- need not coincide with the state or computation universe.
example [MeasurableSpaceForIn m ρ ι] (xs : ρ) (init : α) (step : ι → α → m α) :
    (rdo
      let mut state := init
      for a in xs rdo
        state ← step a state
      return state : m α) =
    (MeasureTheory.forIn xs init fun a state =>
      step a state >>=ₘ fun state => mPure (ForInStep.yield state)) >>=ₘ mPure := rfl

-- A proof binder must pass the actual membership proof to the body.
example [Membership ι ρ] [MeasurableSpaceForIn' m ρ ι inferInstance]
    (xs : ρ) (init : α) (step : (a : ι) → a ∈ xs → α → m α) :
    (rdo
      let mut state := init
      for h : a in xs rdo
        state ← step a h state
      return state : m α) =
    (MeasureTheory.forIn' xs init fun a h state =>
      step a h state >>=ₘ fun state => mPure (ForInStep.yield state)) >>=ₘ mPure := rfl

end Abstract

namespace Test.ForInElab

private def TraceM (α : Type) [_mα : MeasurableSpace α] := StateM (List Nat) α

local instance : MeasurableSpaceMonad TraceM where
  mPure := pure
  mBind := bind

local instance {α : Type} : MeasurableSpaceForIn' TraceM (List α) α inferInstance where
  forIn' := _root_.ForIn'.forIn' (m := StateM (List Nat))

private def run {α : Type} [MeasurableSpace α] (action : TraceM α) : α × List Nat :=
  Id.run (action [])

private def record (n : Nat) : TraceM Unit := fun log => ((), log ++ [n])

-- `continue` and `break` must preserve updates to both mutable variables. The log records
-- which iterations ran, including the skipped value and the final value before `break`.
private def control (xs : List Nat) : TraceM (Nat × Nat) := rdo
  let mut visits := 0
  let mut total := 0
  for n in xs rdo
    record n
    visits := visits + 1
    if n = 0 then continue
    total := total + n
    if n = 3 then break
  return (visits, total)

#guard run (control [1, 0, 3, 7]) == ((3, 4), [1, 0, 3])
#guard run (control [1, 2]) == ((2, 3), [1, 2])

-- Early return must preserve the updated state and skip both remaining iterations and the
-- continuation after the loop. Normal completion must run that continuation.
private def returnWithState (xs : List Nat) : TraceM Nat := rdo
  let mut total := 0
  for n in xs rdo
    record n
    total := total + n
    if total ≥ 4 then return total
  record 99
  return total

#guard run (returnWithState [1, 3, 5]) == (4, [1, 3])
#guard run (returnWithState [1, 2]) == (3, [1, 2, 99])

-- The elaborator uses a different state tuple when an early return carries no mutable variables.
private def returnWithoutState (xs : List Nat) : TraceM Nat := rdo
  for n in xs rdo
    record n
    if n = 3 then return n
  return 0

#guard run (returnWithoutState [1, 3, 5]) == (3, [1, 3])
#guard run (returnWithoutState [1, 2]) == (0, [1, 2])

-- Inner loop jumps must not jump out of the outer loop. This also exercises the custom
-- `ControlInfo` handler, whose absence previously prevented nested loops from elaborating.
private def nested : TraceM Unit := rdo
  for a in [1, 2] rdo
    for b in [0, 1, 2, 3] rdo
      if b = 0 then continue
      if b = 2 then break
      record (10 * a + b)
    record (10 * a)

#guard run nested == ((), [11, 10, 21, 20])

-- Parallel iteration stores the second stream in the loop state. The particular σ-algebra is
-- irrelevant here: this test is about macro expansion and stopping at the shorter collection.
local instance : MeasurableSpace (List Nat) := ⊤

private def parallel (xs : List (Nat × Nat)) (ys : List Nat) : TraceM Unit := rdo
  for (a, b) in xs, c in ys rdo
    record (a + b + c)

#guard run (parallel [(1, 2), (3, 4), (5, 6)] [10, 20]) == ((), [13, 27])
#guard run (parallel [(1, 2)] [10, 20]) == ((), [13])

end Test.ForInElab
