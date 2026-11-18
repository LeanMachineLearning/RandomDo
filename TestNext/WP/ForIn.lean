/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.WP.ForIn
import RandomDo.RDo.Loop
import Lean.Elab.Tactic.VCGen

/-!
# Collection-loop verification rules

These two programs test the registered annotated-loop specs with core's `vcgen`. They remain
polymorphic in the measurable monad and assume only its WP interface. The primitive `mPure`
rule is supplied explicitly; a general `rdo` verification tactic is outside these tests.
-/

set_option experimental.vcgen true
set_option experimental.intrinsic true
set_option linter.privateModule false

open MeasureTheory Std.WP

namespace TestNext.WP.ForIn

universe v

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  {EPred : Type} [Assertion EPred] [WPMeasurableSpaceMonad m Prop EPred]

-- The annotated loop must supply different obligations for continuing and breaking. No
-- measurable space on α is available: only the loop state participates in the monad.
private def cappedCount {α : Type} (xs : List α) : m Nat := rdo
  let mut n := 0
  for _ in xs
    invariant pref _ => n ≤ pref.length ∧ n ≤ 2
  rdo
    if n = 2 then break
    n := n + 1
  return n

example {α : Type} (xs : List α) (epost : EPred) :
    Triple (cappedCount (m := m) xs) True (fun n => n ≤ xs.length ∧ n ≤ 2) epost := by
  simp only [cappedCount, mBind_mPure]
  vcgen [Triple.mPure]
  all_goals first
    | fun_prop
    | exact measurable_fun_forInStep (by fun_prop) (by fun_prop)
    | grind [List.length_append, List.length_cons]

-- The membership proof is passed to the callback, exercising the proof-carrying spec
-- and its conversion through ForIn.toList.
private def weightedCount {α : Type} (xs : List α) (weight : (a : α) → a ∈ xs → Nat) : m Nat := rdo
  let mut n := 0
  for h : a in xs
    invariant pref _ => n = pref.length
  rdo
    n := n + weight a h
  return n

example {α : Type} (xs : List α) (weight : (a : α) → a ∈ xs → Nat)
    (hweight : ∀ a h, weight a h = 1) (epost : EPred) :
    Triple (weightedCount (m := m) xs weight) True (fun n => n = xs.length) epost := by
  simp only [weightedCount, mBind_mPure]
  vcgen [Triple.mPure]
  all_goals first
    | fun_prop
    | grind [List.length_append, List.length_cons]

end TestNext.WP.ForIn
