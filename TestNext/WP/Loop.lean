/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

import RandomDo.RDo.Loop
import RandomDo.WP.ForIn
import Lean.Elab.Tactic.VCGen

/-!
# Generic unbounded-loop verification

The registered invariant-and-variant rule works with stock `vcgen` while the loop and WP
implementations remain abstract. A countable discrete loop state discharges measurability
without imposing extra axioms on the loop implementation.
-/

set_option experimental.vcgen true
set_option experimental.intrinsic true
set_option linter.privateModule false

open MeasureTheory Std.WP

namespace TestNext.WP.Loop

universe v

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  [MeasurableSpaceForIn m Lean.Loop Unit] [LawfulMeasurableSpaceLoop m]
  {EPred : Type} [Assertion EPred] [WPMeasurableSpaceMonad m Prop EPred]

-- A nontrivial invariant/variant example for the registered generic rule.
def countdown (n : Nat) : m Nat := rdo
  let mut remaining := n
  while remaining > 0
    invariant done => remaining ≤ n ∧ (done → remaining = 0)
    decreasing remaining
  rdo
    remaining := remaining - 1
  return remaining

example (n : Nat) (epost : EPred) :
    Triple (countdown (m := m) n) True (fun r => r = 0) epost := by
  simp only [countdown, mBind_mPure]
  vcgen
  all_goals first
    | fun_prop
    | exact measurable_fun_forInStep (by fun_prop) (by fun_prop)
    | grind

end TestNext.WP.Loop
