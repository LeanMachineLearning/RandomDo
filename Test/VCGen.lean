/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Verification

/-!
# Regression tests for quantitative verification

These proofs exercise stock `vcgen` on deterministic returns, continuous state, non-discrete
measurable spaces, and a loop whose collection and accumulator inhabit independent universes.
-/

@[expose] public section

open MeasureTheory Std.Internal.Do MeasurableSpacePure
open scoped ENNReal

set_option mvcgen.warning false

namespace Test.VCGen

noncomputable section

example : Triple (mPure (3 : ℝ≥0∞) : Measure ℝ≥0∞) 3 id ⟨⟩ := by
  vcgen
  rfl

def shift (μ : Measure ℝ) : Measure ℝ := rdo
  let x ← μ
  return x + 1

example (μ : Measure ℝ) (Q : ℝ → ℝ≥0∞) (hQ : Measurable Q) :
    Triple (shift μ) (∫⁻ x, Q (x + 1) ∂μ) Q ⟨⟩ := by
  vcgen (errorOnMissingSpec := false) [shift] <;> try fun_prop
  change (∫⁻ x, Q (x + 1) ∂μ) ≤ ∫⁻ x, ∫⁻ y, Q y ∂Measure.dirac (x + 1) ∂μ
  simp

section Indiscrete

local instance : MeasurableSpace Bool := ⊥

-- The measurable-postcondition return rule works without measurable singleton sets.
example : Triple (mPure true : Measure Bool) 7 (fun _ ↦ 7) ⟨⟩ := by
  vcgen
  fun_prop

end Indiscrete

universe u

-- The loop collection lives in `Type`, while the state can live in any universe.
def keep {α : Type u} [MeasurableSpace α] (xs : List Unit) (a : α) : Measure α := rdo
  let mut b := a
  for _ in xs rdo
    b := b
  return b

example {α : Type u} [MeasurableSpace α] (xs : List Unit) (a : α)
    (Q : α → ℝ≥0∞) (hQ : Measurable Q) :
    Triple (keep xs a) (Q a) Q ⟨⟩ := by
  vcgen [keep] invariants
  · fun _ _ b ↦ Q b
  all_goals try fun_prop
  all_goals try rfl
  exact fun _ hs ↦ ⟨hQ hs, hQ hs⟩

end
end Test.VCGen
