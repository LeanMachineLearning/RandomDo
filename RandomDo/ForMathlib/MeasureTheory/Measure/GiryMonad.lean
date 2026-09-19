/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Binding a pushforward measure

## Main results

* `Measure.bind_map`: binding after mapping is binding the composite, the measure counterpart of
  `PMF.bind_map`.
-/

@[expose] public section

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- `Measure.bind` sees through a `Measure.map` on the left. -/
lemma bind_map (μ : Measure α) {f : α → β} (hf : Measurable f) {k : β → Measure γ}
    (hk : Measurable k) : (μ.map f).bind k = μ.bind fun a ↦ k (f a) := by
  rw [Measure.bind, Measure.bind, map_map hk hf]
  rfl

end MeasureTheory.Measure
