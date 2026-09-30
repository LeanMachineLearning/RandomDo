/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The bind of a sum of two measures, and of a Dirac mass

-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem bind_add {μ ν : Measure α} {f : α → Measure β} (hf : AEMeasurable f (μ + ν)) :
    (μ + ν).bind f = μ.bind f + ν.bind f := by
  obtain ⟨hμ, hν⟩ := aemeasurable_add_measure_iff.1 hf
  ext s hs
  rw [add_apply, bind_apply hs hf, bind_apply hs hμ, bind_apply hs hν, lintegral_add_measure]

/-- Binding a Dirac mass at a point of a space whose points are measurable: the continuation needs
no measurability. -/
@[simp]
theorem dirac_bind' [MeasurableSingletonClass α] (a : α) (f : α → Measure β) :
    (dirac a).bind f = f a := by
  rw [Measure.bind, map_congr (ae_eq_dirac f)]
  change (map (fun _ ↦ f a) (dirac a)).join = f a
  rw [map_const]
  simp

end MeasureTheory.Measure
