/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.List

/-!
# Measurable array operations

Measurability of array transformations, transported through `Array.toList`.
-/

@[expose] public section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

@[fun_prop] theorem measurable_array_reverse : Measurable (Array.reverse : Array α → Array α) := by
  rw [instMeasurableSpaceArray, measurable_comap_iff]
  simp only [Function.comp_def, Array.toList_reverse]
  fun_prop

@[fun_prop] theorem measurable_array_append :
    Measurable (fun p : Array α × Array α => p.1 ++ p.2) := by
  rw [instMeasurableSpaceArray, measurable_comap_iff]
  simp only [Function.comp_def, Array.toList_append]
  fun_prop

@[fun_prop] theorem measurable_array_map {f : α → β} (hf : Measurable f) :
    Measurable (Array.map f) := by
  rw [instMeasurableSpaceArray, measurable_comap_iff]
  simp only [Function.comp_def, Array.toList_map]
  fun_prop
