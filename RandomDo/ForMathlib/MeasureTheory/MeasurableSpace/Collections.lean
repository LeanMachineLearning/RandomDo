/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Data.List.OfFn
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable spaces on finite collections

Lists carry the σ-algebra transported from `Σ n, Fin n → α` by `List.equivSigmaTuple`.
Arrays and subarrays inherit their measurable spaces through `toList`, and vectors through
`toArray`. In particular, the measurable space on a subarray depends only on its contents,
not on the unused portion of its backing array.

The conversion functions `Array.toList`, `Subarray.toList`, and `Vector.toArray` are measurable.
These constructions are independent of the monad and iteration interfaces.
-/

@[expose] public section

section MeasurableSpace

variable {α : Type*} [MeasurableSpace α]

instance instMeasurableSpaceList : MeasurableSpace (List α) :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

instance instMeasurableSpaceArray : MeasurableSpace (Array α) :=
  MeasurableSpace.comap Array.toList inferInstance

instance instMeasurableSpaceVector {n : ℕ} : MeasurableSpace (Vector α n) :=
  MeasurableSpace.comap Vector.toArray inferInstance

instance instMeasurableSpaceSubarray : MeasurableSpace (Subarray α) :=
  MeasurableSpace.comap (fun s : Subarray α ↦ s.toList) inferInstance

@[fun_prop]
lemma measurable_toList : Measurable (Array.toList : Array α → List α) :=
  Measurable.of_comap_le fun _ a ↦ a

@[fun_prop]
lemma measurable_subarray_toList : Measurable (fun s : Subarray α ↦ s.toList) :=
  Measurable.of_comap_le fun _ a ↦ a

@[fun_prop]
lemma measurable_toArray {n : ℕ} : Measurable (Vector.toArray : Vector α n → Array α) :=
  Measurable.of_comap_le fun _ a ↦ a

end MeasurableSpace
