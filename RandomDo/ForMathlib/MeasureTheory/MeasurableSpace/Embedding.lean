/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Lemmas about measurability of sigma types

This file contains lemmas about measurability of sigma types, in particular the fact that the
canonical injection of a summand into a sigma type is a measurable embedding.

## Main results

* `measurableSet_sigma_iff`: a set of a sigma type is measurable exactly when its preimage under
every `Sigma.mk i` is.
* `measurable_sigmaMk`, `measurableEmbedding_sigmaMk`: the injection of a summand into a sigma type
is a measurable embedding.
-/

@[expose] public section

open MeasureTheory

variable {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]

theorem measurableSet_sigma_iff {s : Set (Σ i, β i)} :
    MeasurableSet s ↔ ∀ i, MeasurableSet (Sigma.mk i ⁻¹' s) :=
  MeasurableSpace.measurableSet_iInf

@[fun_prop]
theorem measurable_sigmaMk (i : ι) : Measurable (Sigma.mk i : β i → Σ j, β j) :=
  fun _ hs => measurableSet_sigma_iff.1 hs i

theorem measurableEmbedding_sigmaMk (i : ι) :
    MeasurableEmbedding (Sigma.mk i : β i → Σ j, β j) where
  injective := sigma_mk_injective
  measurable := measurable_sigmaMk i
  measurableSet_image' {t} ht := measurableSet_sigma_iff.2 fun j => by
    by_cases h : j = i
    · subst h
      simpa only [Set.preimage_image_eq _ sigma_mk_injective] using ht
    · convert MeasurableSet.empty
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
      rintro ⟨y, -, hy⟩
      exact h (congrArg Sigma.fst hy).symm

end
