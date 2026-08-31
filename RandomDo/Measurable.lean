/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Monad.ForInInstances
public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.Data.List.OfFn

/-!
# Results on the measurable structure of lists, arrays and vectors

This file contains results on the measurable structure of lists, arrays and vectors.

## Main results

* `List.measurableEquivSigmaTuple`: the identification above, as a measurable equivalence.
* `measurableEmbedding_ofFn`: a stratum sits inside `List α` as a measurable embedding.
* `measurable_cons`, `measurable_headD`: prepending an element to a list, and reading its head,
  are measurable.
* `measurable_of_prodList`: a map out of `δ × List α` is measurable as soon as it is measurable on
  every stratum, which is how one reasons about a program taking a list as an argument.
-/

@[expose] public section

open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α]

/-- Lists are measurably equivalent to the sigma type of tuples of a given length. -/
def List.measurableEquivSigmaTuple : List α ≃ᵐ Σ n, Fin n → α where
  toFun := List.equivSigmaTuple
  invFun := List.equivSigmaTuple.symm
  left_inv := List.equivSigmaTuple.left_inv
  right_inv := List.equivSigmaTuple.right_inv
  measurable_toFun := Measurable.of_comap_le fun s a ↦ a
  measurable_invFun := by
    rintro _ ⟨_, hs, rfl⟩
    simp [hs]

lemma measurableEmbedding_ofFn (n : ℕ) :
    MeasurableEmbedding (List.ofFn : (Fin n → α) → List α) :=
  List.measurableEquivSigmaTuple.symm.measurableEmbedding.comp (measurableEmbedding_sigmaMk n)

@[fun_prop]
lemma measurable_ofFn (n : ℕ) : Measurable (List.ofFn : (Fin n → α) → List α) :=
  (measurableEmbedding_ofFn n).measurable

@[fun_prop]
lemma measurable_finCons {n : ℕ} :
    Measurable fun q : α × (Fin n → α) ↦ (Fin.cons q.1 q.2 : Fin (n + 1) → α) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [Fin.cons_zero]; fun_prop
  · simp only [Fin.cons_succ]; fun_prop

omit [MeasurableSpace α] in
private lemma ofFn_cons {n : ℕ} (a : α) (v : Fin n → α) :
    a :: List.ofFn v = List.ofFn (Fin.cons a v : Fin (n + 1) → α) := by
  rw [List.ofFn_succ]
  simp

/-- A map out of `δ × List α` is measurable as soon as it is measurable on every stratum
`δ × (Fin n → α)` of the lists of a fixed length. -/
lemma measurable_of_prodList {δ Y : Type*} [MeasurableSpace δ] [MeasurableSpace Y]
    {g : δ × List α → Y}
    (h : ∀ n, Measurable fun q : δ × (Fin n → α) => g (q.1, List.ofFn q.2)) : Measurable g := by
  intro t ht
  have key : g ⁻¹' t = ⋃ n : ℕ, (Prod.map id (List.ofFn (n := n))) ''
      ((fun q : δ × (Fin n → α) => g (q.1, List.ofFn q.2)) ⁻¹' t) := by
    ext ⟨d, l⟩
    simp only [mem_preimage, mem_iUnion, mem_image, Prod.exists, Prod.map_apply, id_eq,
      Prod.mk.injEq]
    constructor
    · intro hl
      exact ⟨l.length, d, l.get, by simpa using hl, rfl, by simp⟩
    · grind
  rw [key]
  refine MeasurableSet.iUnion fun n ↦ ?_
  exact (MeasurableEmbedding.id.prodMap (measurableEmbedding_ofFn n)).measurableSet_image' (h n ht)

/-- The σ-algebra of `Vector α n` is the one transported from `Fin n → α` along `v ↦ v[·]`. -/
lemma Vector.measurableSpace_eq_comap {n : ℕ} :
    (inferInstance : MeasurableSpace (Vector α n))
      = MeasurableSpace.comap (fun v (i : Fin n) ↦ v[i]) inferInstance := by
  have h : (Array.toList ∘ Vector.toArray : Vector α n → List α)
      = List.ofFn ∘ (fun v (i : Fin n) ↦ v[i]) := by
    funext v
    simp only [Function.comp_apply]
    rw [← Vector.ofFn_getElem (xs := v)]
    simp only [Vector.toArray_ofFn, Array.toList_ofFn]
    grind
  calc _
      = MeasurableSpace.comap (Array.toList ∘ Vector.toArray) inferInstance :=
        MeasurableSpace.comap_comp
    _ = MeasurableSpace.comap (List.ofFn ∘ fun v (i : Fin n) ↦ v[i])
          inferInstance := by rw [h]
    _ = MeasurableSpace.comap (fun v (i : Fin n) ↦ v[i])
          (MeasurableSpace.comap List.ofFn inferInstance) := MeasurableSpace.comap_comp.symm
    _ = _ := by rw [(measurableEmbedding_ofFn n).comap_eq]

/-- Vectors are equivalent to tuples of a given length. -/
def Vector.measurableEquivTuple {n : ℕ} : Vector α n ≃ᵐ (Fin n → α) where
  toFun v := fun i ↦ v[i]
  invFun := .ofFn
  left_inv := by grind
  right_inv := by grind
  measurable_toFun := Measurable.of_comap_le (ge_of_eq Vector.measurableSpace_eq_comap)
  measurable_invFun := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    simp only [Fin.getElem_fin, Equiv.symm_mk, Equiv.coe_fn_mk]
    convert measurable_ofFn n hu
    ext
    simp

instance : MeasurableSpace (Option α) := MeasurableSpace.map some inferInstance

theorem measurableSet_option_iff {s : Set (Option α)} :
    MeasurableSet s ↔ MeasurableSet (some ⁻¹' s) := Iff.rfl

theorem measurable_option_iff {Y : Type*} [MeasurableSpace Y] {f : Option α → Y} :
    Measurable f ↔ Measurable (f ∘ some) := Iff.rfl

@[fun_prop]
lemma measurable_some : Measurable (some : α → Option α) := fun _ hs ↦ hs

lemma measurableEmbedding_some : MeasurableEmbedding (some : α → Option α) where
  injective := Option.some_injective α
  measurable := measurable_some
  measurableSet_image' {t} ht := by
    rw [measurableSet_option_iff, preimage_image_eq _ (Option.some_injective α)]
    exact ht

@[fun_prop]
lemma measurable_isSome : Measurable (Option.isSome : Option α → Bool) :=
  measurable_option_iff.2 measurable_const

@[fun_prop]
lemma measurable_getD (a : α) : Measurable (fun o : Option α ↦ o.getD a) :=
  measurable_option_iff.2 measurable_id

end
