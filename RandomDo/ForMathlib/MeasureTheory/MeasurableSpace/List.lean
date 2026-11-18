/-
Copyright (c) 2026 Gaëtan Serré, David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, David Ledvinka
-/
module

public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Collections
public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Measurable list operations

Measurability of the constructors and transformations used by monadic list operations.
Lists use the measurable space transported from finite tuples by `List.equivSigmaTuple`.
-/

@[expose] public section

open MeasureTheory Set

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

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

/-- To check a function on lists, it suffices to check it on each length. -/
theorem measurable_list {f : List α → β}
    (hf : ∀ n, Measurable (fun xs : Fin n → α => f (List.ofFn xs))) : Measurable f := by
  have h : Measurable (fun xs : Σ n, Fin n → α => f (List.ofFn xs.2)) :=
    fun s hs => measurableSet_sigma_iff.mpr fun n => hf n hs
  simpa [Function.comp_def, List.measurableEquivSigmaTuple, List.equivSigmaTuple] using
    h.comp List.measurableEquivSigmaTuple.measurable

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

/-- The list argument may also be the first component of the product. -/
theorem measurable_list_prod {f : List α × β → γ}
    (hf : ∀ n, Measurable (fun p : (Fin n → α) × β => f (List.ofFn p.1, p.2))) :
    Measurable f := by
  have h : Measurable (fun p : β × List α => f (p.2, p.1)) :=
    measurable_of_prodList fun n => (hf n).comp measurable_swap
  exact h.comp measurable_swap

@[fun_prop] theorem measurable_list_cons :
    Measurable (fun p : α × List α => p.1 :: p.2) := by
  apply measurable_of_prodList
  intro n
  simp_rw [← List.ofFn_cons]
  apply (measurable_ofFn _).comp
  apply Measurable.of_eval
  intro i
  cases i using Fin.cases <;> simp only [Fin.cons_zero, Fin.cons_succ] <;> fun_prop

@[fun_prop] theorem Measurable.list_cons {a : γ → α} {as : γ → List α}
    (ha : Measurable a) (has : Measurable as) : Measurable (fun x => a x :: as x) :=
  measurable_list_cons.comp (ha.prodMk has)

@[fun_prop] theorem measurable_list_append :
    Measurable (fun p : List α × List α => p.1 ++ p.2) := by
  apply measurable_list_prod
  intro n
  apply measurable_of_prodList
  intro k
  simp_rw [← List.ofFn_fin_append]
  apply (measurable_ofFn _).comp
  apply Measurable.of_eval
  intro i
  cases i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right] <;> fun_prop

@[fun_prop] theorem Measurable.list_append {as bs : γ → List α}
    (has : Measurable as) (hbs : Measurable bs) : Measurable (fun x => as x ++ bs x) :=
  measurable_list_append.comp (has.prodMk hbs)

@[fun_prop] theorem measurable_list_reverse : Measurable (List.reverse : List α → List α) := by
  apply measurable_list
  intro n
  induction n with
  | zero => simp only [List.ofFn_zero, List.reverse_nil]; fun_prop
  | succ n ih =>
    simp only [List.ofFn_succ, List.reverse_cons]
    exact (ih.comp (by fun_prop)).list_append (by fun_prop)

@[fun_prop] theorem measurable_list_map {f : α → β} (hf : Measurable f) :
    Measurable (List.map f) := by
  apply measurable_list
  intro n
  simp_rw [List.map_ofFn]
  fun_prop

@[fun_prop] theorem measurable_list_flatten :
    Measurable (List.flatten : List (List α) → List α) := by
  apply measurable_list
  intro n
  induction n with
  | zero => simp only [List.ofFn_zero, List.flatten_nil]; fun_prop
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons]
    exact (measurable_pi_apply 0).list_append (ih.comp (by fun_prop))

@[fun_prop] theorem measurable_list_toArray : Measurable (List.toArray : List α → Array α) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceArray, MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_id.le

@[fun_prop] theorem measurable_array_push :
    Measurable (fun p : Array α × α => p.1.push p.2) := by
  rw [instMeasurableSpaceArray, measurable_comap_iff]
  simp only [Function.comp_def, Array.toList_push]
  fun_prop
