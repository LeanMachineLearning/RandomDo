/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.Probability.Transfer
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Independence.Basic

set_option linter.style.header false

/-!
# Pulling probabilistic statements back along a measure-preserving map

For a measure-preserving map `f : Ω' → Ω` from `(Ω', P')` to `(Ω, P)`, a statement about random
variables on `Ω` is equivalent to the same statement about their compositions with `f` on `Ω'`:
laws, events and their measure, integrals, almost-everywhere statements, independence, conditional
laws, integrability. This file collects these facts in the forms the `transfer` tactic uses.

* `MeasurePreserving.map_fun_comp` and the `MeasurePreserving.*_fun_comp_iff` lemmas: the
  statement on `Ω'` on the left.
* The `@[transfer]` lemmas `MeasurePreserving.transfer_*`: the statement on `Ω` on the left, with
  `hf` as first explicit argument, which is what `transfer` rewrites with.
* The `@[transfer_forward]` lemmas `*.comp_measurePreserving` and `*.preimage_measurePreserving`:
  one-way transport of a hypothesis, for statements that do not go both ways, such as
  measurability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ### Pulling statements back along a measure-preserving map -/

namespace MeasureTheory.MeasurePreserving

variable {Ω Ω' 𝓧 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} {P' : Measure Ω'}
  {f : Ω' → Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨}

/-- The law of `X ∘ f` under `P'` is the law of `X` under `P`. -/
lemma map_fun_comp (hf : MeasurePreserving f P' P) (hX : AEMeasurable X P) :
    P'.map (fun ω ↦ X (f ω)) = P.map X := by
  rw [← hf.map_eq] at hX ⊢
  exact (AEMeasurable.map_map_of_aemeasurable hX hf.measurable.aemeasurable).symm

lemma hasLaw_fun_comp_iff (hf : MeasurePreserving f P' P) (hX : Measurable X) {ν : Measure 𝓧} :
    HasLaw (fun ω ↦ X (f ω)) ν P' ↔ HasLaw X ν P where
  mp h := ⟨hX.aemeasurable, by rw [← hf.map_fun_comp hX.aemeasurable]; exact h.map_eq⟩
  mpr h := h.comp hf.hasLaw

lemma indepFun_fun_comp_iff (hf : MeasurePreserving f P' P) (hX : Measurable X)
    (hY : Measurable Y) :
    IndepFun (fun ω ↦ X (f ω)) (fun ω ↦ Y (f ω)) P' ↔ IndepFun X Y P := by
  simp only [indepFun_iff_measure_inter_preimage_eq_mul]
  refine forall₄_congr fun s t hs ht ↦ ?_
  change P' (f ⁻¹' (X ⁻¹' s) ∩ f ⁻¹' (Y ⁻¹' t))
    = P' (f ⁻¹' (X ⁻¹' s)) * P' (f ⁻¹' (Y ⁻¹' t)) ↔ _
  rw [← Set.preimage_inter, hf.measure_preimage ((hX hs).inter (hY ht)).nullMeasurableSet,
    hf.measure_preimage (hX hs).nullMeasurableSet, hf.measure_preimage (hY ht).nullMeasurableSet]

lemma hasCondDistrib_fun_comp_iff (hf : MeasurePreserving f P' P) (hX : Measurable X)
    (hY : Measurable Y) {κ : Kernel 𝓧 𝓨} :
    HasCondDistrib (fun ω ↦ Y (f ω)) (fun ω ↦ X (f ω)) κ P' ↔ HasCondDistrib Y X κ P := by
  unfold HasCondDistrib
  rw [hf.map_fun_comp hX.aemeasurable]
  exact hf.hasLaw_fun_comp_iff (hX.prodMk hY)

/-! ### The `@[transfer]` lemmas: from the old space to the new one

The same facts, stated with the old space on the left and `hf` as the first explicit argument,
which is what the `transfer` tactic rewrites with. -/

@[transfer]
lemma transfer_map (hf : MeasurePreserving f P' P) (hX : AEMeasurable X P) :
    P.map X = P'.map (fun ω ↦ X (f ω)) :=
  (hf.map_fun_comp hX).symm

@[transfer]
lemma transfer_measure (hf : MeasurePreserving f P' P) {s : Set Ω} (hs : NullMeasurableSet s P) :
    P s = P' (f ⁻¹' s) :=
  (hf.measure_preimage hs).symm

@[transfer]
lemma transfer_real (hf : MeasurePreserving f P' P) {s : Set Ω} (hs : NullMeasurableSet s P) :
    P.real s = P'.real (f ⁻¹' s) := by
  simp only [measureReal_def, hf.measure_preimage hs]

@[transfer]
lemma transfer_hasLaw (hf : MeasurePreserving f P' P) (hX : Measurable X) {ν : Measure 𝓧} :
    HasLaw X ν P ↔ HasLaw (fun ω ↦ X (f ω)) ν P' :=
  (hf.hasLaw_fun_comp_iff hX).symm

@[transfer]
lemma transfer_indepFun (hf : MeasurePreserving f P' P) (hX : Measurable X) (hY : Measurable Y) :
    IndepFun X Y P ↔ IndepFun (fun ω ↦ X (f ω)) (fun ω ↦ Y (f ω)) P' :=
  (hf.indepFun_fun_comp_iff hX hY).symm

@[transfer]
lemma transfer_hasCondDistrib (hf : MeasurePreserving f P' P) (hX : Measurable X)
    (hY : Measurable Y) {κ : Kernel 𝓧 𝓨} :
    HasCondDistrib Y X κ P ↔ HasCondDistrib (fun ω ↦ Y (f ω)) (fun ω ↦ X (f ω)) κ P' :=
  (hf.hasCondDistrib_fun_comp_iff hX hY).symm

@[transfer]
lemma transfer_integral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hf : MeasurePreserving f P' P) {g : Ω → G} (hg : AEStronglyMeasurable g P) :
    ∫ ω, g ω ∂P = ∫ ω, g (f ω) ∂P' := by
  rw [← hf.map_eq] at hg ⊢
  exact integral_map hf.measurable.aemeasurable hg

@[transfer]
lemma transfer_lintegral (hf : MeasurePreserving f P' P) {g : Ω → ENNReal}
    (hg : AEMeasurable g P) :
    ∫⁻ ω, g ω ∂P = ∫⁻ ω, g (f ω) ∂P' := by
  rw [← hf.map_eq] at hg ⊢
  exact lintegral_map' hg hf.measurable.aemeasurable

@[transfer]
lemma transfer_ae (hf : MeasurePreserving f P' P) {p : Ω → Prop}
    (hp : NullMeasurableSet {ω | p ω} P) :
    (∀ᵐ ω ∂P, p ω) ↔ ∀ᵐ ω ∂P', p (f ω) := by
  rw [ae_iff, ae_iff, ← hf.measure_preimage (s := {ω | ¬ p ω}) hp.compl, Set.preimage_ofPred_eq]

@[transfer]
lemma transfer_ae_eq (hf : MeasurePreserving f P' P) {X Y : Ω → 𝓧}
    (h : NullMeasurableSet {ω | X ω = Y ω} P) :
    X =ᵐ[P] Y ↔ (fun ω ↦ X (f ω)) =ᵐ[P'] fun ω ↦ Y (f ω) :=
  hf.transfer_ae h

@[transfer]
lemma transfer_integrable {G : Type*} [NormedAddCommGroup G] (hf : MeasurePreserving f P' P)
    {g : Ω → G} (hg : AEStronglyMeasurable g P) :
    Integrable g P ↔ Integrable (fun ω ↦ g (f ω)) P' :=
  (hf.integrable_comp hg).symm

end MeasureTheory.MeasurePreserving

/-! ### Forward transport of hypotheses

A hypothesis about the old space gives one about the new space. These are the
`@[transfer_forward]` lemmas: the hypothesis first, then `hf`, then side conditions. -/

section Forward

variable {Ω Ω' 𝓧 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} {P' : Measure Ω'}
  {f : Ω' → Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨}

@[transfer_forward]
lemma Measurable.comp_measurePreserving (hX : Measurable X) (hf : MeasurePreserving f P' P) :
    Measurable fun ω ↦ X (f ω) :=
  hX.comp hf.measurable

@[transfer_forward]
lemma AEMeasurable.comp_measurePreserving (hX : AEMeasurable X P)
    (hf : MeasurePreserving f P' P) :
    AEMeasurable (fun ω ↦ X (f ω)) P' :=
  hX.comp_quasiMeasurePreserving hf.quasiMeasurePreserving

attribute [transfer_forward] MeasureTheory.AEStronglyMeasurable.comp_measurePreserving

@[transfer_forward]
lemma MeasurableSet.preimage_measurePreserving {s : Set Ω} (hs : MeasurableSet s)
    (hf : MeasurePreserving f P' P) :
    MeasurableSet (f ⁻¹' s) :=
  hf.measurable hs

@[transfer_forward]
lemma MeasureTheory.NullMeasurableSet.preimage_measurePreserving {s : Set Ω}
    (hs : NullMeasurableSet s P) (hf : MeasurePreserving f P' P) :
    NullMeasurableSet (f ⁻¹' s) P' :=
  hs.preimage hf.quasiMeasurePreserving

@[transfer_forward]
lemma ProbabilityTheory.HasLaw.comp_measurePreserving {ν : Measure 𝓧} (hX : HasLaw X ν P)
    (hf : MeasurePreserving f P' P) :
    HasLaw (fun ω ↦ X (f ω)) ν P' :=
  hX.comp hf.hasLaw

/-- A conditional law pulls back along a measure-preserving map. -/
@[transfer_forward]
lemma ProbabilityTheory.HasCondDistrib.comp_measurePreserving {κ : Kernel 𝓧 𝓨}
    (h : HasCondDistrib Y X κ P) (hf : MeasurePreserving f P' P) :
    HasCondDistrib (fun ω ↦ Y (f ω)) (fun ω ↦ X (f ω)) κ P' := by
  have hX := h.aemeasurable_fst
  unfold HasCondDistrib at h ⊢
  rw [hf.map_fun_comp hX]
  exact h.comp hf.hasLaw

@[transfer_forward]
lemma ProbabilityTheory.IndepFun.comp_measurePreserving (h : IndepFun X Y P)
    (hf : MeasurePreserving f P' P) (hX : Measurable X) (hY : Measurable Y) :
    IndepFun (fun ω ↦ X (f ω)) (fun ω ↦ Y (f ω)) P' :=
  (hf.indepFun_fun_comp_iff hX hY).2 h

@[transfer_forward]
lemma MeasureTheory.Integrable.comp_measurePreserving {G : Type*} [NormedAddCommGroup G]
    {g : Ω → G} (hg : Integrable g P) (hf : MeasurePreserving f P' P) :
    Integrable (fun ω ↦ g (f ω)) P' :=
  (hf.integrable_comp hg.aestronglyMeasurable).2 hg

end Forward

end

end
