/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Constructions
public import RandomDo.ForMathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The history of the interaction, one round later

## Main results

* `IT.hist_succ_eq_snoc`: the history before time `n + 1` is the history before time `n`, followed
  by the round at time `n`.
* `IT.map_hist_succ`: under `trajMeasure alg env`, the law of a function of the history before
  time `n + 1` is the law of the history before time `n`, bound to one round drawn from the step
  kernel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning.IT

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

lemma hist_succ_eq_snoc (n : ℕ) :
    hist (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨) (n + 1) = fun ω ↦ Fin.snoc (hist n ω) (step n ω) := by
  funext ω i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [hist, step]
  · simp [hist]

/-- The history before time `n + 1` is the history before time `n`, followed by one round drawn
from the step kernel. -/
lemma map_hist_succ {γ : Type*} [MeasurableSpace γ] (alg : Algorithm 𝓞 𝓐 𝓨)
    (env : Environment 𝓞 𝓐 𝓨) (n : ℕ) {F : Hist 𝓞 𝓐 𝓨 (n + 1) → γ} (hF : Measurable F) :
    (trajMeasure alg env).map (F ∘ hist (n + 1))
      = ((trajMeasure alg env).map (hist n)).bind
          fun h ↦ (stepKernel alg env n h).map fun x ↦ F (Fin.snoc h x) := by
  have hsnoc : Measurable fun p : Hist 𝓞 𝓐 𝓨 n × Round 𝓞 𝓐 𝓨 ↦ F (Fin.snoc p.1 p.2) :=
    hF.comp (measurable_fst.finSnoc measurable_snd)
  have e : F ∘ hist (n + 1)
      = (fun p ↦ F (Fin.snoc p.1 p.2)) ∘ (fun ω ↦ (hist n ω, step n ω)) := by
    rw [hist_succ_eq_snoc]
    rfl
  rw [e, ← Measure.map_map hsnoc (by fun_prop), (hasCondDistrib_step alg env n).map_eq,
    Measure.map_compProd_eq_bind _ _ hsnoc]

end Learning.IT
