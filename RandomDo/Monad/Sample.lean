/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Monad.Instances
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Kernel.Representation

/-!
# Sampling measures and kernels

`SampleM.draw P` consumes one entry of an IID stream with marginal law `P`.
`SampleM.ofMeasure` and `SampleM.ofKernel` use a common stream of uniform values in `[0,1]`
to sample probability measures and Markov kernels with standard Borel outputs. These constructors
are noncomputable mathematical samplers. Their distribution and measurability theorems do not
require a global `RandomM.MeasurableEvalDomain` instance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MeasurableSpaceBind MeasurableSpaceFunctor

universe u v w

namespace RandomM

variable {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-- The value returned by a sampler is independent of the remaining source state. -/
theorem indepFun_fst_snd (x : RandomM Ω P α) :
    IndepFun (fun ω ↦ (x.sample ω).1) (fun ω ↦ (x.sample ω).2) P := by
  apply (indepFun_iff_map_prod_eq_prod_map_map x.measurable_fst_sample.aemeasurable
    x.measurable_snd_sample.aemeasurable).2
  change P.map x.sample = x.law.prod (P.map (Prod.snd ∘ x.sample))
  rw [x.measurePreserving_snd.map_eq, x.map_sample]

/-- Sequencing two fixed samplers gives independent results, regardless of earlier draws. -/
theorem law_mBind_mMap_pair (x : RandomM Ω P α) (y : RandomM Ω P β) :
    (x >>=ₘ fun a ↦ Prod.mk a <$>ₘ y).law = x.law.prod y.law := by
  have hf : Measurable (fun p : α × Ω ↦ (Prod.mk p.1 <$>ₘ y).sample p.2) := by
    simp only [sample_mMap, measurable_prodMk_left]
    have hy : Measurable (fun p : α × Ω ↦ y.sample p.2) :=
      y.measurable_sample.comp measurable_snd
    exact (measurable_fst.prodMk hy.fst).prodMk hy.snd
  change (bind x _).law = _
  rw [law_bind_of_measurable _ _ hf]
  simp only [law_mMap, measurable_prodMk_left]
  ext s hs
  rw [Measure.bind_apply hs Measurable.map_prodMk_left.aemeasurable, Measure.prod_apply hs]
  congr 1
  funext a
  rw [Measure.map_apply measurable_prodMk_left hs]

end RandomM

namespace SampleM

variable {Ω : Type w} [MeasurableSpace Ω]

/-- Consume the next entry of an IID stream with common law `P`.
The returned value is independent of the remaining stream, which has its original law. -/
noncomputable def draw (P : Measure Ω) [IsProbabilityMeasure P] : SampleM Ω P Ω where
  sample ω := (ω 0, fun n ↦ ω (n + 1))
  measurePreserving := by
    have hi := iIndepFun_infinitePi (P := fun _ : ℕ ↦ P)
      (X := fun _ ω ↦ ω) (fun _ ↦ measurable_id)
    have h := indep_iSup_of_disjoint (fun i ↦ (measurable_pi_apply i).comap_le) hi.iIndep
      (S := {0}) (T := Set.range Nat.succ) (by simp)
    have hind : IndepFun (fun ω : ℕ → Ω ↦ ω 0) (fun ω : ℕ → Ω ↦ fun n ↦ ω (n + 1))
        (Measure.infinitePi fun _ : ℕ ↦ P) := by
      rw [IndepFun_iff_Indep, MeasurableSpace.comap_process_pi]
      simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left, iSup_range] using h
    refine ⟨by fun_prop, ?_⟩
    change (Measure.infinitePi fun _ : ℕ ↦ P).map (fun ω ↦ (ω 0, fun n ↦ ω (n + 1))) =
      ((Measure.infinitePi fun _ : ℕ ↦ P).map (fun ω ↦ ω 0)).prod _
    rw [hind.map_prod_eq_prod_map_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aemeasurable (by fun_prop)),
      Measure.map_infinitePi_infinitePi_of_inj Nat.succ_injective]

@[simp]
theorem sample_draw (P : Measure Ω) [IsProbabilityMeasure P] (ω : ℕ → Ω) :
    (draw P).sample ω = (ω 0, fun n ↦ ω (n + 1)) := rfl

@[simp]
theorem law_draw (P : Measure Ω) [IsProbabilityMeasure P] : (draw P).law = P :=
  Measure.infinitePi_map_eval (fun _ : ℕ ↦ P) 0

variable {α : Type u} [MeasurableSpace α] [StandardBorelSpace α]

/-- Sample a probability measure on a standard Borel space using one fresh uniform value.
All such samplers use the same source, so draws from different measures can be sequenced. -/
noncomputable def ofMeasure (μ : Measure α) [IsProbabilityMeasure μ] :
    SampleM unitInterval volume α := by
  letI := nonempty_of_isProbabilityMeasure μ
  exact RandomM.map μ.exists_measurable_map_eq.choose μ.exists_measurable_map_eq.choose_spec.1
    (draw volume)

@[simp]
theorem snd_sample_ofMeasure (μ : Measure α) [IsProbabilityMeasure μ]
    (ω : ℕ → unitInterval) : ((ofMeasure μ).sample ω).2 = fun n ↦ ω (n + 1) := rfl

@[simp]
theorem law_ofMeasure (μ : Measure α) [IsProbabilityMeasure μ] : (ofMeasure μ).law = μ := by
  let := nonempty_of_isProbabilityMeasure μ
  simpa only [ofMeasure, RandomM.law_map, law_draw] using μ.exists_measurable_map_eq.choose_spec.2

variable {δ : Type v} [MeasurableSpace δ] [Nonempty α]

/-- Sample a Markov kernel using one fresh uniform value. The chosen realization is jointly
measurable in the kernel's input and the source value, so it supports dependent sequencing. -/
noncomputable def ofKernel (κ : Kernel δ α) [IsMarkovKernel κ] (a : δ) :
    SampleM unitInterval volume α :=
  RandomM.map (κ.exists_measurable_map_eq_unitInterval.choose a)
    κ.exists_measurable_map_eq_unitInterval.choose_spec.1.of_uncurry_left (draw volume)

@[simp]
theorem snd_sample_ofKernel (κ : Kernel δ α) [IsMarkovKernel κ] (a : δ)
    (ω : ℕ → unitInterval) : ((ofKernel κ a).sample ω).2 = fun n ↦ ω (n + 1) := rfl

@[simp]
theorem law_ofKernel (κ : Kernel δ α) [IsMarkovKernel κ] (a : δ) :
    (ofKernel κ a).law = κ a := by
  simpa only [ofKernel, RandomM.law_map, law_draw] using
    κ.exists_measurable_map_eq_unitInterval.choose_spec.2 a

@[fun_prop]
theorem measurable_sample_ofKernel (κ : Kernel δ α) [IsMarkovKernel κ] :
    Measurable (fun p : δ × (ℕ → unitInterval) ↦ (ofKernel κ p.1).sample p.2) := by
  change Measurable (fun p : δ × (ℕ → unitInterval) ↦
    (κ.exists_measurable_map_eq_unitInterval.choose p.1 (p.2 0), fun n ↦ p.2 (n + 1)))
  exact (κ.exists_measurable_map_eq_unitInterval.choose_spec.1.comp
    (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).prodMk (by fun_prop)

@[fun_prop]
theorem measurable_ofKernel (κ : Kernel δ α) [IsMarkovKernel κ] : Measurable (ofKernel κ) :=
  RandomM.measurable_iff.2 fun _ ↦ (measurable_sample_ofKernel κ).comp measurable_prodMk_right

variable {β : Type u} [MeasurableSpace β]

@[simp]
theorem sample_mBind_ofKernel (x : SampleM unitInterval volume β)
    (κ : Kernel β α) [IsMarkovKernel κ] (ω : ℕ → unitInterval) :
    (x >>=ₘ ofKernel κ).sample ω = (ofKernel κ (x.sample ω).1).sample (x.sample ω).2 :=
  RandomM.sample_bind_of_measurable x (ofKernel κ) (measurable_sample_ofKernel κ) ω

/-- A dependent kernel draw has the usual distribution semantics of kernel composition. -/
@[simp]
theorem law_mBind_ofKernel (x : SampleM unitInterval volume β)
    (κ : Kernel β α) [IsMarkovKernel κ] :
    (x >>=ₘ ofKernel κ).law = x.law.bind κ := by
  change (RandomM.bind x _).law = _
  rw [RandomM.law_bind_of_measurable _ _ (measurable_sample_ofKernel κ)]
  simp only [law_ofKernel]

end SampleM
