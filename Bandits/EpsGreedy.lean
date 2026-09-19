/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Bandits.Theory

/-!
# ε-greedy, and the draws inside its algorithm-environment sequence

ε-greedy is a randomized bandit algorithm: at each round it tosses a coin of bias `ε`, and on heads
pulls an arm drawn uniformly, on tails the greedy arm (the first arm never pulled if there is one,
and otherwise the one with the best empirical mean). Its policy is written here as an `rdo`
program, and turned into a LeanMachineLearning `Algorithm`.

A statement such as *every arm is pulled with probability at least `ε / K`* is about the coin and
the uniform draw, but an algorithm-environment sequence `IsAlgEnvSeq O A R alg env P` only has the
actions: the draws of the policy are not random variables of `(Ω, P)`. `alg_env_trace` supplies
them. From the trace `rdo_trace` finds for the policy (`hasTrace_policy`), it moves the goal to a
space that also carries the draws `T n`, with their conditional law given the history and the
action as a readout of them, and discharges the obligation of transferring the result back.

There, the draws have the law `Ber(ε) ⊗ uniform` whatever the history (`draws_eq_const`); on the
event where the coin says explore and the uniform draw is `a`, the action is `a`. Hence the
exploration bound, for any environment, and a linear lower bound on the regret.

## Main results

* `le_map_action`: at every round, every arm is pulled with probability at least `ε / K`.
* `le_integral_regret`: the expected regret of ε-greedy after `n` rounds is at least
  `n ε / K ∑ₐ Δₐ`.
* `le_integral_regret_banditRunRand`: the same lower bound for the program `banditRunRand` of
  `Bandits.Defs` running `epsGreedyArm`, which is ε-greedy on the statistics of the history
  (`policy_eq_epsGreedyArm`, `Bandits.Theory.banditRunRand_eq_map`). This is the program that runs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning RDo Bandits
open scoped ENNReal NNReal

namespace RDoBandit.EpsGreedy

variable {K : ℕ} [NeZero K]

/-- The uniform distribution on the arms. -/
noncomputable def uniformArm : Measure (Fin K) := (PMF.uniformOfFintype (Fin K)).toMeasure

instance : IsProbabilityMeasure (uniformArm (K := K)) := by unfold uniformArm; infer_instance

lemma uniformArm_singleton (a : Fin K) : uniformArm {a} = (K : ℝ≥0∞)⁻¹ := by
  rw [uniformArm, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
    PMF.uniformOfFintype_apply, Fintype.card_fin]

/-- The greedy arm of the statistics is measurable: the first unpulled arm is read off counts in a
countable set, and the argmax is measurable. -/
@[fun_prop]
lemma measurable_greedyArm_state : Measurable (RDoBandit.greedyArm (K := K) (R := ℝ)) := by
  let F : (Fin K → ℕ) × Fin K → Fin K := fun p ↦
    match (List.finRange K).find? fun a ↦ p.1 a == 0 with
    | some a => a
    | none => p.2
  have hF : Measurable F := by
    refine measurable_from_prod_countable_right fun c ↦ ?_
    simp only [F]
    split <;> fun_prop
  have hc : Measurable fun s : State K ℝ ↦ fun a : Fin K ↦ s.1[a] :=
    measurable_pi_iff.2 fun a ↦ (measurable_vector_getElem a).comp measurable_fst
  have hg : Measurable fun s : State K ℝ ↦
      (HasArgmax.argmax fun a ↦ s.2.1[a] / (s.1[a] : ℝ) : Fin K) :=
    measurable_hasArgmax_real.comp (measurable_pi_iff.2 fun a ↦ by fun_prop)
  exact hF.comp (hc.prodMk hg)

/-- The greedy arm of a history: the greedy arm of its statistics, the first arm never pulled if
there is one, and otherwise the one with the best empirical mean. -/
noncomputable def greedyArm (n : ℕ) (h : Hist Unit (Fin K) ℝ n) : Fin K :=
  RDoBandit.greedyArm (histState n h)

@[fun_prop]
lemma measurable_greedyArm (n : ℕ) : Measurable (greedyArm (K := K) n) :=
  measurable_greedyArm_state.comp (measurable_histState n)

variable (ε : unitInterval)

/-- **The ε-greedy policy**, as an `rdo` program: toss a coin of bias `ε`; on heads explore an arm
drawn uniformly, on tails exploit the greedy arm. -/
noncomputable def policy (n : ℕ) (p : Hist Unit (Fin K) ℝ n × Unit) : Measure (Fin K) := rdo
  let explore ← bernoulliMeasure true false ε
  let u ← uniformArm
  return if explore then u else greedyArm n p.1

instance (n : ℕ) : IsMarkov (policy (K := K) ε n) := by unfold policy; is_markov

/-- ε-greedy, as a LeanMachineLearning algorithm. -/
noncomputable def alg : Algorithm Unit (Fin K) ℝ where
  policy n := markovKernel (policy ε n) inferInstance

/-- The draws the policy makes at round `n`: the coin, then the uniform arm. This is the trace
kernel `rdo_trace` finds; neither draw reads the history. -/
noncomputable def draws (n : ℕ) : Kernel (Hist Unit (Fin K) ℝ n × Unit) (Bool × Fin K) :=
  Kernel.const _ (bernoulliMeasure true false ε)
    ⊗ₖ Kernel.prodMkRight Bool (Kernel.const _ uniformArm)

/-- The action, read off the history and the draws. -/
noncomputable def readout (n : ℕ) (p : (Hist Unit (Fin K) ℝ n × Unit) × (Bool × Fin K)) : Fin K :=
  if p.2.1 = true then p.2.2 else greedyArm n p.1.1

instance (n : ℕ) : IsMarkovKernel (draws (K := K) ε n) := by unfold draws; infer_instance

/-- `rdo_trace` finds the trace of the policy. -/
lemma hasTrace_policy (n : ℕ) : HasTrace (policy (K := K) ε n) (draws ε n) (readout n) := by
  rdo_trace (policy (K := K) ε n) with h
  exact h

/-- The trace of ε-greedy, for `alg_env_trace`. -/
noncomputable def trace : AlgTrace (alg (K := K) ε) (Bool × Fin K) where
  K := draws ε
  out := readout
  hasTrace n := hasTrace_policy ε n

/-- The draws do not depend on the history: they are a coin and an independent uniform arm. -/
lemma draws_eq_const (n : ℕ) :
    draws (K := K) ε n = Kernel.const _ ((bernoulliMeasure true false ε).prod uniformArm) := by
  ext1 p
  rw [draws, Kernel.compProd_apply_eq_compProd_sectR, Kernel.const_apply, Kernel.const_apply]
  have : (Kernel.prodMkRight Bool
      (Kernel.const (Hist Unit (Fin K) ℝ n × Unit) (uniformArm (K := K)))).sectR p
      = Kernel.const Bool (uniformArm (K := K)) := by ext1 b; rfl
  rw [this, Measure.compProd_const]

/-- **Every arm is explored.** Whatever the environment, at every round, ε-greedy pulls each arm
with probability at least `ε / K`. -/
theorem le_map_action (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀]
    {P : Measure Ω₀} [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K}
    {R : ℕ → Ω₀ → ℝ} (h : IsAlgEnvSeq O A R (alg (K := K) ε) env P) (n : ℕ) (a : Fin K) :
    ENNReal.ofReal (ε / K) ≤ P.map (A n) {a} := by
  alg_env_trace (trace (K := K) ε) with Ω P O A R T hseq htr hT hA
  have hlaw : HasLaw (T n) ((bernoulliMeasure true false ε).prod uniformArm) P := by
    have h1 := hT n
    simp only [trace, draws_eq_const] at h1
    exact h1.hasLaw_of_const
  -- When the coin says explore and the uniform draw is `a`, the action is `a`.
  have hsub : T n ⁻¹' {(true, a)} ≤ᵐ[P] A n ⁻¹' {a} := by
    filter_upwards [hA n] with ω hω hTω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hTω ⊢
    rw [hω]
    simp [trace, readout, hTω]
  calc ENNReal.ofReal (ε / K)
      = ((bernoulliMeasure true false ε).prod uniformArm) {(true, a)} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod,
          bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp)
            (by simp), uniformArm_singleton,
          ENNReal.ofReal_div_of_pos (by exact_mod_cast NeZero.pos K), ENNReal.ofReal_natCast,
          div_eq_mul_inv, ← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
    _ = P (T n ⁻¹' {(true, a)}) := by
        rw [← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable
          (measurableSet_singleton _)]
    _ ≤ P (A n ⁻¹' {a}) := measure_mono_ae hsub
    _ = P.map (A n) {a} :=
        (Measure.map_apply (hseq.measurable_action n) (measurableSet_singleton a)).symm

/-- **ε-greedy has linear regret.** Against any stationary environment, the expected regret after
`n` rounds is at least `n ε / K` times the sum of the gaps: every round, each arm is explored with
probability at least `ε / K`. -/
theorem le_integral_regret (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] {Ω₀ : Type}
    [MeasurableSpace Ω₀] {P : Measure Ω₀} [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit}
    {A : ℕ → Ω₀ → Fin K} {R : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A R (alg (K := K) ε) (stationaryEnv ν) P) (n : ℕ) :
    (n : ℝ) * ((ε : ℝ) / K) * ∑ a, gap ν a ≤ P[regret ν A n] := by
  have hA := h.measurable_action
  have hint (s : ℕ) : Integrable (fun ω ↦ gap ν (A s ω)) P :=
    (Integrable.of_finite (μ := P.map (A s)) (f := gap ν)).comp_measurable (hA s)
  have hround (s : ℕ) : (ε : ℝ) / K * ∑ a, gap ν a ≤ ∫ ω, gap ν (A s ω) ∂P := by
    rw [← integral_map (hA s).aemeasurable (measurable_of_countable _).aestronglyMeasurable,
      integral_fintype (Integrable.of_finite (f := gap ν)), Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    rw [smul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (gap_nonneg (ν := ν) (a := a))
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1
      (le_map_action ε (stationaryEnv ν) h s a)
  simp_rw [regret_eq_sum_gap]
  rw [integral_finsetSum _ fun s _ ↦ hint s]
  calc (n : ℝ) * ((ε : ℝ) / K) * ∑ a, gap ν a
        = ∑ _s ∈ Finset.range n, (ε : ℝ) / K * ∑ a, gap ν a := by
        simp [Finset.sum_const]; ring
    _ ≤ ∑ s ∈ Finset.range n, ∫ ω, gap ν (A s ω) ∂P := Finset.sum_le_sum fun s _ ↦ hround s

/-! ### The program that runs -/

/-- At `Measure`, the program `epsGreedyArm` is a Markov kernel in the state. -/
instance isMarkov_epsGreedyArm (n : ℕ) :
    IsMarkov (epsGreedyArm (m := Measure) (K := K) (ε : ℝ) n) := by
  unfold epsGreedyArm
  is_markov

/-- **The program is ε-greedy.** At `Measure`, the program `epsGreedyArm` on the statistics of a
history is the policy of ε-greedy on that history. -/
lemma policy_eq_epsGreedyArm (n : ℕ) (h : Hist Unit (Fin K) ℝ n) :
    (alg (K := K) ε).policy n (h, ()) = epsGreedyArm (m := Measure) (ε : ℝ) n (histState n h) := by
  change policy ε n (h, ()) = (bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one ε)).bind
    fun b ↦ (uniformArm (K := K)).bind fun u ↦
      Measure.dirac (if b = true then u else RDoBandit.greedyArm (histState n h))
  rw [Set.projIcc_of_mem _ ε.2]
  rfl

/-- **ε-greedy has linear regret**, for the program that runs: the expected pseudo-regret of
`banditRunRand` with `epsGreedyArm`, against Gaussian arms, is at least `n ε / K ∑ₐ Δₐ`. -/
theorem le_integral_regret_banditRunRand (μ : Fin K → ℝ) (σ2 : ℝ≥0) (n : ℕ) :
    (n : ℝ) * ((ε : ℝ) / K) * ∑ a, gapOf μ a
      ≤ ∫ s, pseudoRegret μ s
          ∂(banditRunRand (m := Measure) (epsGreedyArm (m := Measure) (ε : ℝ)) μ σ2 n) := by
  rw [integral_pseudoRegret_banditRunRand μ σ2 (alg ε) _ (isMarkov_epsGreedyArm ε)
    (policy_eq_epsGreedyArm ε) n]
  have h := le_integral_regret ε (arms μ σ2)
    (IT.isAlgEnvSeq_trajMeasure (alg (K := K) ε) (stationaryEnv (arms μ σ2))) n
  simpa only [gap_arms] using h

end RDoBandit.EpsGreedy
