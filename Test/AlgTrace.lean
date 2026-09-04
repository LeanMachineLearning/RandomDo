module

public import Test.Common

set_option linter.style.header false

/-!
# The algorithm-environment tactics on a toy algorithm

A toy sequential algorithm, to show the pipeline end to end: write the policy as an `rdo` program,
get its trace from `rdo_trace`, package it as an `AlgTrace`, and then read the algorithm's internal
draws off any algorithm-environment sequence, with `alg_env_trace`. The same algorithm then
exercises `extend_space` alongside an algorithm-environment sequence.

To do the same for `thompson` one needs the measurable equivalence between `Iic n → 𝓐 × 𝓨` and
`Vector (𝓐 × 𝓨) (n + 1)` that turns it into a policy, which is not available yet. Everything after
that point is what follows below.
-/

open MeasureTheory ProbabilityTheory Finset Learning RDo

@[expose] public section

noncomputable section

namespace Test.AlgTrace

variable {K : ℕ} (hK : 0 < K)

/-- The action, read off the history and the noise: depending on the sign of the noise, either
switch to arm `0` or repeat the last action. -/
def readout (n : ℕ) (p : (Iic n → Fin K × ℝ) × ℝ) : Fin K :=
  if 0 < p.2 then ⟨0, hK⟩ else (p.1 ⟨n, by simp⟩).1

@[fun_prop]
lemma measurable_readout (n : ℕ) : Measurable (readout hK n) := by
  unfold readout
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
    (measurable_fst.comp ((measurable_pi_apply _).comp measurable_fst))

/-- The policy: perturb the last reward by Gaussian noise, then read the action off it. -/
def policy (n : ℕ) (h : Iic n → Fin K × ℝ) : Measure (Fin K) := rdo
  let z ← gaussianReal (h ⟨n, by simp⟩).2 1
  return readout hK n (h, z)

instance (n : ℕ) : IsMarkov (policy hK n) := by unfold policy; is_markov

/-- The noise the policy draws at step `n`, as a kernel: the one coordinate of its trace. -/
def noise (n : ℕ) : Kernel (Iic n → Fin K × ℝ) ℝ :=
  markovKernel (fun h ↦ gaussianReal (h ⟨n, by simp⟩).2 1)
    (IsMarkov.gaussianReal (by fun_prop) measurable_const)

instance (n : ℕ) : IsMarkovKernel (noise (K := K) n) := by unfold noise; infer_instance

lemma hasTrace_policy (n : ℕ) : HasTrace (policy hK n) (noise n) (readout hK n) := by
  rdo_trace (policy hK n) with h
  exact h

/-- The algorithm. -/
def alg : Algorithm (Fin K) ℝ where
  policy n := markovKernel (policy hK n) inferInstance
  p0 := Measure.dirac ⟨0, hK⟩

/-- Its trace: one Gaussian draw per step. -/
def trace : AlgTrace (alg hK) ℝ where
  K := noise
  out := readout hK
  hasTrace n := hasTrace_policy hK n
  K0 := gaussianReal 0 1
  out0 := fun _ ↦ ⟨0, hK⟩
  measurable_out0 := measurable_const
  map_out0 := by rw [Measure.map_const]; simp [alg]

/-- **The payoff.** Given any algorithm-environment sequence for this algorithm, one may assume the
space also carries the noise `Z` the policy draws at each step: it has the conditional law `noise n`
given the history, and the action is `readout` of the history and it. The trajectory keeps the same
law, so anything proved there about the actions and feedbacks holds of the original sequence. -/
theorem exists_noise (env : Environment (Fin K) ℝ) {Ω₀ : Type*} [MeasurableSpace Ω₀]
    {P : Measure Ω₀} [IsProbabilityMeasure P] {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq A Y (alg hK) env P) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (A' : ℕ → Ω' → Fin K) (Y' : ℕ → Ω' → ℝ) (Z : ℕ → Ω' → ℝ),
      IsAlgEnvSeq A' Y' (alg hK) env P'
        ∧ P'.map (trajectory A' Y') = P.map (trajectory A Y)
        ∧ (∀ n, HasCondDistrib (Z (n + 1)) (history A' Y' n) (noise n) P')
        ∧ (∀ n, A' (n + 1) =ᵐ[P'] fun ω ↦ readout hK n (history A' Y' n ω, Z (n + 1) ω)) := by
  obtain ⟨Ω', mΩ', P', hP', A', Y', Z, hseq, hlaw, -, hZ, -, hA⟩ :=
    (trace hK).exists_isAlgEnvSeq_trace h
  exact ⟨Ω', mΩ', P', hP', A', Y', Z, hseq, hlaw, hZ, hA⟩

/-- **The tactic at work.** `alg_env_trace` replaces the context and the goal by ones on a space
that also carries the noise `Z` the policy draws. The obligation that the statement only depends
on the law of the trajectory is discharged by `transfer` through the trajectory space, so only the
traced goal is left. Any hypothesis mentioning the space travels with the goal, so nothing is
silently lost. -/
example (env : Environment (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq A Y (alg hK) env P) :
    P.map (A 0) = Measure.dirac ⟨0, hK⟩ := by
  alg_env_trace (trace hK) with Ω P A Y Z hseq hZ₀ hZ hA₀ hA
  -- `Z`, `hZ₀`, `hZ` and `hA` are the algorithm's draws and their laws, now available.
  exact hseq.hasLaw_action_zero.map_eq

/-- A statement `transfer` has no lemma for leaves the obligation, which is then proved by hand,
here trivially. -/
example (env : Environment (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq A Y (alg hK) env P) :
    IsProbabilityMeasure P := by
  alg_env_trace (trace hK)
  case traced => infer_instance
  case transfer =>
    intro Ω₁ _ P₁ _ A₁ Y₁ Ω₂ _ P₂ _ A₂ Y₂ h₁ h₂ hlaw h₀
    infer_instance

/-- **`extend_space` alongside an algorithm-environment sequence.** After the extension, `Ω`, `P`,
`A` and `Y` live on a larger space that also carries a Gaussian `U` independent of the whole
trajectory, and `h` has been transported by `IsAlgEnvSeq.comp_measurePreserving`. The statement
does not mention the original space, so the `transfer` obligation is trivial and `extend_space`
closes it. The measurability of the sequence is put in the context first, so that the
independence statement `hind` covers `A` and `Y`. -/
example (env : Environment (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq A Y (alg hK) env P) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (A' : ℕ → Ω' → Fin K) (Y' : ℕ → Ω' → ℝ) (U : Ω' → ℝ),
      IsAlgEnvSeq A' Y' (alg hK) env P' ∧ HasLaw U (gaussianReal 0 1) P'
        ∧ IndepFun (trajectory A' Y') U P' := by
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  extend_space! (gaussianReal 0 1) using P with U hU hind
  have hAY : IndepFun (trajectory A Y) U P :=
    hind.comp (φ := fun (p : (ℕ → Fin K) × (ℕ → ℝ)) (n : ℕ) ↦ (p.1 n, p.2 n)) (by fun_prop)
      measurable_id
  exact ⟨Ω₀, inferInstance, P, inferInstance, A, Y, U, h, hU, hAY⟩

/-- **The explicit form, `extend_space_map`.** The goal mentions the space through `P` and `A 0`;
`transfer` moves it to the new space, with the measurability of the sequence taken from `h`. In
the extended goal, `transfer hf at h` pulls the sequence back. -/
example (env : Environment (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq A Y (alg hK) env P) :
    P.map (A 0) = Measure.dirac ⟨0, hK⟩ := by
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  extend_space_map (gaussianReal 0 1) with Ω' P' f hf U hU hind
  transfer hf at h
  exact h.hasLaw_action_zero.map_eq

end Test.AlgTrace

end

end
