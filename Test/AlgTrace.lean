module

public import Test.Common

set_option linter.style.header false

/-!
# The algorithm-environment tactics on a toy algorithm

A toy sequential algorithm, to show the pipeline end to end: write the policy as an `rdo` program,
get its trace from `rdo_trace`, package it as an `AlgTrace`, and then read the algorithm's internal
draws off any algorithm-environment sequence, with `alg_env_trace`. The sections after that pin
down what the tactic does with the rest of the context, what it introduces, and the errors it
reports. The same algorithm then exercises `extend_space` alongside an algorithm-environment
sequence.

The algorithm is a bandit algorithm: it sees no observations, so its observation space is `Unit`.
-/

open MeasureTheory ProbabilityTheory Finset Learning RDo

@[expose] public section

noncomputable section

namespace Test.AlgTrace

universe u

variable {K : ℕ} (hK : 0 < K)

/-- The action of the last round of a history, or arm `0` before the first round. -/
def lastAction (n : ℕ) (h : Hist Unit (Fin K) ℝ n) : Fin K :=
  if hn : 0 < n then (h ⟨n - 1, by omega⟩).action else ⟨0, hK⟩

/-- The feedback of the last round of a history, or `0` before the first round. -/
def lastFeedback (n : ℕ) (h : Hist Unit (Fin K) ℝ n) : ℝ :=
  if hn : 0 < n then (h ⟨n - 1, by omega⟩).feedback else 0

@[fun_prop]
lemma measurable_lastAction (n : ℕ) : Measurable (lastAction hK n) := by
  unfold lastAction
  split_ifs <;> fun_prop

@[fun_prop]
lemma measurable_lastFeedback (n : ℕ) : Measurable (lastFeedback (K := K) n) := by
  unfold lastFeedback
  split_ifs <;> fun_prop

/-- The action, read off the history and the noise: depending on the sign of the noise, either
switch to arm `0` or repeat the last action. -/
def readout (n : ℕ) (p : (Hist Unit (Fin K) ℝ n × Unit) × ℝ) : Fin K :=
  if 0 < p.2 then ⟨0, hK⟩ else lastAction hK n p.1.1

@[fun_prop]
lemma measurable_readout (n : ℕ) : Measurable (readout hK n) := by
  unfold readout
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
    ((measurable_lastAction hK n).comp (measurable_fst.comp measurable_fst))

/-- The policy: perturb the last feedback by Gaussian noise, then read the action off it. -/
def policy (n : ℕ) (p : Hist Unit (Fin K) ℝ n × Unit) : Measure (Fin K) := rdo
  let z ← gaussianReal (lastFeedback n p.1) 1
  return readout hK n (p, z)

instance (n : ℕ) : IsMarkov (policy hK n) := by unfold policy; is_markov

/-- The noise the policy draws at step `n`, as a kernel: the one coordinate of its trace. -/
def noise (n : ℕ) : Kernel (Hist Unit (Fin K) ℝ n × Unit) ℝ :=
  markovKernel (fun p ↦ gaussianReal (lastFeedback n p.1) 1)
    (IsMarkov.gaussianReal (by fun_prop) measurable_const)

instance (n : ℕ) : IsMarkovKernel (noise (K := K) n) := by unfold noise; infer_instance

lemma hasTrace_policy (n : ℕ) : HasTrace (policy hK n) (noise n) (readout hK n) := by
  rdo_trace (policy hK n) with h
  exact h

/-- The algorithm. -/
def alg : Algorithm Unit (Fin K) ℝ where
  policy n := markovKernel (policy hK n) inferInstance

/-- Its trace: one Gaussian draw per step. -/
def trace : AlgTrace (alg hK) ℝ where
  K := noise
  out := readout hK
  hasTrace n := hasTrace_policy hK n

/-- **The payoff.** Given any algorithm-environment sequence for this algorithm, one may assume the
space also carries the noise `Z` the policy draws at each step: it has the conditional law `noise n`
given the history and the observation, and the action is `readout` of those and the noise. The
trajectory keeps the same law, so anything proved there about the observations, actions and
feedbacks holds of the original sequence. -/
theorem exists_noise (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type*} [MeasurableSpace Ω₀]
    {P : Measure Ω₀} [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K}
    {Y : ℕ → Ω₀ → ℝ} (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (O' : ℕ → Ω' → Unit) (A' : ℕ → Ω' → Fin K) (Y' : ℕ → Ω' → ℝ) (Z : ℕ → Ω' → ℝ),
      IsAlgEnvSeq O' A' Y' (alg hK) env P'
        ∧ P'.map (trajectory O' A' Y') = P.map (trajectory O A Y)
        ∧ (∀ n, HasCondDistrib (Z n) (fun ω ↦ (history O' A' Y' n ω, O' n ω)) (noise n) P')
        ∧ (∀ n, A' n =ᵐ[P'] fun ω ↦ readout hK n ((history O' A' Y' n ω, O' n ω), Z n ω)) := by
  obtain ⟨Ω', mΩ', P', hP', O', A', Y', Z, hseq, -, hlaw, hZ, hA⟩ :=
    (trace hK).exists_isAlgEnvSeq_trace h
  exact ⟨Ω', mΩ', P', hP', O', A', Y', Z, hseq, hlaw, hZ, hA⟩

/-- **The tactic at work.** `alg_env_trace` replaces the context and the goal by ones on a space
that also carries the noise `Z` the policy draws. The first action is arm `0`: whatever the noise,
the readout is arm `0` before the first round. The obligation that the statement only depends on
the law of the trajectory is discharged by `transfer` through the trajectory space, so only the
traced goal is left. -/
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    ∀ᵐ ω ∂P, A 0 ω = ⟨0, hK⟩ := by
  alg_env_trace (trace hK) with Ω P O A Y Z hseq htr hZ hA
  -- `Z`, `hZ` and `hA` are the algorithm's draws and their laws, now available.
  filter_upwards [hA 0] with ω hω
  rw [hω]
  simp [trace, readout, lastAction]

/-- Without `with`, the names are `Ω P O A Y T hseq htr hT hA`. -/
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    ∀ᵐ ω ∂P, A 0 ω = ⟨0, hK⟩ := by
  alg_env_trace (trace hK) using h
  guard_hyp hseq : IsAlgEnvSeq O A Y (alg hK) env P
  guard_hyp htr :
    IsAlgEnvSeq O (fun n ω ↦ (T n ω, A n ω)) Y (trace hK).algorithm (env.withTrace ℝ) P
  guard_hyp hT :
    ∀ n, HasCondDistrib (T n) (fun ω ↦ (history O A Y n ω, O n ω)) ((trace hK).K n) P
  guard_hyp hA :
    ∀ n, A n =ᵐ[P] fun ω ↦ (trace hK).out n ((history O A Y n ω, O n ω), T n ω)
  filter_upwards [hA 0] with ω hω
  rw [hω]
  simp [trace, readout, lastAction]

/-- **Using the draws.** The second action is either arm `0` or the first action, since it is the
readout of the noise and the history: a statement about the actions, proved from `hA` on the traced
space and transferred back to the original one. -/
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    ∀ᵐ ω ∂P, A 1 ω = ⟨0, hK⟩ ∨ A 1 ω = A 0 ω := by
  alg_env_trace (trace hK)
  filter_upwards [hA 1] with ω hω
  rw [hω]
  by_cases h0 : 0 < T 1 ω <;> simp [trace, readout, lastAction, history, h0]

/-- The space may live in any universe. -/
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type u} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    ∀ᵐ ω ∂P, A 0 ω = ⟨0, hK⟩ := by
  alg_env_trace (trace hK)
  filter_upwards [hA 0] with ω hω
  rw [hω]
  simp [trace, readout, lastAction]

/-! ## What travels with the goal, and what does not -/

/-- A hypothesis about the sequence travels with the goal, is available on the traced space, and
the obligation is still discharged. -/
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) (ν : Measure (Fin K)) (hA1 : P.map (A 1) = ν) :
    P.map (A 1) = ν := by
  alg_env_trace (trace hK)
  guard_hyp hA1 : P.map (A 1) = ν
  exact hA1

/-- Data on the space that the goal does not depend on — a random variable, a point, and what is
about them — is cleared: it has no counterpart on the traced space. The obligation is discharged. -/
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) (X : Ω₀ → ℝ) (_hX : Measurable X) (x : Ω₀)
    (_hx : X x = 0) :
    ∀ᵐ ω ∂P, A 0 ω = ⟨0, hK⟩ := by
  alg_env_trace (trace hK)
  fail_if_success guard_hyp X
  fail_if_success guard_hyp _hX
  fail_if_success guard_hyp x
  fail_if_success guard_hyp _hx
  filter_upwards [hA 0] with ω hω
  rw [hω]
  simp [trace, readout, lastAction]

/-- A statement `transfer` has no lemma for leaves the obligation, which is then proved by hand,
here trivially. -/
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    IsProbabilityMeasure P := by
  alg_env_trace (trace hK)
  case traced => infer_instance
  case transfer =>
    intro Ω₁ _ P₁ _ O₁ A₁ Y₁ Ω₂ _ P₂ _ O₂ A₂ Y₂ h₁ h₂ hlaw h₀
    infer_instance

/-! ## Errors -/

/-- Another algorithm, to check that a trace is matched against the algorithm of the hypothesis. -/
def alg2 : Algorithm Unit (Fin K) ℝ where
  policy _ := Kernel.const _ (Measure.dirac ⟨0, hK⟩)

/--
error: alg_env_trace: the goal depends on
  s
of type
  Set Ω₀
which lives on the space of the sequence without being part of it. Only statements about the actions, the feedbacks and the measure survive the change of space.
-/
#guard_msgs in
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) (s : Set Ω₀) (hs : P s = 1 / 2) : P s = 1 / 2 := by
  alg_env_trace (trace hK)

/--
error: alg_env_trace: no `IsAlgEnvSeq` hypothesis in the context
-/
#guard_msgs in
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] : P Set.univ = 1 := by
  alg_env_trace (trace hK)

/--
error: alg_env_trace: hP is not an `IsAlgEnvSeq` hypothesis
-/
#guard_msgs in
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] (hP : P Set.univ = 1) : P Set.univ = 1 := by
  alg_env_trace (trace hK) using hP

/--
error: alg_env_trace: the probability space must be given by local hypotheses, but ℕ → ℝ is not
-/
#guard_msgs in
example (env : Environment Unit (Fin K) ℝ) {P : Measure (ℕ → ℝ)} [IsProbabilityMeasure P]
    {O : ℕ → (ℕ → ℝ) → Unit} {A : ℕ → (ℕ → ℝ) → Fin K} {Y : ℕ → (ℕ → ℝ) → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    ∀ᵐ ω ∂P, A 0 ω = ⟨0, hK⟩ := by
  alg_env_trace (trace hK)

/--
error: alg_env_trace: the observation, action and feedback sequences must be local hypotheses, but fun n ω ↦ Y n ω + 0 is not
-/
#guard_msgs in
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A (fun n ω ↦ Y n ω + 0) (alg hK) env P) :
    ∀ᵐ ω ∂P, A 0 ω = ⟨0, hK⟩ := by
  alg_env_trace (trace hK)

/--
error: alg_env_trace: trace hK is not a trace of the algorithm of the hypothesis
-/
#guard_msgs in
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg2 hK) env P) :
    ∀ᵐ ω ∂P, A 0 ω = ⟨0, hK⟩ := by
  alg_env_trace (trace hK)

/--
error: alg_env_trace: at most 10 names may be given
-/
#guard_msgs in
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    ∀ᵐ ω ∂P, A 0 ω = ⟨0, hK⟩ := by
  alg_env_trace (trace hK) with a b c d e f g i j k l

/-! ## `extend_space` alongside an algorithm-environment sequence -/

/-- **`extend_space` alongside an algorithm-environment sequence.** After the extension, `Ω`, `P`,
`O`, `A` and `Y` live on a larger space that also carries a Gaussian `U` independent of the whole
trajectory, and `h` has been transported by `IsAlgEnvSeq.comp_measurePreserving`. The statement
does not mention the original space, so the `transfer` obligation is trivial and `extend_space`
closes it. The measurability of the sequence is put in the context first, so that the
independence statement `hind` covers `O`, `A` and `Y`. -/
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (O' : ℕ → Ω' → Unit) (A' : ℕ → Ω' → Fin K) (Y' : ℕ → Ω' → ℝ) (U : Ω' → ℝ),
      IsAlgEnvSeq O' A' Y' (alg hK) env P' ∧ HasLaw U (gaussianReal 0 1) P'
        ∧ IndepFun (trajectory O' A' Y') U P' := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  extend_space! (gaussianReal 0 1) using P with U hU hind
  have hOAY : IndepFun (trajectory O A Y) U P :=
    hind.comp (φ := fun (p : (ℕ → Unit) × (ℕ → Fin K) × (ℕ → ℝ)) (n : ℕ) ↦
      (p.1 n, p.2.1 n, p.2.2 n)) (by fun_prop) measurable_id
  exact ⟨Ω₀, inferInstance, P, inferInstance, O, A, Y, U, h, hU, hOAY⟩

/-- **The explicit form, `extend_space_map`.** The goal mentions the space through `P`, `O 0` and
`A 0`; `transfer` moves it to the new space, with the measurability of the sequence taken from `h`.
In the extended goal, `transfer hf at h` pulls the sequence back. -/
example (env : Environment Unit (Fin K) ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    [IsProbabilityMeasure P] {O : ℕ → Ω₀ → Unit} {A : ℕ → Ω₀ → Fin K} {Y : ℕ → Ω₀ → ℝ}
    (h : IsAlgEnvSeq O A Y (alg hK) env P) :
    HasCondDistrib (A 0) (O 0) (alg hK).p0 P := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  extend_space_map (gaussianReal 0 1) with Ω' P' f hf U hU hind
  transfer hf at h
  exact h.hasCondDistrib_action_zero

end Test.AlgTrace

end

end
