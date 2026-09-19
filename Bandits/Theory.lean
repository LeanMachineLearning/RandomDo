/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Bandits.Defs
public import LeanMachineLearning.Online.Bandit.Algorithms.Regret.ETC
public import LeanMachineLearning.Online.Bandit.Algorithms.Regret.UCB

/-!
# The regret of the `rdo` bandit programs

LeanMachineLearning proves regret bounds for explore-then-commit and UCB, as statements about any
algorithm-environment sequence (`IsAlgEnvSeq`) for its algorithms `etcAlgorithm` and
`ucbAlgorithm`. This file carries them over to the programs of `Bandits.Defs`, read at `Measure`:
the expected pseudo-regret of the state `banditRun n` reaches is bounded as LeanMachineLearning
bounds the expected regret.

## The bridge

LeanMachineLearning's algorithms read the whole history; the programs read its *state*, the
number of pulls and the sum of the rewards of each arm and the last arm pulled (`histState`).

* `etcArm_histState`, `ucbArm_histState`: at `ℝ`, the arm the programs pull from the state of a
  history is the arm LeanMachineLearning's algorithms pull from the history.
* `histState_snoc`: the state of a history extended by one round is the state updated by it,
  which is what `banditStep` computes.
* `banditRun_eq_map`: **the law of the program**. For any algorithm reading the history through
  its state, `banditRun n` is the law of the state of the history of `n` rounds of the
  interaction, on LeanMachineLearning's trajectory space. The proof is an induction on `n`: the
  history of `n + 1` rounds is that of `n` rounds followed by a round drawn from the step kernel
  (`map_hist_succ`), and a round of a deterministic algorithm against Gaussian arms is the arm it
  chooses and a Gaussian reward (`map_stepKernel`).
* `integral_pseudoRegret_banditRun`: hence the expected pseudo-regret of the program is the
  expected regret of the interaction.

## Main results

* `integral_regret_etc_le`: the regret bound of explore-then-commit.
* `integral_regret_ucb_le`, `integral_regret_ucb_le_of_gt`: the regret bounds of UCB, the second
  logarithmic in the number of rounds when `c > 2 σ2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Finset
open scoped NNReal ENNReal

namespace RDoBandit

variable {K : ℕ} [NeZero K]

section Vector

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

@[fun_prop]
lemma measurable_vector_getElem (i : Fin n) : Measurable fun v : Vector α n ↦ v[i] :=
  (measurable_pi_apply i).comp Vector.measurableEquivTuple.measurable

lemma measurable_vector_iff {β : Type*} [MeasurableSpace β] {f : β → Vector α n} :
    Measurable f ↔ ∀ i : Fin n, Measurable fun b ↦ (f b)[i] :=
  ⟨fun hf i ↦ (measurable_vector_getElem i).comp hf,
    fun h ↦ by
      have h' : Measurable fun b ↦ Vector.ofFn fun i : Fin n ↦ (f b)[i] :=
        Vector.measurableEquivTuple.symm.measurable.comp (measurable_pi_iff.2 h)
      simpa using h'⟩

@[fun_prop]
lemma measurable_vector_ofFn {β : Type*} [MeasurableSpace β] {f : β → Fin n → α}
    (hf : ∀ i, Measurable fun b ↦ f b i) : Measurable fun b ↦ Vector.ofFn (f b) :=
  measurable_vector_iff.2 fun i ↦ by simpa using hf i

end Vector

/-- The last arm of a history, arm `0` before the first round. -/
noncomputable def lastArm (n : ℕ) (h : Hist Unit (Fin K) ℝ n) : Fin K :=
  if hn : 0 < n then (h ⟨n - 1, by omega⟩).action else 0

/-- The state of a history: the number of pulls of each arm, the sum of its rewards, and the last
arm pulled. -/
noncomputable def histState (n : ℕ) (h : Hist Unit (Fin K) ℝ n) : State K ℝ :=
  (Vector.ofFn (pullCount' n h), Vector.ofFn (sumRewards' n h), lastArm n h)

@[fun_prop]
lemma measurable_lastArm (n : ℕ) : Measurable (lastArm (K := K) n) := by
  unfold lastArm
  split_ifs <;> fun_prop

@[fun_prop]
lemma measurable_histState (n : ℕ) : Measurable (histState (K := K) n) := by
  unfold histState
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ (measurable_lastArm n))
  · exact measurable_vector_ofFn fun a ↦ measurable_pullCount' n a
  · exact measurable_vector_ofFn fun a ↦ measurable_sumRewards' n a

lemma histState_zero (h : Hist Unit (Fin K) ℝ 0) : histState 0 h = State.init := by
  simp only [histState, State.init, lastArm, lt_self_iff_false, dite_false, Prod.mk.injEq,
    and_true]
  constructor <;> ext <;> simp [pullCount'_eq_sum, sumRewards']

omit [NeZero K] in
lemma pullCount'_snoc (n : ℕ) (h : Hist Unit (Fin K) ℝ n) (a b : Fin K) (r : ℝ) :
    pullCount' (n + 1) (Fin.snoc h ((), a, r)) b = pullCount' n h b + if a = b then 1 else 0 := by
  rw [pullCount'_eq_sum, pullCount'_eq_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

omit [NeZero K] in
lemma sumRewards'_snoc (n : ℕ) (h : Hist Unit (Fin K) ℝ n) (a b : Fin K) (r : ℝ) :
    sumRewards' (n + 1) (Fin.snoc h ((), a, r)) b = sumRewards' n h b + if a = b then r else 0 := by
  rw [sumRewards', sumRewards', Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma histState_snoc (n : ℕ) (h : Hist Unit (Fin K) ℝ n) (a : Fin K) (r : ℝ) :
    histState (n + 1) (Fin.snoc h ((), a, r)) = (histState n h).update a r := by
  simp only [histState, State.update, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · ext i hi
    rw [Vector.getElem_ofFn, pullCount'_snoc, Vector.getElem_set]
    by_cases hai : (a : ℕ) = i
    · obtain rfl : a = ⟨i, hi⟩ := Fin.ext hai
      simp
    · have : a ≠ ⟨i, hi⟩ := fun h ↦ hai (congrArg Fin.val h)
      simp [hai, this]
  · ext i hi
    rw [Vector.getElem_ofFn, sumRewards'_snoc, Vector.getElem_set]
    by_cases hai : (a : ℕ) = i
    · obtain rfl : a = ⟨i, hi⟩ := Fin.ext hai
      simp
    · have : a ≠ ⟨i, hi⟩ := fun h ↦ hai (congrArg Fin.val h)
      simp [hai, this]
  · simp [lastArm, Fin.snoc, Fin.last]

lemma etcArm_histState (m n : ℕ) (h : Hist Unit (Fin K) ℝ n) :
    etcArm m n (histState n h) = ETC.nextArm K m n h := by
  unfold etcArm ETC.nextArm
  split_ifs with h1 h2
  · rfl
  · simp only [histState, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
    rfl
  · simp [histState, lastArm, show 0 < n by omega]

lemma ucbArm_histState (c : ℝ) (n : ℕ) (h : Hist Unit (Fin K) ℝ n) :
    ucbArm c n (histState n h) = UCB.nextArm K c n h := by
  unfold ucbArm UCB.nextArm
  split_ifs
  · rfl
  · simp only [histState, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
    rfl

section Measures

open MeasurableSpacePure MeasurableSpaceBind

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Mapping a composition-product is binding the kernel, mapped along the section. -/
lemma map_compProd_eq_bind (ρ : Measure α) [SFinite ρ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {F : α × β → γ} (hF : Measurable F) :
    (ρ ⊗ₘ κ).map F = ρ.bind fun a ↦ (κ a).map fun b ↦ F (a, b) := by
  have hmap (a : α) {t : Set γ} (ht : MeasurableSet t) :
      ((κ a).map fun b ↦ F (a, b)) t = κ a (Prod.mk a ⁻¹' (F ⁻¹' t)) :=
    Measure.map_apply (hF.comp measurable_prodMk_left) ht
  have hmeas : Measurable fun a ↦ (κ a).map fun b ↦ F (a, b) := by
    refine Measure.measurable_of_measurable_coe _ fun t ht ↦ ?_
    simp_rw [hmap _ ht]
    exact Kernel.measurable_kernel_prodMk_left (hF ht)
  ext s hs
  rw [Measure.map_apply hF hs, Measure.compProd_apply (hF hs),
    Measure.bind_apply hs hmeas.aemeasurable]
  simp_rw [hmap _ hs]

lemma dirac_compProd_eq_map [MeasurableSingletonClass α] (a : α) (κ : Kernel α β)
    [IsSFiniteKernel κ] : Measure.dirac a ⊗ₘ κ = (κ a).map (Prod.mk a) := by
  ext s hs
  rw [Measure.dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]

/-- Binding after mapping is binding the composite. -/
lemma bind_map_eq (ρ : Measure α) {f : α → β} (hf : Measurable f) {g : β → Measure γ}
    (hg : Measurable g) : (ρ.map f).bind g = ρ.bind (g ∘ f) := by
  ext s hs
  have hgs : Measurable fun b ↦ g b s := (Measure.measurable_coe hs).comp hg
  rw [Measure.bind_apply hs hg.aemeasurable, Measure.bind_apply hs (hg.comp hf).aemeasurable,
    lintegral_map hgs hf]
  rfl

end Measures

section Arms

variable (μ : Fin K → ℝ) (σ2 : ℝ≥0)

/-- The arms, as a Markov kernel: arm `a` returns rewards drawn from `𝒩(μ a, σ2)`. -/
noncomputable def arms : Kernel (Fin K) ℝ where
  toFun a := gaussianReal (μ a) σ2
  measurable' := measurable_of_countable _

omit [NeZero K] in
lemma arms_apply (a : Fin K) : arms μ σ2 a = gaussianReal (μ a) σ2 := rfl

instance : IsMarkovKernel (arms μ σ2) := ⟨fun a ↦ by rw [arms_apply]; infer_instance⟩

omit [NeZero K] in
lemma integral_arms (a : Fin K) : ∫ x, x ∂(arms μ σ2 a) = μ a := by
  simp [arms_apply, integral_id_gaussianReal]

/-- The gap of an arm: how much less its mean is than the best one. -/
noncomputable def gapOf (a : Fin K) : ℝ := (⨆ i, μ i) - μ a

omit [NeZero K] in
lemma gap_arms (a : Fin K) : gap (arms μ σ2) a = gapOf μ a := by
  simp [gap, gapOf, integral_arms]

omit [NeZero K] in
/-- Gaussian rewards are sub-Gaussian, with variance proxy their variance. -/
lemma hasSubgaussianMGF_arms (a : Fin K) :
    HasSubgaussianMGF (fun x ↦ x - (arms μ σ2 a)[id]) σ2 (arms μ σ2 a) := by
  rw [show (arms μ σ2 a)[id] = μ a from integral_arms μ σ2 a, arms_apply]
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · have := (integrable_exp_mul_gaussianReal (μ := μ a) (v := σ2) t).const_mul
      (Real.exp (-(t * μ a)))
    refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [← Real.exp_add]
    ring_nf
  · rw [mgf_gaussianReal ⟨by fun_prop, gaussianReal_map_sub_const (μ a)⟩ t]
    simp

end Arms

section Law

open MeasurableSpacePure MeasurableSpaceBind

variable (μ : Fin K → ℝ) (σ2 : ℝ≥0)

omit [NeZero K] in
lemma getElem_set_fin {α : Type*} (v : Vector α K) (a b : Fin K) (x : α) :
    (v.set a x)[b] = if a = b then x else v[b] := by
  simp only [Fin.getElem_fin, Vector.getElem_set, Fin.ext_iff]

omit [NeZero K] in
/-- For a fixed arm, updating the state is measurable in the state and the reward. -/
lemma measurable_update_const (a : Fin K) :
    Measurable fun p : State K ℝ × ℝ ↦ p.1.update a p.2 := by
  refine Measurable.prodMk (measurable_vector_iff.2 fun i ↦ ?_)
    (Measurable.prodMk (measurable_vector_iff.2 fun i ↦ ?_) measurable_const)
  · simp only [getElem_set_fin]
    split_ifs
    · exact (measurable_of_countable (· + 1 : ℕ → ℕ)).comp (by fun_prop)
    · fun_prop
  · simp only [getElem_set_fin]
    split_ifs <;> fun_prop

omit [NeZero K] in
@[fun_prop]
lemma Measurable.stateUpdate {X : Type*} [MeasurableSpace X] {f : X → State K ℝ}
    {g : X → Fin K} {r : X → ℝ} (hf : Measurable f) (hg : Measurable g) (hr : Measurable r) :
    Measurable fun x ↦ (f x).update (g x) (r x) := by
  have h : Measurable fun q : (State K ℝ × ℝ) × Fin K ↦ q.1.1.update q.2 q.1.2 :=
    measurable_from_prod_countable_left fun a ↦ measurable_update_const a
  exact h.comp ((hf.prodMk hr).prodMk hg)

variable {μ σ2}

omit [NeZero K] in
/-- At `Measure`, one round is the law of the reward of the chosen arm, mapped by the update. -/
lemma banditStep_eq (arm : ℕ → State K ℝ → Fin K) (n : ℕ) (s : State K ℝ) :
    banditStep (m := Measure) arm μ σ2 n s
      = (gaussianReal (μ (arm n s)) σ2).map (s.update (arm n s)) := by
  change (gaussianReal (μ (arm n s)) σ2).bind (fun r ↦ Measure.dirac (s.update (arm n s) r)) = _
  rw [Measure.bind_dirac_eq_map _ (by fun_prop)]

lemma banditRun_succ (arm : ℕ → State K ℝ → Fin K) (n : ℕ) :
    banditRun (m := Measure) arm μ σ2 (n + 1)
      = (banditRun (m := Measure) arm μ σ2 n).bind (banditStep (m := Measure) arm μ σ2 n) := by
  rw [banditRun]
  rfl

omit [NeZero K] in
lemma measurable_banditStep {arm : ℕ → State K ℝ → Fin K} {n : ℕ} (harm : Measurable (arm n)) :
    Measurable (banditStep (m := Measure) arm μ σ2 n) := by
  have hk : IsMarkov fun s ↦ gaussianReal (μ (arm n s)) σ2 :=
    IsMarkov.gaussianReal ((measurable_of_countable μ).comp harm) measurable_const
  have hu : Measurable fun p : State K ℝ × ℝ ↦ p.1.update (arm n p.1) p.2 := by fun_prop
  refine Measure.measurable_of_measurable_coe _ fun t ht ↦ ?_
  have hmap (s : State K ℝ) : (banditStep (m := Measure) arm μ σ2 n s) t
      = IsMarkov.toKernel (fun s ↦ gaussianReal (μ (arm n s)) σ2) s
          (Prod.mk s ⁻¹' ((fun p : State K ℝ × ℝ ↦ p.1.update (arm n p.1) p.2) ⁻¹' t)) := by
    rw [banditStep_eq, Measure.map_apply (by fun_prop) ht]
    rfl
  simp_rw [hmap]
  exact Kernel.measurable_kernel_prodMk_left (hu ht)

omit [NeZero K] in
lemma measurable_snoc {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable fun p : (Fin n → X) × X ↦ (Fin.snoc p.1 p.2 : Fin (n + 1) → X) := by
  refine Measurable.of_eval fun i ↦ ?_
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Fin.snoc_last]
    exact measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

omit [NeZero K] in
lemma hist_succ_eq (n : ℕ) :
    IT.hist (𝓞 := Unit) (𝓐 := Fin K) (𝓨 := ℝ) (n + 1)
      = fun ω ↦ Fin.snoc (IT.hist n ω) (IT.step n ω) := by
  funext ω i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [IT.hist, IT.step]
  · simp [IT.hist]

omit [NeZero K] in
/-- The history after `n + 1` rounds is the history after `n` rounds, followed by one round drawn
from the step kernel. -/
lemma map_hist_succ {γ : Type*} [MeasurableSpace γ] (alg : Algorithm Unit (Fin K) ℝ)
    (env : Environment Unit (Fin K) ℝ) (n : ℕ) {F : Hist Unit (Fin K) ℝ (n + 1) → γ}
    (hF : Measurable F) :
    (trajMeasure alg env).map (F ∘ IT.hist (n + 1))
      = ((trajMeasure alg env).map (IT.hist n)).bind
          fun h ↦ (stepKernel alg env n h).map fun x ↦ F (Fin.snoc h x) := by
  have e : F ∘ IT.hist (n + 1)
      = (fun p ↦ F (Fin.snoc p.1 p.2)) ∘ (fun ω ↦ (IT.hist n ω, IT.step n ω)) := by
    rw [hist_succ_eq]
    rfl
  rw [e, ← Measure.map_map (g := fun p ↦ F (Fin.snoc p.1 p.2))
    (f := fun ω ↦ (IT.hist n ω, IT.step n ω)) (hF.comp (measurable_snoc n)) (by fun_prop),
    (IT.hasCondDistrib_step alg env n).map_eq,
    map_compProd_eq_bind (F := fun p ↦ F (Fin.snoc p.1 p.2)) _ _ (hF.comp (measurable_snoc n))]

variable {nextA : (n : ℕ) → Hist Unit (Fin K) ℝ n × Unit → Fin K}
  {hnext : ∀ n, Measurable (nextA n)}

omit [NeZero K] in
/-- One round of a deterministic algorithm against the Gaussian arms: the chosen arm, then its
reward. -/
lemma map_stepKernel {γ : Type*} [MeasurableSpace γ] (n : ℕ) (h : Hist Unit (Fin K) ℝ n)
    {G : Round Unit (Fin K) ℝ → γ} (hG : Measurable G) :
    (stepKernel (detAlgorithm nextA hnext) (stationaryEnv (arms μ σ2)) n h).map G
      = (gaussianReal (μ (nextA n (h, ()))) σ2).map fun r ↦ G ((), nextA n (h, ()), r) := by
  rw [stepKernel_stationaryEnv, Kernel.compProd_apply_eq_compProd_sectR, Kernel.const_apply,
    Measure.dirac_unit_compProd, Kernel.sectR_apply, Kernel.compProd_apply_eq_compProd_sectR,
    detAlgorithm_policy, Kernel.deterministic_apply, dirac_compProd_eq_map, Kernel.sectR_apply,
    Kernel.prodMkLeft_apply, arms_apply, Measure.map_map hG measurable_prodMk_left,
    Measure.map_map (hG.comp measurable_prodMk_left) measurable_prodMk_left]
  rfl

/-- **The law of the program.** For an algorithm that reads the history only through its state,
the state after `n` rounds of `banditRun` has the law of the state of the history of `n` rounds of
LeanMachineLearning's algorithm-environment interaction. -/
theorem banditRun_eq_map (arm : ℕ → State K ℝ → Fin K) (harm_meas : ∀ n, Measurable (arm n))
    (harm : ∀ n h, arm n (histState n h) = nextA n (h, ())) (n : ℕ) :
    banditRun (m := Measure) arm μ σ2 n
      = (trajMeasure (detAlgorithm nextA hnext) (stationaryEnv (arms μ σ2))).map
          (histState n ∘ IT.hist n) := by
  induction n with
  | zero =>
    have : histState 0 ∘ IT.hist (𝓞 := Unit) (𝓐 := Fin K) (𝓨 := ℝ) 0 = fun _ ↦ State.init := by
      funext ω
      exact histState_zero _
    rw [this, Measure.map_const, measure_univ, one_smul]
    rfl
  | succ n ih =>
    rw [banditRun_succ, ih, map_hist_succ _ _ n (measurable_histState (n + 1)),
      ← Measure.map_map (measurable_histState n) (IT.measurable_hist n),
      bind_map_eq _ (measurable_histState n) (measurable_banditStep (harm_meas n))]
    congr 1
    funext h
    have hG : Measurable fun x ↦ histState (n + 1) (Fin.snoc h x) :=
      (measurable_histState (n + 1)).comp ((measurable_snoc n).comp
        (measurable_const.prodMk measurable_id))
    rw [Function.comp_apply, banditStep_eq, map_stepKernel n h hG, harm]
    simp_rw [histState_snoc]

end Law

section RandomizedLaw

/-! ### Algorithms drawing their arm

The same statement for an algorithm whose policy, at `Measure`, is a program drawing the arm from
the state: the step kernel then binds over the arm the policy draws, instead of taking the one it
chooses. -/

variable {μ : Fin K → ℝ} {σ2 : ℝ≥0}

instance (s : ℝ≥0) : IsMarkov fun x : ℝ ↦ gaussianReal x s :=
  IsMarkov.gaussianReal measurable_id measurable_const

omit [NeZero K] in
/-- At `Measure`, one round is the arm drawn by the policy, then its reward, mapped by the
update. -/
lemma banditStepRand_eq (arm : ℕ → State K ℝ → Measure (Fin K)) (n : ℕ) (s : State K ℝ) :
    banditStepRand (m := Measure) arm μ σ2 n s
      = (arm n s).bind fun a ↦ (gaussianReal (μ a) σ2).map (s.update a) := by
  change (arm n s).bind (fun a ↦ (gaussianReal (μ a) σ2).bind
    (fun r ↦ Measure.dirac (s.update a r))) = _
  congr with a : 1
  rw [Measure.bind_dirac_eq_map _ (by fun_prop)]

lemma banditRunRand_succ (arm : ℕ → State K ℝ → Measure (Fin K)) (n : ℕ) :
    banditRunRand (m := Measure) arm μ σ2 (n + 1)
      = (banditRunRand (m := Measure) arm μ σ2 n).bind
          (banditStepRand (m := Measure) arm μ σ2 n) := by
  rw [banditRunRand]
  rfl

omit [NeZero K] in
lemma isMarkov_banditStepRand {arm : ℕ → State K ℝ → Measure (Fin K)} {n : ℕ}
    (harm : IsMarkov (arm n)) : IsMarkov (banditStepRand (m := Measure) arm μ σ2 n) := by
  have hμ : Measurable μ := measurable_of_countable μ
  unfold banditStepRand
  is_markov

omit [NeZero K] in
/-- One round of an algorithm against the Gaussian arms: the arm its policy draws, then the reward
of that arm. -/
lemma map_stepKernel_bind {γ : Type*} [MeasurableSpace γ] (alg : Algorithm Unit (Fin K) ℝ)
    (n : ℕ) (h : Hist Unit (Fin K) ℝ n) {G : Round Unit (Fin K) ℝ → γ} (hG : Measurable G) :
    (stepKernel alg (stationaryEnv (arms μ σ2)) n h).map G
      = (alg.policy n (h, ())).bind fun a ↦ (gaussianReal (μ a) σ2).map fun r ↦ G ((), a, r) := by
  rw [stepKernel_stationaryEnv, Kernel.compProd_apply_eq_compProd_sectR, Kernel.const_apply,
    Measure.dirac_unit_compProd, Kernel.sectR_apply, Kernel.compProd_apply_eq_compProd_sectR,
    Measure.map_map hG measurable_prodMk_left,
    map_compProd_eq_bind _ _ (hG.comp measurable_prodMk_left)]
  rfl

/-- **The law of the program**, for an algorithm drawing its arm. If, at every round, the policy
of `alg` on a history is the program `arm` on the state of that history, then the state after `n`
rounds of `banditRunRand` has the law of the state of the history of `n` rounds of the
interaction of `alg` with the Gaussian arms. -/
theorem banditRunRand_eq_map (alg : Algorithm Unit (Fin K) ℝ)
    (arm : ℕ → State K ℝ → Measure (Fin K)) (harm_markov : ∀ n, IsMarkov (arm n))
    (harm : ∀ n h, alg.policy n (h, ()) = arm n (histState n h)) (n : ℕ) :
    banditRunRand (m := Measure) arm μ σ2 n
      = (trajMeasure alg (stationaryEnv (arms μ σ2))).map (histState n ∘ IT.hist n) := by
  induction n with
  | zero =>
    have : histState 0 ∘ IT.hist (𝓞 := Unit) (𝓐 := Fin K) (𝓨 := ℝ) 0 = fun _ ↦ State.init := by
      funext ω
      exact histState_zero _
    rw [this, Measure.map_const, measure_univ, one_smul]
    rfl
  | succ n ih =>
    rw [banditRunRand_succ, ih, map_hist_succ _ _ n (measurable_histState (n + 1)),
      ← Measure.map_map (measurable_histState n) (IT.measurable_hist n),
      bind_map_eq _ (measurable_histState n) (isMarkov_banditStepRand (harm_markov n)).measurable]
    congr 1
    funext h
    have hG : Measurable fun x ↦ histState (n + 1) (Fin.snoc h x) :=
      (measurable_histState (n + 1)).comp ((measurable_snoc n).comp
        (measurable_const.prodMk measurable_id))
    rw [Function.comp_apply, banditStepRand_eq, map_stepKernel_bind alg n h hG, harm]
    simp_rw [histState_snoc]

end RandomizedLaw

section Regret

variable (μ : Fin K → ℝ) (σ2 : ℝ≥0)

/-- The pseudo-regret of a state: the number of pulls of each arm, times its gap. -/
noncomputable def pseudoRegret (s : State K ℝ) : ℝ := ∑ a, ((s.1[a] : ℕ) : ℝ) * gapOf μ a

omit [NeZero K] in
@[fun_prop]
lemma measurable_pseudoRegret : Measurable (pseudoRegret (K := K) μ) := by
  unfold pseudoRegret
  refine Finset.measurable_sum _ fun a _ ↦ ?_
  exact ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
    ((measurable_vector_getElem a).comp measurable_fst)).mul_const _

/-- The regret of the interaction is the pseudo-regret of the state of its history. -/
lemma regret_eq_pseudoRegret (n : ℕ) (ω : ℕ → Round Unit (Fin K) ℝ) :
    regret (arms μ σ2) IT.action n ω = pseudoRegret μ (histState n (IT.hist n ω)) := by
  rw [regret_eq_sum_pullCount_mul_gap]
  simp only [pseudoRegret, histState, Fin.getElem_fin, Vector.getElem_ofFn, gap_arms]
  congr with a
  rw [pullCount_eq_pullCount' (O := IT.obs) (R' := IT.feedback), IT.history_obs_action_feedback]

variable {nextA : (n : ℕ) → Hist Unit (Fin K) ℝ n × Unit → Fin K}
  {hnext : ∀ n, Measurable (nextA n)}

/-- **The expected pseudo-regret of the program is the expected regret of the interaction.** -/
theorem integral_pseudoRegret_banditRun (arm : ℕ → State K ℝ → Fin K)
    (harm_meas : ∀ n, Measurable (arm n)) (harm : ∀ n h, arm n (histState n h) = nextA n (h, ()))
    (n : ℕ) :
    ∫ s, pseudoRegret μ s ∂(banditRun (m := Measure) arm μ σ2 n)
      = (trajMeasure (detAlgorithm nextA hnext) (stationaryEnv (arms μ σ2)))[
          regret (arms μ σ2) IT.action n] := by
  rw [banditRun_eq_map (hnext := hnext) arm harm_meas harm n,
    integral_map (by fun_prop) (measurable_pseudoRegret μ).aestronglyMeasurable]
  congr with ω
  exact (regret_eq_pseudoRegret μ σ2 n ω).symm

omit [NeZero K] in
@[fun_prop]
lemma measurable_hasArgmax_real [NeZero K] :
    Measurable (HasArgmax.argmax : (Fin K → ℝ) → Fin K) := measurable_argmax

omit [NeZero K] in
@[fun_prop]
lemma measurable_count (a : Fin K) : Measurable fun s : State K ℝ ↦ ((s.1[a] : ℕ) : ℝ) :=
  (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
    ((measurable_vector_getElem a).comp measurable_fst)

lemma measurable_etcArm (m n : ℕ) : Measurable (etcArm (K := K) (R := ℝ) m n) := by
  unfold etcArm
  split_ifs
  · exact measurable_const
  · exact measurable_hasArgmax_real.comp (measurable_pi_iff.2 fun a ↦ by fun_prop)
  · fun_prop

lemma measurable_ucbArm (c : ℝ) (n : ℕ) : Measurable (ucbArm (K := K) (R := ℝ) c n) := by
  unfold ucbArm
  split_ifs
  · exact measurable_const
  · exact measurable_hasArgmax_real.comp (measurable_pi_iff.2 fun a ↦ by fun_prop)

/-- **Regret of explore-then-commit.** The bound of `Bandits.ETC.regret_le`, for the program. -/
theorem integral_regret_etc_le {m : ℕ} (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    ∫ s, pseudoRegret μ s ∂(banditRun (m := Measure) (etcArm m) μ σ2 n)
      ≤ ∑ a, gapOf μ a * (m + (n - K * m) * Real.exp (- (m : ℝ) * gapOf μ a ^ 2 / (4 * σ2))) := by
  have h := ETC.regret_le
    (IT.isAlgEnvSeq_trajMeasure (etcAlgorithm K m) (stationaryEnv (arms μ σ2)))
    (hasSubgaussianMGF_arms μ σ2) hm n hn
  simp only [gap_arms] at h
  rw [integral_pseudoRegret_banditRun μ σ2 (hnext := fun n ↦ ETC.measurable_nextArm m n |>.comp
    measurable_fst) (etcArm m) (measurable_etcArm m) (fun n h ↦ etcArm_histState m n h) n]
  exact h

/-- **Regret of UCB.** The bound of `Bandits.UCB.regret_le'`, for the program. -/
theorem integral_regret_ucb_le {c : ℝ} (hc : 0 < c) (hσ2 : σ2 ≠ 0) (n : ℕ) :
    ∫ s, pseudoRegret μ s ∂(banditRun (m := Measure) (ucbArm c) μ σ2 n)
      ≤ ∑ a, (8 * c * Real.log (n + 1) / gapOf μ a
        + gapOf μ a * (2 + 2 * UCB.constSum (c / σ2) n)) := by
  have h := UCB.regret_le'
    (IT.isAlgEnvSeq_trajMeasure (ucbAlgorithm K c) (stationaryEnv (arms μ σ2)))
    (hasSubgaussianMGF_arms μ σ2) hσ2 hc n
  simp only [gap_arms] at h
  rw [integral_pseudoRegret_banditRun μ σ2 (hnext := fun n ↦ UCB.measurable_nextArm c n |>.comp
    measurable_fst) (ucbArm c) (measurable_ucbArm c) (fun n h ↦ ucbArm_histState c n h) n]
  exact h

/-- **Regret of UCB**, for `c > 2 σ2`: logarithmic in the number of rounds. -/
theorem integral_regret_ucb_le_of_gt {c : ℝ} (hc : 2 * σ2 < c) (hσ2 : σ2 ≠ 0) (n : ℕ) :
    ∫ s, pseudoRegret μ s ∂(banditRun (m := Measure) (ucbArm c) μ σ2 n)
      ≤ ∑ a, (8 * c * Real.log (n + 1) / gapOf μ a
        + gapOf μ a * (4 + 2 * σ2 / (c - 2 * σ2))) := by
  have h := UCB.regret_le_of_gt_two'
    (IT.isAlgEnvSeq_trajMeasure (ucbAlgorithm K c) (stationaryEnv (arms μ σ2)))
    (hasSubgaussianMGF_arms μ σ2) hσ2 hc n
  simp only [gap_arms] at h
  rw [integral_pseudoRegret_banditRun μ σ2 (hnext := fun n ↦ UCB.measurable_nextArm c n |>.comp
    measurable_fst) (ucbArm c) (measurable_ucbArm c) (fun n h ↦ ucbArm_histState c n h) n]
  exact h

/-- **The expected pseudo-regret of the program is the expected regret of the interaction**, for an
algorithm drawing its arm. -/
theorem integral_pseudoRegret_banditRunRand (alg : Algorithm Unit (Fin K) ℝ)
    (arm : ℕ → State K ℝ → Measure (Fin K)) (harm_markov : ∀ n, IsMarkov (arm n))
    (harm : ∀ n h, alg.policy n (h, ()) = arm n (histState n h)) (n : ℕ) :
    ∫ s, pseudoRegret μ s ∂(banditRunRand (m := Measure) arm μ σ2 n)
      = (trajMeasure alg (stationaryEnv (arms μ σ2)))[regret (arms μ σ2) IT.action n] := by
  rw [banditRunRand_eq_map alg arm harm_markov harm n,
    integral_map (by fun_prop) (measurable_pseudoRegret μ).aestronglyMeasurable]
  congr with ω
  exact (regret_eq_pseudoRegret μ σ2 n ω).symm

end Regret

end RDoBandit
