/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Monad.While
public import RandomDo.Tactic.IsMarkov.Elab
public import RandomDo.ForMathlib.Algebra.Notation.Indicator
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Termination of `while` loops

`is_markov` hands back the termination of a `while` loop as a goal `Terminates f b`. This file
implements proof rules of the literature for it, each under the name of its authors and with the
hypotheses of its paper, translated as described in the implementation notes.

## Main results

* `Terminates.mcIverMorgan_variantRule`, `Terminates.mcIverMorgan_variantRule_of_finite`: the
  variant rule for loops of McIver and Morgan (2005, Lemmas 7.5.1 and 2.7.1).
* `Terminates.mcIverMorgan_variantRule_of_antitone`: its form with a variant that cannot increase
  (McIver and Morgan 2005, p. 56).
* `Terminates.mcIverMorganKaminskiKatoen`: the new variant rule for loops of McIver, Morgan,
  Kaminski and Katoen (POPL 2018, Theorem 4.1).
* `Terminates.majumdarSathiyanarayana_variantRule`: the variant rule of McIver and Morgan, as
  presented by Majumdar and Sathiyanarayana for probabilistic transition systems (POPL 2025, Proof
  Rule 3.1).
* `Terminates.majumdarSathiyanarayana_martingaleRule`: the martingale rule of Majumdar and
  Sathiyanarayana (POPL 2025, Proof Rule 3.2).
* `bournezGarnier`: the Lyapunov ranking functions of Bournez and Garnier (RTA 2005, Theorem 2),
  which give almost-sure termination with a bound on the expected number of steps.

## Implementation notes

The rules are stated for the two program models of their papers.
* A loop `while G do body` of pGCL is `whileStep G body`, whose body is a Markov kernel. The weakest
  pre-expectation `wp.body.E` at `s` is the integral of `E` against `body s`, which for a predicate
  `P` is the probability `body s {s' | P s'}`.
* A probabilistic transition system (a control flow graph, a probabilistic program) is the system
  whose states are the `ForInStep σ`: the successor of `yield s` is drawn from `f s`, and the states
  `done s` are terminal. Every `rdo` loop is of this form.

The programs have no demonic nondeterminism, one step of a transition system is one iteration of the
loop, and "every successor" is "almost every successor". The papers state these rules for discrete
probabilistic choice (countable state spaces or discrete distributions); the rules here hold for any
measurable state space and any Markov kernel, and their measurability conditions, which a discrete
state space satisfies, have default proofs.

## References

* Annabelle McIver, Carroll Morgan, *Abstraction, Refinement and Proof for Probabilistic Systems*,
  2005.
* Annabelle McIver, Carroll Morgan, Benjamin Lucien Kaminski, Joost-Pieter Katoen, *A New Proof Rule
  for Almost-Sure Termination*, POPL 2018.
* Rupak Majumdar, V. R. Sathiyanarayana, *Sound and Complete Proof Rules for Probabilistic
  Termination*, POPL 2025.
* Olivier Bournez, Florent Garnier, *Proving Positive Almost-Sure Termination*, RTA 2005.
* Luis María Ferrer Fioriti, Holger Hermanns, *Probabilistic Termination: Soundness, Completeness,
  and Compositionality*, POPL 2015.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

/- The probabilities in the rules are read in `ℝ` through `ENNReal.toReal`: pushing it through the
sums of finite probabilities lets `norm_num` compute them. -/
attribute [simp] ENNReal.toReal_add

namespace MeasurableSpaceMonadWhile

universe u

variable {σ : Type u} [MeasurableSpace σ] {f : σ → Measure (ForInStep σ)} {b : σ}

/-! ### Geometric decay on an invariant -/

private lemma loopRun_add_apply_univ_le [hf : IsMarkov f] {I : σ → Prop}
    (hI : ∀ s, I s → ∀ᵐ t ∂f s, ¬t.isDone → I t.run) {M : ℕ} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : ∀ s, I s → loopRun f M s Set.univ ≤ c) (n : ℕ) :
    ∀ b, I b → loopRun f (n + M) b Set.univ ≤ c * loopRun f n b Set.univ := by
  induction n with
  | zero => exact fun b hb ↦ by simpa using h b hb
  | succ n ih =>
    intro b hb
    rw [Nat.add_right_comm, loopRun_succ_apply_univ hf.measurable,
      loopRun_succ_apply_univ hf.measurable, ← lintegral_const_mul' _ _ hc]
    refine lintegral_mono_ae ?_
    filter_upwards [hI b hb] with t ht
    cases t with
    | done _ => simp
    | yield s => simpa using ih s (by simpa using ht)

private lemma loopRun_mul_apply_univ_le [IsMarkov f] {I : σ → Prop}
    (hI : ∀ s, I s → ∀ᵐ t ∂f s, ¬t.isDone → I t.run) {N : ℕ} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : ∀ s, I s → loopRun f N s Set.univ ≤ c) (k : ℕ) :
    ∀ b, I b → loopRun f (N * k) b Set.univ ≤ c ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro b hb
    rw [Nat.mul_succ, pow_succ']
    exact (loopRun_add_apply_univ_le hI hc h _ b hb).trans (by gcongr; exact ih b hb)

/-- From a state of an invariant, a loop stops almost surely as soon as, from every state of the
invariant, the runs still going after `N` steps have a mass at most some `c < 1`. -/
private lemma terminates_of_loopRun_le [IsMarkov f] (I : σ → Prop)
    (hI : ∀ s, I s → ∀ᵐ t ∂f s, ¬t.isDone → I t.run) (N : ℕ) {c : ℝ≥0∞} (hc : c < 1)
    (h : ∀ s, I s → loopRun f N s Set.univ ≤ c) (hb : I b) : Terminates f b := by
  have lim := tendsto_atTop_iInf (antitone_loopRun_apply_univ f b)
  suffices ⨅ n, loopRun f n b Set.univ = 0 by rwa [this] at lim
  refine le_antisymm ?_ bot_le
  refine ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc) fun k ↦ ?_
  exact (iInf_le _ (N * k)).trans
    (loopRun_mul_apply_univ_le hI (hc.trans ENNReal.one_lt_top).ne h k b hb)

/-- The common core of the variant rules: from a state of an invariant, a loop stops almost surely
if a natural number `V`, bounded by `N` on the invariant, is decreased or the loop stopped with
probability at least `ε > 0` by every step from the invariant. -/
private lemma terminates_of_variant [hf : IsMarkov f] (I : σ → Prop)
    (hI : ∀ s, I s → ∀ᵐ t ∂f s, ¬t.isDone → I t.run) (V : σ → ℕ) (hV : Measurable V) (N : ℕ)
    (hN : ∀ s, I s → V s ≤ N) (ε : ℝ≥0∞) (hε : ε ≠ 0)
    (h : ∀ s, I s → ε ≤ f s {t | t.isDone ∨ V t.run < V s}) (hb : I b) : Terminates f b := by
  -- From a state of `I` whose variant is `< n`, the runs still going after `n` steps have a mass
  -- at most `1 - εⁿ`.
  have key : ∀ n s, I s → V s < n → loopRun f n s Set.univ ≤ 1 - ε ^ n := by
    intro n
    induction n with
    | zero => exact fun s _ hs ↦ absurd hs (Nat.not_lt_zero _)
    | succ n ih =>
      intro s hIs hs
      set S := {t : ForInStep σ | t.isDone ∨ V t.run < V s}
      have hS : MeasurableSet S :=
        (ForInStep.measurable_isDone (measurableSet_singleton true)).union
          ((hV.comp ForInStep.measurable_run) measurableSet_Iio)
      have := hf.isProbabilityMeasure s
      have hε1 : ε ≤ 1 := (h s hIs).trans prob_le_one
      rw [loopRun_succ_apply_univ hf.measurable]
      calc _ ≤ ∫⁻ t, 1 - S.indicator (fun _ ↦ ε ^ n) t ∂f s := by
            refine lintegral_mono_ae ?_
            filter_upwards [hI s hIs] with t ht
            cases t with
            | done s' => simp
            | yield s' =>
              have hIs' : I s' := by simpa using ht
              by_cases hlt : V s' < V s
              · simpa [S, hlt] using ih s' hIs' (hlt.trans_le (Nat.lt_succ_iff.1 hs))
              · simpa [S, hlt] using loopRun_apply_univ_le_one f n s'
        _ = 1 - ε ^ n * f s S := by
          rw [lintegral_sub (measurable_const.indicator hS), lintegral_indicator_const hS]
          · simp
          · rw [lintegral_indicator_const hS]
            exact ENNReal.mul_ne_top
              (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hε1)) (measure_ne_top _ _)
          · exact Eventually.of_forall fun t ↦
              Set.indicator_le (fun _ _ ↦ pow_le_one₀ bot_le hε1) t
        _ ≤ 1 - ε ^ (n + 1) := tsub_le_tsub_left (by rw [pow_succ]; gcongr; exact h s hIs) 1
  refine terminates_of_loopRun_le I hI (N + 1) (c := 1 - ε ^ (N + 1)) ?_
    (fun s hs ↦ key _ s hs (Nat.lt_succ_of_le (hN s hs))) hb
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (pow_ne_zero _ hε)

/-! ### Stopping a loop on a set, and the probability of reaching it -/

/-- The loop whose step is `f`, stopped as soon as its state is in `A`. -/
private noncomputable def stopOn (A : Set σ) (f : σ → Measure (ForInStep σ)) (s : σ) :
    Measure (ForInStep σ) :=
  open Classical in if s ∈ A then Measure.dirac (ForInStep.done s) else f s

private lemma isMarkov_stopOn [hf : IsMarkov f] {A : Set σ} (hA : MeasurableSet A) :
    IsMarkov (stopOn A f) := by
  classical
  refine ⟨?_, fun s ↦ ?_⟩
  · exact Measurable.ite hA (Measure.measurable_dirac.comp ForInStep.measurable_done) hf.measurable
  · unfold stopOn
    split_ifs
    · infer_instance
    · exact hf.isProbabilityMeasure s

private lemma stopOn_of_mem {A : Set σ} {s : σ} (h : s ∈ A) :
    stopOn A f s = Measure.dirac (ForInStep.done s) := by
  classical
  simp [stopOn, h]

private lemma stopOn_of_notMem {A : Set σ} {s : σ} (h : s ∉ A) : stopOn A f s = f s := by
  classical
  simp [stopOn, h]

/-- Under the Dirac mass at a stop, every run has stopped. -/
private lemma ae_dirac_done (P : σ → Prop) (s : σ) :
    ∀ᵐ t ∂Measure.dirac (ForInStep.done s), ¬t.isDone → P t.run := by
  have h0 : Measure.dirac (ForInStep.done s) (ForInStep.isDone ⁻¹' {false}) = 0 := by
    rw [Measure.dirac_apply' _ (ForInStep.measurable_isDone (measurableSet_singleton false))]
    simp
  refine measure_mono_null (fun t ht ↦ ?_) h0
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  cases hdone : t.isDone
  · rfl
  · exact absurd (fun h ↦ absurd hdone h) ht

/-- The stopped loop keeps the invariants of the loop. -/
private lemma ae_stopOn {A : Set σ} {I : σ → Prop}
    (h : ∀ s, I s → ∀ᵐ t ∂f s, ¬t.isDone → I t.run) :
    ∀ s, I s → ∀ᵐ t ∂stopOn A f s, ¬t.isDone → I t.run := by
  intro s hs
  by_cases hA : s ∈ A
  · rw [stopOn_of_mem hA]
    exact ae_dirac_done I s
  · rw [stopOn_of_notMem hA]
    exact h s hs

/-- The probability that the loop whose step is `f`, from `s`, is in `A` at one of its first `n + 1`
states while it has not stopped. -/
private noncomputable def hitRun (f : σ → Measure (ForInStep σ)) (A : Set σ) : ℕ → σ → ℝ≥0∞
  | 0, s => A.indicator 1 s
  | n + 1, s => open Classical in
      if s ∈ A then 1 else ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0)
        (hitRun f A n) ∂f s

private lemma measurable_casesOn' {γ : Type*} [MeasurableSpace γ] {d y : σ → γ}
    (hd : Measurable d) (hy : Measurable y) :
    Measurable fun t : ForInStep σ ↦ ForInStep.casesOn (motive := fun _ ↦ γ) t d y :=
  fun _ hs ↦ ⟨hy hs, hd hs⟩

private lemma measurable_hitRun (hf : Measurable f) {A : Set σ} (hA : MeasurableSet A) :
    ∀ n, Measurable (hitRun f A n)
  | 0 => measurable_const.indicator hA
  | n + 1 => by
    classical
    exact Measurable.ite hA measurable_const ((Measure.measurable_lintegral
      (measurable_casesOn' measurable_const (measurable_hitRun hf hA n))).comp hf)

private lemma hitRun_le_one (A : Set σ) [hf : IsMarkov f] : ∀ n s, hitRun f A n s ≤ 1
  | 0, s => by simp only [hitRun]; exact Set.indicator_le_self' (fun _ _ ↦ zero_le_one) s
  | n + 1, s => by
    classical
    simp only [hitRun]
    split_ifs
    · exact le_rfl
    · have := hf.isProbabilityMeasure s
      calc _ ≤ ∫⁻ _, 1 ∂f s := lintegral_mono fun t ↦ by
            cases t <;> simp [hitRun_le_one A n]
        _ = 1 := by simp

/-- The runs still going after `n` steps either are still going in the loop stopped on `A`, or have
been in `A` before. -/
private lemma loopRun_le_stopOn_add_hitRun [hf : IsMarkov f] {A : Set σ} (hA : MeasurableSet A) :
    ∀ n b, loopRun f n b Set.univ ≤ loopRun (stopOn A f) n b Set.univ + hitRun f A n b
  | 0, b => by simp
  | n + 1, b => by
    classical
    have hfA := isMarkov_stopOn (f := f) hA
    rw [loopRun_succ_apply_univ hf.measurable, loopRun_succ_apply_univ hfA.measurable]
    by_cases hb : b ∈ A
    · simp only [hitRun, hb, ite_true]
      calc _ ≤ (1 : ℝ≥0∞) := (loopRun_succ_apply_univ hf.measurable n b).symm ▸
              loopRun_apply_univ_le_one f (n + 1) b
        _ ≤ _ := le_add_self
    · simp only [stopOn, hitRun, hb, ite_false]
      have hRun : Measurable fun s ↦ loopRun (stopOn A f) n s Set.univ :=
        (Measure.measurable_coe MeasurableSet.univ).comp (measurable_loopRun hfA.measurable n)
      rw [← lintegral_add_left (measurable_casesOn' measurable_const hRun)]
      refine lintegral_mono fun t ↦ ?_
      cases t with
      | done _ => simp
      | yield s => simpa [stopOn] using loopRun_le_stopOn_add_hitRun hA n s

/-- A loop stops almost surely if, for every `δ > 0`, it stops almost surely once stopped on some
set that it reaches with probability at most `δ`. -/
private lemma terminates_of_stopOn [IsMarkov f]
    (h : ∀ δ : ℝ≥0∞, 0 < δ → ∃ A, MeasurableSet A ∧ Terminates (stopOn A f) b ∧
      ∀ n, hitRun f A n b ≤ δ) : Terminates f b := by
  have lim := tendsto_atTop_iInf (antitone_loopRun_apply_univ f b)
  suffices ⨅ n, loopRun f n b Set.univ = 0 by rwa [this] at lim
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_) bot_le
  obtain ⟨A, hA, hterm, hhit⟩ := h δ (by exact_mod_cast hδ)
  have := isMarkov_stopOn (f := f) hA
  -- The runs of the stopped loop still going tend to `0`.
  refine ge_of_tendsto' (hterm.add_const (δ : ℝ≥0∞)) fun n ↦ ?_
  exact (iInf_le _ n).trans ((loopRun_le_stopOn_add_hitRun hA n b).trans
      (by gcongr; exact hhit n))

/-- **Maximal inequality**, for a nonnegative supermartingale `W` on an invariant: the probability
of reaching a set on which `W ≥ r` is at most `W / r`. -/
private lemma mul_hitRun_le_of_supermartingale [hf : IsMarkov f] (I : σ → Prop)
    (hI : ∀ s, I s → ∀ᵐ t ∂f s, ¬t.isDone → I t.run) (W : σ → ℝ≥0∞) (hW : Measurable W)
    (hsuper : ∀ s, I s →
      ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0) W ∂f s ≤ W s)
    {A : Set σ} (r : ℝ≥0∞) (hA : ∀ s ∈ A, r ≤ W s) (hAm : MeasurableSet A) :
    ∀ n s, I s → r * hitRun f A n s ≤ W s
  | 0, s, _ => by
    classical
    simp only [hitRun, Set.indicator_apply, Pi.one_apply]
    split_ifs with h
    · simpa using hA s h
    · simp
  | n + 1, s, hs => by
    classical
    simp only [hitRun]
    split_ifs with h
    · simpa using hA s h
    · rw [← lintegral_const_mul _ (measurable_casesOn' measurable_const
        (measurable_hitRun hf.measurable hAm n))]
      refine le_trans (lintegral_mono_ae ?_) (hsuper s hs)
      filter_upwards [hI s hs] with t ht
      cases t with
      | done _ => simp
      | yield s' =>
        have := mul_hitRun_le_of_supermartingale I hI W hW hsuper r hA hAm n s' (by simpa using ht)
        simpa using this


/-- **Maximal inequality**, for a submartingale `Z ≤ H` that vanishes on `A`: from a state of the
invariant, `Z` plus `H` times the probability of reaching `A` is at most `H`. -/
private lemma add_mul_hitRun_le_of_submartingale [hf : IsMarkov f] (I : σ → Prop)
    (hI : ∀ s, I s → ∀ᵐ t ∂f s, ¬t.isDone → I t.run) (Z : σ → ℝ≥0∞) (H : ℝ≥0∞)
    (hZH : ∀ s, Z s ≤ H) {A : Set σ} (hAm : MeasurableSet A) (hZA : ∀ s ∈ A, Z s = 0)
    (hsub : ∀ s, I s → s ∉ A →
      Z s ≤ ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ H) Z ∂f s) :
    ∀ n s, I s → Z s + H * hitRun f A n s ≤ H
  | 0, s, _ => by
    classical
    simp only [hitRun, Set.indicator_apply, Pi.one_apply]
    split_ifs with h
    · simp [hZA s h]
    · simpa using hZH s
  | n + 1, s, hs => by
    classical
    simp only [hitRun]
    split_ifs with h
    · simp [hZA s h]
    · have := hf.isProbabilityMeasure s
      have hmeas : Measurable fun t : ForInStep σ ↦
          H * ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0) (hitRun f A n) :=
        measurable_const.mul (measurable_casesOn' measurable_const
          (measurable_hitRun hf.measurable hAm n))
      rw [← lintegral_const_mul _ (measurable_casesOn' measurable_const
        (measurable_hitRun hf.measurable hAm n))]
      calc _ ≤ ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ H) Z ∂f s +
            ∫⁻ t, H * ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0)
              (hitRun f A n) ∂f s := by gcongr; exact hsub s hs h
        _ = ∫⁻ t, (ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ H) Z +
            H * ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0)
              (hitRun f A n)) ∂f s := (lintegral_add_right _ hmeas).symm
        _ ≤ ∫⁻ _, H ∂f s := by
          refine lintegral_mono_ae ?_
          filter_upwards [hI s hs] with t ht
          cases t with
          | done _ => simp
          | yield s' =>
            have := add_mul_hitRun_le_of_submartingale I hI Z H hZH hAm hZA hsub n s'
              (by simpa using ht)
            simpa using this
        _ = H := by simp

/-! ### The loop `while G do body` -/

/-- The step of the loop `while G do body`, whose body is a family `body` of measures on the
states: from a state satisfying `G`, run the body and carry on; from any other state, stop. -/
noncomputable def whileStep (G : σ → Prop) (body : σ → Measure σ) (s : σ) :
    Measure (ForInStep σ) :=
  open Classical in if G s then (body s).map ForInStep.yield else Measure.dirac (ForInStep.done s)

lemma isMarkov_whileStep {G : σ → Prop} (hG : MeasurableSet {s | G s}) {body : σ → Measure σ}
    [hbody : IsMarkov body] : IsMarkov (whileStep G body) := by
  classical
  refine ⟨Measurable.ite hG ((Measure.measurable_map _ ForInStep.measurable_yield).comp
    hbody.measurable) (Measure.measurable_dirac.comp ForInStep.measurable_done), fun s ↦ ?_⟩
  unfold whileStep
  split_ifs
  · have := hbody.isProbabilityMeasure s
    exact Measure.isProbabilityMeasure_map ForInStep.measurable_yield.aemeasurable
  · infer_instance


section whileStep

variable {G : σ → Prop} {body : σ → Measure σ} {s : σ}

private lemma whileStep_of_pos (h : G s) : whileStep G body s = (body s).map ForInStep.yield := by
  classical
  simp [whileStep, h]

private lemma whileStep_of_neg (h : ¬G s) :
    whileStep G body s = Measure.dirac (ForInStep.done s) := by
  classical
  simp [whileStep, h]

/-- A predicate holding with probability `1`: its complement is null. -/
private lemma measure_compl_eq_zero_of_one_le {μ : Measure σ} [IsProbabilityMeasure μ]
    {P : σ → Prop} (hP : MeasurableSet {s | P s}) (h : 1 ≤ (μ {s | P s}).toReal) :
    μ {s | P s}ᶜ = 0 := by
  rw [measure_compl hP (measure_ne_top _ _), measure_univ]
  exact tsub_eq_zero_of_le (by simpa using ENNReal.ofReal_le_of_le_toReal h)

/-- A step from a state of an invariant `Inv` satisfying `G` carries on in `Inv`, almost surely. -/
private lemma ae_whileStep {Inv : σ → Prop} (hInv : MeasurableSet {s | Inv s})
    (h : G s → 1 ≤ (body s {s' | Inv s'}).toReal) [IsMarkov body] :
    ∀ᵐ t ∂whileStep G body s, ¬t.isDone → Inv t.run := by
  by_cases hG : G s
  · rw [whileStep_of_pos hG, ForInStep.measurableEmbedding_yield.ae_map_iff]
    have := IsMarkov.isProbabilityMeasure (κ := body) s
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_compl_eq_zero_of_one_le hInv (h hG))]
      with s' hs'
    simpa using hs'
  · rw [whileStep_of_neg hG]
    exact ae_dirac_done Inv s

end whileStep

namespace Terminates

/-- **Variant rule for loops** (McIver and Morgan 2005, Lemma 7.5.1, first stated as Lemma 2.7.1).

For the loop `while G do body`, let `V` be an integer-valued function of the state and `Inv` a
predicate such that
1. there are integers `L` and `H` with `G ∧ Inv ⇛ L ≤ V < H`;
2. `[Inv]` is a strong invariant: `[G] ∗ [Inv] ⇛ wp.body.[Inv]`;
3. for some probability `ε > 0` and all integers `N`, `ε ∗ [G ∧ Inv ∧ (V = N)] ⇛ wp.body.[V < N]`.

Then the loop terminates with probability `1` from every state satisfying `Inv`: `[Inv] ⇛ T`.

The body is a Markov kernel, and `wp.body.[P]` at `s` is the probability `body s {s' | P s'}`. The
bound `ε ≤ 1`, implicit in "probability", is not needed. -/
theorem mcIverMorgan_variantRule {G Inv : σ → Prop} {body : σ → Measure σ}
    (V : σ → ℤ) (L H : ℤ) (ε : ℝ) (hε : 0 < ε)
    (h1 : ∀ s, G s → Inv s → L ≤ V s ∧ V s < H)
    (h2 : ∀ s, G s → Inv s → 1 ≤ (body s {s' | Inv s'}).toReal)
    (h3 : ∀ N : ℤ, ∀ s, G s → Inv s → V s = N → ε ≤ (body s {s' | V s' < N}).toReal)
    (hb : Inv b) (hG : MeasurableSet {s | G s} := by measurability)
    (hInv : MeasurableSet {s | Inv s} := by measurability) (hV : Measurable V := by fun_prop)
    (hbody : IsMarkov body := by is_markov) : Terminates (whileStep G body) b := by
  classical
  have := isMarkov_whileStep (body := body) hG
  -- The variant shifted to `ℕ`, and set to `0` on the states where the loop stops.
  let V' : σ → ℕ := fun s ↦ if G s then (V s - L + 1).toNat else 0
  have hV' : Measurable V' :=
    Measurable.ite hG ((Measurable.of_discrete (f := fun z : ℤ ↦ (z - L + 1).toNat)).comp hV)
      measurable_const
  refine terminates_of_variant Inv (fun s hs ↦ ae_whileStep hInv (h2 s · hs)) V' hV'
    (H - L).toNat (fun s hs ↦ ?_) (min (ENNReal.ofReal ε) 1)
    (lt_min (ENNReal.ofReal_pos.2 hε) one_pos).ne' (fun s hs ↦ ?_) hb
  · simp only [V']
    split_ifs with hG
    · have := h1 s hG hs
      exact Int.toNat_le_toNat (by omega)
    · exact Nat.zero_le _
  · by_cases hG : G s
    · have := IsMarkov.isProbabilityMeasure (κ := body) s
      rw [whileStep_of_pos hG, ForInStep.measurableEmbedding_yield.map_apply]
      refine (min_le_left _ _).trans
        ((ENNReal.ofReal_le_of_le_toReal (h3 (V s) s hG hs rfl)).trans ?_)
      rw [← measure_inter_conull (measure_compl_eq_zero_of_one_le hInv (h2 s hG hs))]
      refine measure_mono fun s' ⟨hlt, hInv'⟩ ↦ Or.inr ?_
      have := h1 s hG hs
      simp only [Set.mem_ofPred_eq] at hlt hInv'
      change V' s' < V' s
      simp only [V', hG, ite_true]
      split_ifs with hG'
      · have := h1 s' hG' hInv'
        omega
      · omega
    · rw [whileStep_of_neg hG, Measure.dirac_apply_of_mem (by simp)]
      exact min_le_right _ _


/-- **Variant rule for loops** (McIver and Morgan 2005, Lemma 2.7.1): the bounds on the variant are
only asked when the states satisfying `G ∧ Inv` are infinitely many, and `0 < ε ≤ 1`. -/
theorem mcIverMorgan_variantRule_of_finite {G Inv : σ → Prop} {body : σ → Measure σ}
    (V : σ → ℤ) (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (h1 : ¬{s | G s ∧ Inv s}.Finite → ∃ L H : ℤ, ∀ s, G s → Inv s → L ≤ V s ∧ V s < H)
    (h2 : ∀ s, G s → Inv s → 1 ≤ (body s {s' | Inv s'}).toReal)
    (h3 : ∀ N : ℤ, ∀ s, G s → Inv s → V s = N → ε ≤ (body s {s' | V s' < N}).toReal)
    (hb : Inv b) (hG : MeasurableSet {s | G s} := by measurability)
    (hInv : MeasurableSet {s | Inv s} := by measurability) (hV : Measurable V := by fun_prop)
    (hbody : IsMarkov body := by is_markov) : Terminates (whileStep G body) b := by
  -- Over finitely many states, the variant takes finitely many values.
  obtain ⟨L, H, hLH⟩ : ∃ L H : ℤ, ∀ s, G s → Inv s → L ≤ V s ∧ V s < H := by
    by_cases hfin : {s | G s ∧ Inv s}.Finite
    · obtain ⟨L, hL⟩ := (hfin.image V).bddBelow
      obtain ⟨H, hH⟩ := (hfin.image V).bddAbove
      exact ⟨L, H + 1, fun s hG hI ↦ ⟨hL ⟨s, ⟨hG, hI⟩, rfl⟩,
        Int.lt_add_one_iff.2 (hH ⟨s, ⟨hG, hI⟩, rfl⟩)⟩⟩
    · exact h1 hfin
  exact mcIverMorgan_variantRule V L H ε hε hLH h2 h3 hb hG hInv hV hbody

/-- **Variant rule for loops, with a variant that cannot increase** (McIver and Morgan 2005, p. 56,
stated and derived there informally from Lemma 2.7.1). The variant is bounded below but not
necessarily above, it decreases with probability at least `ε > 0`, and it cannot increase: its
initial value bounds it above. -/
theorem mcIverMorgan_variantRule_of_antitone {G Inv : σ → Prop} {body : σ → Measure σ}
    (V : σ → ℤ) (L : ℤ) (ε : ℝ) (hε : 0 < ε)
    (h1 : ∀ s, G s → Inv s → L ≤ V s)
    (h2 : ∀ s, G s → Inv s → 1 ≤ (body s {s' | Inv s'}).toReal)
    (h3 : ∀ N : ℤ, ∀ s, G s → Inv s → V s = N → ε ≤ (body s {s' | V s' < N}).toReal)
    (h4 : ∀ N : ℤ, ∀ s, G s → Inv s → V s = N → 1 ≤ (body s {s' | V s' ≤ N}).toReal)
    (hb : Inv b) (hG : MeasurableSet {s | G s} := by measurability)
    (hInv : MeasurableSet {s | Inv s} := by measurability) (hV : Measurable V := by fun_prop)
    (hbody : IsMarkov body := by is_markov) : Terminates (whileStep G body) b := by
  have hle : MeasurableSet {s | V s ≤ V b} := hV measurableSet_Iic
  refine mcIverMorgan_variantRule (Inv := fun s ↦ Inv s ∧ V s ≤ V b) V L (V b + 1) ε hε
    (fun s hG hs ↦ ⟨h1 s hG hs.1, Int.lt_add_one_iff.2 hs.2⟩) (fun s hG hs ↦ ?_)
    (fun N s hG hs ↦ h3 N s hG hs.1) ⟨hb, le_rfl⟩ hG (hInv.inter hle) hV hbody
  -- The invariant is kept, and the variant does not increase, almost surely.
  have := IsMarkov.isProbabilityMeasure (κ := body) s
  refine le_trans ?_ (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (s := {s' | V s' ≤ V s} ∩ {s' | Inv s'}) fun s' ⟨hV', hI'⟩ ↦
      ⟨hI', hV'.trans hs.2⟩))
  rw [measure_inter_conull (measure_compl_eq_zero_of_one_le hInv (h2 s hG hs.1))]
  exact h4 (V s) s hG hs.1 rfl


/-- **New variant rule for loops** (McIver, Morgan, Kaminski and Katoen, *A New Proof Rule for
Almost-Sure Termination*, POPL 2018, Theorem 4.1).

For the loop `while G do body`, let `I` be a predicate, `V` a nonnegative real-valued function of
the state, not necessarily bounded, and `p` ("probability", valued in `(0, 1]`) and `d`
("decrease", valued in `ℝ>0`) fixed functions of the nonnegative reals, both antitone on strictly
positive arguments, such that
* (i) `I` is a standard invariant of the loop: `[G ∧ I] ≤ wp.body.[I]`;
* (ii) `G ∧ I ⇒ V > 0`;
* (iii) for every `R > 0`, `p(R) · [G ∧ I ∧ V = R] ≤ wp.body.[V ≤ R - d(R)]`;
* (iv) `V` is a super-martingale: for every `H > 0`, `[G ∧ I] · (H ⊖ V) ≤ wp.body.(H ⊖ V)`, where
  `H ⊖ V = max (H - V) 0`.

Then the loop terminates with probability `1` from every state satisfying `I`.

The body is a Markov kernel, `wp.body.[P]` at `s` is the probability `body s {s' | P s'}`, and
`wp.body.(H ⊖ V)` is the integral of `H ⊖ V` against `body s`. -/
theorem mcIverMorganKaminskiKatoen {G I : σ → Prop} {body : σ → Measure σ}
    (V : σ → ℝ) (hV0 : ∀ s, 0 ≤ V s) (p d : ℝ → ℝ)
    (hp : ∀ r, 0 ≤ r → 0 < p r ∧ p r ≤ 1) (hd : ∀ r, 0 ≤ r → 0 < d r)
    (hp_anti : AntitoneOn p (Set.Ioi 0)) (hd_anti : AntitoneOn d (Set.Ioi 0))
    (h1 : ∀ s, G s → I s → 1 ≤ (body s {s' | I s'}).toReal)
    (h2 : ∀ s, G s → I s → 0 < V s)
    (h3 : ∀ R, 0 < R → ∀ s, G s → I s → V s = R → p R ≤ (body s {s' | V s' ≤ R - d R}).toReal)
    (h4 : ∀ H, 0 < H → ∀ s, G s → I s →
      ENNReal.ofReal (H - V s) ≤ ∫⁻ s', ENNReal.ofReal (H - V s') ∂body s)
    (hb : I b) (hG : MeasurableSet {s | G s} := by measurability)
    (hI : MeasurableSet {s | I s} := by measurability) (hV : Measurable V := by fun_prop)
    (hbody : IsMarkov body := by is_markov) : Terminates (whileStep G body) b := by
  classical
  have := isMarkov_whileStep (body := body) hG
  have hIf : ∀ s, I s → ∀ᵐ t ∂whileStep G body s, ¬t.isDone → I t.run :=
    fun s hs ↦ ae_whileStep hI (h1 s · hs)
  refine terminates_of_stopOn fun δ hδ ↦ ?_
  -- A level `H` above `V b`, high enough for `V b / H ≤ δ`.
  obtain ⟨H, hVH, hHδ⟩ : ∃ H : ℝ, V b < H ∧ ENNReal.ofReal (V b) / ENNReal.ofReal H ≤ δ := by
    by_cases hδtop : δ = ⊤
    · exact ⟨V b + 1, by linarith, hδtop ▸ le_top⟩
    have hδ' : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
    have hq := div_nonneg (hV0 b) hδ'.le
    have hH : 0 < V b + 1 + V b / δ.toReal := by linarith [hV0 b]
    refine ⟨V b + 1 + V b / δ.toReal, by linarith, ?_⟩
    rw [← ENNReal.ofReal_div_of_pos hH]
    calc ENNReal.ofReal (V b / (V b + 1 + V b / δ.toReal)) ≤ ENNReal.ofReal δ.toReal := by
          refine ENNReal.ofReal_le_ofReal ((div_le_iff₀ hH).2 ?_)
          have : δ.toReal * (V b / δ.toReal) = V b := by field_simp
          nlinarith [hV0 b]
      _ = δ := ENNReal.ofReal_toReal hδtop
  have hH : 0 < H := (hV0 b).trans_lt hVH
  set A := {s | H ≤ V s}
  have hA : MeasurableSet A := hV measurableSet_Ici
  refine ⟨A, hA, ?_, fun n ↦ ?_⟩
  · -- Below the level `H`, the variant `⌈V / d(H)⌉` decreases with probability at least `p(H)`.
    have := isMarkov_stopOn (f := whileStep G body) hA
    have hdH := hd H hH.le
    let V' : σ → ℕ := fun s ↦ if G s ∧ V s < H then ⌈V s / d H⌉₊ else 0
    have hV' : Measurable V' :=
      Measurable.ite (hG.inter (hV measurableSet_Iio)) (Measurable.nat_ceil (hV.div_const (d H)))
        measurable_const
    refine terminates_of_variant I (ae_stopOn hIf) V' hV' ⌈H / d H⌉₊ (fun s _ ↦ ?_)
      (min (ENNReal.ofReal (p H)) 1) (lt_min (ENNReal.ofReal_pos.2 (hp H hH.le).1) one_pos).ne'
      (fun s hs ↦ ?_) hb
    · simp only [V']
      split_ifs with h
      · exact Nat.ceil_mono (div_le_div_of_nonneg_right h.2.le hdH.le)
      · exact Nat.zero_le _
    · by_cases hsA : s ∈ A
      · rw [stopOn_of_mem hsA, Measure.dirac_apply_of_mem (by simp)]
        exact min_le_right _ _
      rw [stopOn_of_notMem hsA]
      simp only [A, Set.mem_ofPred_eq, not_le] at hsA
      by_cases hGs : G s
      · have := IsMarkov.isProbabilityMeasure (κ := body) s
        have hVs := h2 s hGs hs
        rw [whileStep_of_pos hGs, ForInStep.measurableEmbedding_yield.map_apply]
        refine (min_le_left _ _).trans ?_
        refine (ENNReal.ofReal_le_ofReal (hp_anti hVs hH hsA.le)).trans ?_
        refine (ENNReal.ofReal_le_of_le_toReal (h3 (V s) hVs s hGs hs rfl)).trans ?_
        refine measure_mono fun s' hs' ↦ Or.inr ?_
        simp only [Set.mem_ofPred_eq] at hs'
        have hdle : d H ≤ d (V s) := hd_anti hVs hH hsA.le
        change V' s' < V' s
        have hV's : V' s = ⌈V s / d H⌉₊ := by simp [V', hGs, hsA]
        rw [hV's, Nat.lt_ceil]
        simp only [V']
        split_ifs with h'
        · calc (⌈V s' / d H⌉₊ : ℝ) < V s' / d H + 1 :=
                Nat.ceil_lt_add_one (div_nonneg (hV0 s') hdH.le)
            _ ≤ V s / d H := by
              rw [div_add_one hdH.ne', div_le_div_iff_of_pos_right hdH]
              linarith
        · simpa using div_pos hVs hdH
      · rw [whileStep_of_neg hGs, Measure.dirac_apply_of_mem (by simp)]
        exact min_le_right _ _
  · -- The maximal inequality, for the submartingale `H ⊖ V`.
    have hmax := add_mul_hitRun_le_of_submartingale (f := whileStep G body) I hIf
      (fun s ↦ ENNReal.ofReal (H - V s)) (ENNReal.ofReal H)
      (fun s ↦ ENNReal.ofReal_le_ofReal (by linarith [hV0 s])) hA
      (fun s hs ↦ ENNReal.ofReal_eq_zero.2 (by simp only [A, Set.mem_ofPred_eq] at hs; linarith))
      (fun s hs hsA ↦ ?_) n b hb
    · have hsub := ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top hmax
      rw [← ENNReal.ofReal_sub _ (by linarith), sub_sub_cancel] at hsub
      refine le_trans ?_ hHδ
      rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hH).ne')
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact hsub
    · have hZ : Measurable fun s ↦ ENNReal.ofReal (H - V s) :=
        ENNReal.measurable_ofReal.comp (measurable_const.sub hV)
      by_cases hGs : G s
      · rw [whileStep_of_pos hGs, ForInStep.measurableEmbedding_yield.lintegral_map]
        exact h4 H hH s hGs hs
      · rw [whileStep_of_neg hGs, lintegral_dirac' _ (measurable_casesOn' measurable_const hZ)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hV0 s])


/-- **Variant rule for almost-sure termination** (McIver and Morgan 2005, in the form of Majumdar
and Sathiyanarayana, *Sound and Complete Proof Rules for Probabilistic Termination*, POPL 2025,
Proof Rule 3.1 and Lemma 3.1).

The program is the transition system whose states are the `ForInStep σ`: the successor of a state
`yield s` is drawn from `f s`, and the states `done s` are terminal. To show that it terminates
almost surely from `yield b`, find
1. an inductive invariant `Inv` containing `yield b`;
2. a variant function `U : Inv → ℤ`;
3. bounds `Lo` and `Hi` such that `Lo ≤ U < Hi` on `Inv`;
4. an `ε > 0`,

such that, for each state of `Inv`,
* (4.1) if it is terminal, `U = Lo`;
* (4.3) otherwise, the successors that decrease `U` have a total probability `> ε`.

Every non-terminal state is probabilistic, so condition (4.2) on assignment and nondeterministic
states does not apply, and "every successor" is "almost every successor". -/
theorem majumdarSathiyanarayana_variantRule (Inv : ForInStep σ → Prop) (U : ForInStep σ → ℤ)
    (Lo Hi : ℤ) (ε : ℝ) (hε : 0 < ε) (hb : Inv (.yield b))
    (hInv : ∀ s, Inv (.yield s) → ∀ᵐ t ∂f s, Inv t)
    (hbounds : ∀ t, Inv t → Lo ≤ U t ∧ U t < Hi)
    (_hdone : ∀ s, Inv (.done s) → U (.done s) = Lo)
    (hprog : ∀ s, Inv (.yield s) → ε < (f s {t | U t < U (.yield s)}).toReal)
    (hU : Measurable U := by fun_prop) (hf : IsMarkov f := by is_markov) : Terminates f b := by
  let V' : σ → ℕ := fun s ↦ (U (.yield s) - Lo).toNat
  have hV' : Measurable V' :=
    (Measurable.of_discrete (f := fun z : ℤ ↦ (z - Lo).toNat)).comp
      (hU.comp ForInStep.measurable_yield)
  refine terminates_of_variant (fun s ↦ Inv (.yield s)) (fun s hs ↦ ?_) V' hV' (Hi - Lo).toNat
    (fun s hs ↦ Int.toNat_le_toNat (by linarith [(hbounds _ hs).2])) (min (ENNReal.ofReal ε) 1)
    (lt_min (ENNReal.ofReal_pos.2 hε) one_pos).ne' (fun s hs ↦ ?_) hb
  · filter_upwards [hInv s hs] with t ht
    cases t with
    | done _ => simp
    | yield _ => simpa using ht
  · refine (min_le_left _ _).trans ((ENNReal.ofReal_le_of_le_toReal (hprog s hs).le).trans ?_)
    rw [← measure_inter_conull (t := {t | Inv t})
      (by rw [Set.compl_ofPred]; exact ae_iff.1 (hInv s hs))]
    refine measure_mono fun t ⟨hlt, ht⟩ ↦ ?_
    cases t with
    | done _ => simp
    | yield s' =>
      simp only [Set.mem_ofPred_eq] at hlt ht
      have := (hbounds _ ht).1
      simp only [Set.mem_ofPred_eq, ForInStep.isDone_yield, Bool.false_eq_true, false_or,
        ForInStep.run_yield, V']
      omega

/-- **Martingale rule for almost-sure termination** (Majumdar and Sathiyanarayana, *Sound and
Complete Proof Rules for Probabilistic Termination*, POPL 2025, Proof Rule 3.2 and Lemma 3.2).

The program is the transition system whose states are the `ForInStep σ`, as in
`majumdarSathiyanarayana_variantRule`. To show that it terminates almost surely from `yield b`,
find
1. an inductive invariant `Inv` containing `yield b`;
2. a supermartingale function `V : Inv → ℝ` that assigns `0` to the terminal states and, at every
   other state of `Inv`, (2.1) is positive and (2.3) is at least the expected value of `V` after a
   step;
3. a variant function `U : Inv → ℕ` that assigns `0` to the terminal states and satisfies, on each
   sublevel set `V≤r = {σ ∈ Inv | V σ ≤ r}`,
   (3.2.1) `U` is bounded on `V≤r`, and
   (3.2.2) there is an `εᵣ > 0` such that from every non-terminal state of `V≤r`, the successors
   that decrease `U` have a total probability `> εᵣ`.

Every non-terminal state is probabilistic, so conditions (2.2) and (3.1) on assignment and
nondeterministic states do not apply, and "every successor" is "almost every successor". -/
theorem majumdarSathiyanarayana_martingaleRule (Inv : ForInStep σ → Prop) (V : ForInStep σ → ℝ)
    (U : ForInStep σ → ℕ) (hb : Inv (.yield b)) (hInv : ∀ s, Inv (.yield s) → ∀ᵐ t ∂f s, Inv t)
    (hVdone : ∀ s, Inv (.done s) → V (.done s) = 0)
    (hVpos : ∀ s, Inv (.yield s) → 0 < V (.yield s))
    (hVsuper : ∀ s, Inv (.yield s) →
      ∫⁻ t, ENNReal.ofReal (V t) ∂f s ≤ ENNReal.ofReal (V (.yield s)))
    (_hUdone : ∀ s, Inv (.done s) → U (.done s) = 0)
    (hUbdd : ∀ r : ℝ, ∃ B : ℕ, ∀ t, Inv t → V t ≤ r → U t ≤ B)
    (hUprog : ∀ r : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s, Inv (.yield s) → V (.yield s) ≤ r →
      ε < (f s {t | U t < U (.yield s)}).toReal)
    (hV : Measurable V := by fun_prop) (hU : Measurable U := by fun_prop)
    (hf : IsMarkov f := by is_markov) : Terminates f b := by
  classical
  let I : σ → Prop := fun s ↦ Inv (.yield s)
  have hI : ∀ s, I s → ∀ᵐ t ∂f s, ¬t.isDone → I t.run := fun s hs ↦ by
    filter_upwards [hInv s hs] with t ht
    cases t with
    | done _ => simp
    | yield _ => simpa [I] using ht
  have hVy : Measurable fun s ↦ V (.yield s) := hV.comp ForInStep.measurable_yield
  refine terminates_of_stopOn fun δ hδ ↦ ?_
  -- A level `r` above `V b`, high enough for `V b / r ≤ δ`.
  obtain ⟨r, hVr, hrδ⟩ : ∃ r : ℝ, V (.yield b) < r ∧
      ENNReal.ofReal (V (.yield b)) / ENNReal.ofReal r ≤ δ := by
    have hV0 := (hVpos b hb).le
    by_cases hδtop : δ = ⊤
    · exact ⟨V (.yield b) + 1, by linarith, hδtop ▸ le_top⟩
    have hδ' : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
    have hq := div_nonneg hV0 hδ'.le
    have hr : 0 < V (.yield b) + 1 + V (.yield b) / δ.toReal := by linarith
    refine ⟨V (.yield b) + 1 + V (.yield b) / δ.toReal, by linarith, ?_⟩
    rw [← ENNReal.ofReal_div_of_pos hr]
    calc ENNReal.ofReal (V (.yield b) / (V (.yield b) + 1 + V (.yield b) / δ.toReal))
        ≤ ENNReal.ofReal δ.toReal := by
          refine ENNReal.ofReal_le_ofReal ((div_le_iff₀ hr).2 ?_)
          have : δ.toReal * (V (.yield b) / δ.toReal) = V (.yield b) := by field_simp
          nlinarith
      _ = δ := ENNReal.ofReal_toReal hδtop
  have hr : 0 < r := (hVpos b hb).trans hVr
  set A := {s | r < V (.yield s)}
  have hA : MeasurableSet A := hVy measurableSet_Ioi
  refine ⟨A, hA, ?_, fun n ↦ ?_⟩
  · -- Within the sublevel set `V ≤ r`, the variant `U` is bounded and decreases with probability
    -- at least `εᵣ`.
    have := isMarkov_stopOn (f := f) hA
    obtain ⟨B, hB⟩ := hUbdd r
    obtain ⟨ε, hε, hprog⟩ := hUprog r
    let V' : σ → ℕ := fun s ↦ if s ∈ A then 0 else U (.yield s)
    have hV' : Measurable V' :=
      Measurable.ite hA measurable_const (hU.comp ForInStep.measurable_yield)
    refine terminates_of_variant I (ae_stopOn hI) V' hV' B (fun s hs ↦ ?_)
      (min (ENNReal.ofReal ε) 1) (lt_min (ENNReal.ofReal_pos.2 hε) one_pos).ne'
      (fun s hs ↦ ?_) hb
    · simp only [V']
      split_ifs with hsA
      · exact Nat.zero_le _
      · exact hB _ hs (by simpa [A] using hsA)
    · by_cases hsA : s ∈ A
      · rw [stopOn_of_mem hsA, Measure.dirac_apply_of_mem (by simp)]
        exact min_le_right _ _
      rw [stopOn_of_notMem hsA]
      refine (min_le_left _ _).trans ((ENNReal.ofReal_le_of_le_toReal
        (hprog s hs (by simpa [A] using hsA)).le).trans ?_)
      rw [← measure_inter_conull (t := {t | Inv t})
      (by rw [Set.compl_ofPred]; exact ae_iff.1 (hInv s hs))]
      refine measure_mono fun t ⟨hlt, ht⟩ ↦ ?_
      cases t with
      | done _ => simp
      | yield s' =>
        simp only [Set.mem_ofPred_eq] at hlt
        simp only [Set.mem_ofPred_eq, ForInStep.isDone_yield, Bool.false_eq_true, false_or,
          ForInStep.run_yield]
        have hV's : V' s = U (.yield s) := by simp [V', hsA]
        rw [hV's]
        refine lt_of_le_of_lt ?_ hlt
        simp only [V']
        split_ifs
        · exact Nat.zero_le _
        · exact le_rfl
  · -- The maximal inequality, for the nonnegative supermartingale `V`.
    have hsuper : ∀ s, I s → ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0)
        (fun s ↦ ENNReal.ofReal (V (.yield s))) ∂f s ≤ ENNReal.ofReal (V (.yield s)) := by
      intro s hs
      refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hVsuper s hs)
      filter_upwards [hInv s hs] with t ht
      cases t with
      | done s' => simp [hVdone s' ht]
      | yield s' => rfl
    have hmax := mul_hitRun_le_of_supermartingale I hI (fun s ↦ ENNReal.ofReal (V (.yield s)))
      (ENNReal.measurable_ofReal.comp hVy) hsuper (ENNReal.ofReal r)
      (fun s hs ↦ ENNReal.ofReal_le_ofReal hs.le) hA n b hb
    refine le_trans ?_ hrδ
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hr).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hmax

end Terminates

/-- **Lyapunov ranking functions** (Bournez and Garnier, *Proving positive almost-sure termination*,
RTA 2005, Theorem 2, in the form recalled by Ferrer Fioriti and Hermanns, *Probabilistic
Termination: Soundness, Completeness, and Compositionality*, POPL 2015, equation (1)).

The program is the transition system whose states are the `ForInStep σ`, as in
`Terminates.majumdarSathiyanarayana_variantRule`. A map `v` from its states to the nonnegative
reals is a Lyapunov ranking function if there is an `ε > 0` such that
`v(s) ≥ Σ_{s'} P(s, s') v(s') + ε` at every state `s` where a step is enabled, that is at every
non-terminal state. Then the program terminates almost surely, and `v(s) / ε` bounds the expected
number of steps before termination (by Foster's theorem): it is positively almost surely
terminating. Bournez and Garnier take `v` real-valued and bounded below, which is the same up to a
shift. -/
theorem bournezGarnier (v : ForInStep σ → ℝ≥0) (ε : ℝ≥0) (hε : 0 < ε)
    (h : ∀ s, ∫⁻ t, (v t : ℝ≥0∞) ∂f s + ε ≤ v (.yield s)) (hf : IsMarkov f := by is_markov) :
    Terminates f b ∧ expectedSteps f b ≤ v (.yield b) / ε := by
  -- `ε` times the expected number of steps among the first `n` is at most `v`.
  have key : ∀ n s, (ε : ℝ≥0∞) * ∑ k ∈ Finset.range n, loopRun f k s Set.univ ≤ v (.yield s) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro s
      have hmeas : ∀ k, Measurable fun s' ↦ loopRun f k s' Set.univ := fun k ↦
        (Measure.measurable_coe MeasurableSet.univ).comp (measurable_loopRun hf.measurable k)
      have hsum : ∑ k ∈ Finset.range n, loopRun f (k + 1) s Set.univ =
          ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0)
            (fun s' ↦ ∑ k ∈ Finset.range n, loopRun f k s' Set.univ) ∂f s := by
        simp_rw [loopRun_succ_apply_univ hf.measurable]
        rw [← lintegral_finsetSum _ fun k _ ↦ measurable_casesOn' measurable_const (hmeas k)]
        exact lintegral_congr fun t ↦ by cases t <;> simp
      rw [Finset.sum_range_succ', hsum, loopRun_zero_apply_univ, mul_add, mul_one,
        ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      refine le_trans ?_ (h s)
      refine add_le_add_left (lintegral_mono fun t ↦ ?_) _
      cases t with
      | done _ => simp
      | yield s' => simpa using ih s'
  have hle : expectedSteps f b ≤ v (.yield b) / ε := by
    rw [expectedSteps, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun n ↦ ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hε.ne'))
      (Or.inl ENNReal.coe_ne_top), mul_comm]
    exact key n b
  refine ⟨ENNReal.tendsto_atTop_zero_of_tsum_ne_top (ne_top_of_le_ne_top ?_ hle), hle⟩
  exact ENNReal.div_ne_top ENNReal.coe_ne_top (ENNReal.coe_ne_zero.2 hε.ne')

end MeasurableSpaceMonadWhile
