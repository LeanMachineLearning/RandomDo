/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Monad.While
public import RandomDo.Tactic.IsMarkov.Elab

/-!
# Termination of `while` loops

`is_markov` hands back the termination of a `while` loop as a goal `Terminates f b`. This file
implements proof rules of the literature for it, each under the name of its authors and with the
hypotheses of its paper.

## Main results

* `Terminates.majumdarSathiyanarayana_martingaleRule`: the martingale rule of Majumdar and
  Sathiyanarayana (POPL 2025, Proof Rule 3.2), sound and relatively complete for almost-sure
  termination.
* `Terminates.majumdarSathiyanarayana_variantRule`: the variant rule of McIver and Morgan, as
  presented by Majumdar and Sathiyanarayana (POPL 2025, Proof Rule 3.1), derived from the
  martingale rule with the supermartingale `1`.
* `bournezGarnier`: the Lyapunov ranking functions of Bournez and Garnier (RTA 2005, Theorem 2),
  which give almost-sure termination with a bound on the expected number of steps.

## Implementation notes

The program is a probabilistic transition system whose states are the `ForInStep σ`: the successor
of `yield s` is drawn from `f s`, and the states `done s` are terminal. Every `rdo` loop is of this
form. It has no demonic nondeterminism, one step is one iteration of the loop, and "every successor"
is "almost every successor". The papers state these rules for discrete probabilistic choice; the
rules here hold for any measurable state space and any Markov kernel, and their measurability
conditions, which a discrete state space satisfies, have default proofs.

## References

* Annabelle McIver, Carroll Morgan, *Abstraction, Refinement and Proof for Probabilistic Systems*,
  2005.
* Rupak Majumdar, V. R. Sathiyanarayana, *Sound and Complete Proof Rules for Probabilistic
  Termination*, POPL 2025.
* Olivier Bournez, Florent Garnier, *Proving Positive Almost-Sure Termination*, RTA 2005.
* Luis María Ferrer Fioriti, Holger Hermanns, *Probabilistic Termination: Soundness, Completeness,
  and Compositionality*, POPL 2015.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal

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

/-- From a state of an invariant, a loop stops almost surely if a natural number `V`, bounded by `N`
on the invariant, is decreased or the loop stopped with probability at least `ε > 0` by every step
from the invariant. -/
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

/-- The stopped loop keeps the invariants of the loop. -/
private lemma ae_stopOn {A : Set σ} {I : σ → Prop}
    (h : ∀ s, I s → ∀ᵐ t ∂f s, ¬t.isDone → I t.run) :
    ∀ s, I s → ∀ᵐ t ∂stopOn A f s, ¬t.isDone → I t.run := by
  intro s hs
  by_cases hA : s ∈ A
  · -- Under the Dirac mass at a stop, every run has stopped.
    rw [stopOn_of_mem hA]
    have h0 : Measure.dirac (ForInStep.done s) (ForInStep.isDone ⁻¹' {false}) = 0 := by
      rw [Measure.dirac_apply' _ (ForInStep.measurable_isDone (measurableSet_singleton false))]
      simp
    refine measure_mono_null (fun t ht ↦ ?_) h0
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    cases hdone : t.isDone
    · rfl
    · exact absurd (fun h ↦ absurd hdone h) ht
  · rw [stopOn_of_notMem hA]
    exact h s hs

/-- The probability that the loop whose step is `f`, from `s`, is in `A` at one of its first `n + 1`
states while it has not stopped. -/
private noncomputable def hitRun (f : σ → Measure (ForInStep σ)) (A : Set σ) : ℕ → σ → ℝ≥0∞
  | 0, s => A.indicator 1 s
  | n + 1, s => open Classical in
      if s ∈ A then 1 else ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0)
        (hitRun f A n) ∂f s

private lemma measurable_hitRun (hf : Measurable f) {A : Set σ} (hA : MeasurableSet A) :
    ∀ n, Measurable (hitRun f A n)
  | 0 => measurable_const.indicator hA
  | n + 1 => by
    classical
    exact Measurable.ite hA measurable_const ((Measure.measurable_lintegral
      (measurable_casesOn measurable_const (measurable_hitRun hf hA n))).comp hf)

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
      rw [← lintegral_add_left (measurable_casesOn measurable_const hRun)]
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
    · rw [← lintegral_const_mul _ (measurable_casesOn measurable_const
        (measurable_hitRun hf.measurable hAm n))]
      refine le_trans (lintegral_mono_ae ?_) (hsuper s hs)
      filter_upwards [hI s hs] with t ht
      cases t with
      | done _ => simp
      | yield s' =>
        have := mul_hitRun_le_of_supermartingale I hI W hW hsuper r hA hAm n s' (by simpa using ht)
        simpa using this

namespace Terminates

/-- **Martingale rule for almost-sure termination** (Majumdar and Sathiyanarayana, *Sound and
Complete Proof Rules for Probabilistic Termination*, POPL 2025, Proof Rule 3.2 and Lemma 3.2).

The program is the transition system whose states are the `ForInStep σ`: the successor of a state
`yield s` is drawn from `f s`, and the states `done s` are terminal. To show that it terminates
almost surely from `yield b`, find
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

/-- **Variant rule for almost-sure termination** (McIver and Morgan 2005, in the form of Majumdar
and Sathiyanarayana, *Sound and Complete Proof Rules for Probabilistic Termination*, POPL 2025,
Proof Rule 3.1 and Lemma 3.1).

The program is the transition system of `majumdarSathiyanarayana_martingaleRule`. To show that it
terminates almost surely from `yield b`, find
1. an inductive invariant `Inv` containing `yield b`;
2. a variant function `U : Inv → ℤ`;
3. bounds `Lo` and `Hi` such that `Lo ≤ U < Hi` on `Inv`;
4. an `ε > 0`,

such that, for each state of `Inv`,
* (4.1) if it is terminal, `U = Lo`;
* (4.3) otherwise, the successors that decrease `U` have a total probability `> ε`.

Every non-terminal state is probabilistic, so condition (4.2) on assignment and nondeterministic
states does not apply, and "every successor" is "almost every successor". This is the martingale
rule with the supermartingale `1` on the non-terminal states and the variant `U - Lo`. -/
theorem majumdarSathiyanarayana_variantRule (Inv : ForInStep σ → Prop) (U : ForInStep σ → ℤ)
    (Lo Hi : ℤ) (ε : ℝ) (hε : 0 < ε) (hb : Inv (.yield b))
    (hInv : ∀ s, Inv (.yield s) → ∀ᵐ t ∂f s, Inv t)
    (hbounds : ∀ t, Inv t → Lo ≤ U t ∧ U t < Hi)
    (hdone : ∀ s, Inv (.done s) → U (.done s) = Lo)
    (hprog : ∀ s, Inv (.yield s) → ε < (f s {t | U t < U (.yield s)}).toReal)
    (hU : Measurable U := by fun_prop) (hf : IsMarkov f := by is_markov) : Terminates f b := by
  refine majumdarSathiyanarayana_martingaleRule Inv
    (fun t ↦ if t.isDone then 0 else 1) (fun t ↦ (U t - Lo).toNat) hb hInv
    (fun _ _ ↦ by simp) (fun _ _ ↦ by simp) (fun s _ ↦ ?_) (fun s hs ↦ by simp [hdone s hs])
    (fun _ ↦ ⟨(Hi - Lo).toNat, fun t ht _ ↦ by grind⟩)
    (fun _ ↦ ⟨ε, hε, fun s hs _ ↦ (hprog s hs).trans_le ?_⟩)
    (Measurable.ite (ForInStep.measurable_isDone (measurableSet_singleton true)) measurable_const
      measurable_const) ((Measurable.of_discrete (f := fun z : ℤ ↦ (z - Lo).toNat)).comp hU) hf
  · -- The constant `1` is a supermartingale, since a step has mass `1`.
    have := hf.isProbabilityMeasure s
    calc _ ≤ ∫⁻ _, 1 ∂f s := lintegral_mono fun t ↦ by split_ifs <;> simp
      _ = _ := by simp
  · -- Almost every successor is in `Inv`, where `U` decreases exactly when `U - Lo` does.
    have := hf.isProbabilityMeasure s
    refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
    rw [← measure_inter_conull (t := {t | Inv t})
      (by rw [Set.compl_ofPred]; exact ae_iff.1 (hInv s hs))]
    refine measure_mono fun t ⟨hlt, ht⟩ ↦ ?_
    have := (hbounds _ ht).1
    simp only [Set.mem_ofPred_eq] at hlt ⊢
    omega

end Terminates

/-- **Lyapunov ranking functions** (Bournez and Garnier, *Proving positive almost-sure termination*,
RTA 2005, Theorem 2, in the form recalled by Ferrer Fioriti and Hermanns, *Probabilistic
Termination: Soundness, Completeness, and Compositionality*, POPL 2015, equation (1)).

The program is the transition system whose states are the `ForInStep σ`, as in
`Terminates.majumdarSathiyanarayana_martingaleRule`. A map `v` from its states to the nonnegative
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
        rw [← lintegral_finsetSum _ fun k _ ↦ measurable_casesOn measurable_const (hmeas k)]
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
