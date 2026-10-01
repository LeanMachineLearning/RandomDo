/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Tactic.IsMarkov.Elab
public import RandomDo.Tactic.IsMarkov.While.LoopInvariant

/-!
# Termination of `while` loops

`is_markov` hands back the termination of a `while` loop as a goal `Terminates f b`. This file
implements proof rules of the literature for it, each under the name of its authors and with the
hypotheses of its paper.

## Main results

* `Terminates.mcIverMorgan_zeroOneLaw`: the zero-one law of McIver and Morgan (2005,
  Lemma 2.6.1).
* `Terminates.majumdarSathiyanarayana_variantRule`: the variant rule of McIver and Morgan, as
  presented by Majumdar and Sathiyanarayana (POPL 2025, Proof Rule 3.1), derived from the zero-one
  law as McIver and Morgan derive their variant rule (2005, Lemma 2.7.1).
* `Terminates.mcIverMorgan_immediateEscape`: termination when every step stops with probability at
  least some fixed `ε > 0`, the stronger condition McIver and Morgan remark after their zero-one law
  (2005, p. 54).

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
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasurableSpaceMonadWhile

universe u

variable {σ : Type u} [MeasurableSpace σ] {f : σ → Measure (ForInStep σ)} {b : σ}

namespace Terminates

/-- **Zero-one law** (McIver and Morgan 2005, Lemma 2.6.1, stated informally there; its conditions
are formalised by (2.12) with `I = [Inv]`, footnote 27).

The program is the transition system whose states are the `ForInStep σ`: the successor of a state
`yield s` is drawn from `f s`, and the states `done s` are terminal. Let `I` be an invariant, the
paper's `Inv`, with `I.running b`. If, from every non-terminal state of `I`, the program terminates
with probability at least some fixed `ε > 0`, then it terminates almost surely from `yield b`. The
probability of terminating from `s` is the mass of the loop `loop f s`. -/
theorem mcIverMorgan_zeroOneLaw (I : LoopInvariant f) (ε : ℝ) (hε : 0 < ε) (hb : I.running b)
    (hterm : ∀ s, I.running s → ε ≤ (loop f s Set.univ).toReal)
    (hf : IsMarkov f := by is_markov) : Terminates f b := by
  -- The probability `r s` that the loop never stops from `s`.
  set r : σ → ℝ≥0∞ := fun s ↦ ⨅ n, loopRun f n s Set.univ
  have hr s : Tendsto (fun n ↦ loopRun f n s Set.univ) atTop (𝓝 (r s)) :=
    tendsto_atTop_iInf (antitone_loopRun_apply_univ f s)
  -- It is `1` minus the probability that the loop stops, so at most `1 - ε` on `I`.
  have hrInv : ∀ s, I.running s → r s ≤ 1 - ENNReal.ofReal ε := fun s hs ↦ by
    rw [tendsto_nhds_unique (hr s) (tendsto_loopRun_apply_univ f s)]
    exact tsub_le_tsub_left (ENNReal.ofReal_le_of_le_toReal (hterm s hs)) 1
  -- The loop never stops from `s` when one step carries on and it never stops from there.
  have hstep s : r s = ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0) r ∂f s := by
    have := hf.isProbabilityMeasure s
    refine tendsto_nhds_unique ((hr s).comp (tendsto_add_atTop_nat 1)) ?_
    simp_rw [Function.comp_def, loopRun_succ_apply_univ hf.measurable]
    refine tendsto_lintegral_of_dominated_convergence 1 (fun n ↦ measurable_casesOn
      measurable_const ((Measure.measurable_coe MeasurableSet.univ).comp
        (measurable_loopRun hf.measurable n))) (fun n ↦ .of_forall fun t ↦ ?_) (by simp)
      (.of_forall fun t ↦ ?_)
    · cases t <;> simp [loopRun_apply_univ_le_one]
    · cases t with
      | done _ => exact tendsto_const_nhds
      | yield s' => exact hr s'
  -- So the loop never stops with probability at most `(1 - ε)` times that it goes on for `m` steps.
  have key : ∀ m s, I.running s → r s ≤ (1 - ENNReal.ofReal ε) * loopRun f m s Set.univ := by
    intro m
    induction m with
    | zero => exact fun s hs ↦ by simpa using hrInv s hs
    | succ m ih =>
      intro s hs
      rw [hstep s, loopRun_succ_apply_univ hf.measurable,
        ← lintegral_const_mul' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
      refine lintegral_mono_ae ?_
      filter_upwards [I.step s hs] with t ht
      cases t with
      | done _ => simp
      | yield s' => simpa using ih s' ht
  -- In the limit, `r b ≤ (1 - ε) r b`, so `r b = 0`.
  have hle : r b ≤ (1 - ENNReal.ofReal ε) * r b := ge_of_tendsto'
    (ENNReal.Tendsto.const_mul (hr b) (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top
      tsub_le_self))) fun m ↦ key m b hb
  have hr0 : r b = 0 := by
    by_contra h
    have hrb : r b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
      ((iInf_le _ 0).trans (loopRun_apply_univ_le_one f 0 b))
    have hlt : 1 - ENNReal.ofReal ε < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ENNReal.ofReal_pos.2 hε).ne'
    exact (ENNReal.mul_lt_mul_left h hrb hlt).not_ge (by simpa using hle)
  simpa [Terminates, hr0] using hr b

/-- **Variant rule for almost-sure termination** (McIver and Morgan 2005, in the form of Majumdar
and Sathiyanarayana, *Sound and Complete Proof Rules for Probabilistic Termination*, POPL 2025,
Proof Rule 3.1 and Lemma 3.1).

The program is the transition system of `mcIverMorgan_zeroOneLaw`. To show that it terminates
almost surely from `yield b`, find
1. an inductive invariant `Inv` containing `yield b`, here an invariant `I` with `I.running b`;
2. a variant function `U : Inv → ℤ`;
3. bounds `Lo` and `Hi` such that `Lo ≤ U < Hi` on `Inv`;
4. an `ε > 0`,

such that, for each non-terminal state of `Inv`, (4.3) the successors that decrease `U` have a total
probability `> ε`.

Every non-terminal state is probabilistic, so condition (4.2) on assignment and nondeterministic
states does not apply, and "every successor" is "almost every successor". Condition (4.1), `U = Lo`
on the terminal states, is not needed and is dropped: the rule of the paper follows by forgetting
it. Setting `U = Lo` on the terminal states still makes stopping count as decreasing `U`.

As in McIver and Morgan's proof of their variant rule (Lemma 2.7.1), the program terminates within
`Hi - Lo` steps with probability at least `ε ^ (Hi - Lo)` from every state of `Inv`, and the
zero-one law concludes. -/
theorem majumdarSathiyanarayana_variantRule (I : LoopInvariant f) (U : ForInStep σ → ℤ)
    (Lo Hi : ℤ) (ε : ℝ) (hε : 0 < ε) (hb : I.running b)
    (hbounds : ∀ t, I t → Lo ≤ U t ∧ U t < Hi)
    (hprog : ∀ s, I.running s → ε < (f s {t | U t < U (.yield s)}).toReal)
    (hU : Measurable U := by fun_prop) (hf : IsMarkov f := by is_markov) : Terminates f b := by
  have hprog' s (hs : I.running s) : ENNReal.ofReal ε ≤ f s {t | U t < U (.yield s)} :=
    ENNReal.ofReal_le_of_le_toReal (hprog s hs).le
  have hε1 s (hs : I.running s) : ENNReal.ofReal ε ≤ 1 := by
    have := hf.isProbabilityMeasure s
    exact (hprog' s hs).trans prob_le_one
  -- From a state of `I` where `U - Lo < n`, the loop goes on for `n` steps with probability at
  -- most `1 - εⁿ`.
  have key : ∀ n s, I.running s → (U (.yield s) - Lo).toNat < n →
      loopRun f n s Set.univ ≤ 1 - ENNReal.ofReal ε ^ n := by
    intro n
    induction n with
    | zero => exact fun s _ hs ↦ absurd hs (Nat.not_lt_zero _)
    | succ n ih =>
      intro s hs hUs
      set S := {t : ForInStep σ | U t < U (.yield s)}
      have hS : MeasurableSet S := hU measurableSet_Iio
      have := hf.isProbabilityMeasure s
      rw [loopRun_succ_apply_univ hf.measurable]
      calc _ ≤ ∫⁻ t, 1 - S.indicator (fun _ ↦ ENNReal.ofReal ε ^ n) t ∂f s := by
            refine lintegral_mono_ae ?_
            filter_upwards [I.step s hs] with t ht
            cases t with
            | done _ => simp
            | yield s' =>
              by_cases hlt : U (.yield s') < U (.yield s)
              · have := (hbounds (.yield s') ht).1
                simpa [S, hlt] using ih s' ht (by omega)
              · simpa [S, hlt] using loopRun_apply_univ_le_one f n s'
        _ = 1 - ENNReal.ofReal ε ^ n * f s S := by
          rw [lintegral_sub (measurable_const.indicator hS), lintegral_indicator_const hS]
          · simp
          · rw [lintegral_indicator_const hS]
            exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
          · exact .of_forall fun t ↦
              Set.indicator_le (fun _ _ ↦ pow_le_one₀ bot_le (hε1 s hs)) t
        _ ≤ 1 - ENNReal.ofReal ε ^ (n + 1) :=
          tsub_le_tsub_left (by rw [pow_succ]; gcongr; exact hprog' s hs) 1
  -- So the loop stops with probability at least `ε ^ (Hi - Lo)` from every state of `I`.
  refine mcIverMorgan_zeroOneLaw I (ε ^ (Hi - Lo).toNat) (pow_pos hε _) hb
    (fun s hs ↦ ?_) hf
  have hloop : loop f s Set.univ ≤ 1 := measure_loop_univ_le_one (fun s ↦ by
    have := hf.isProbabilityMeasure s
    exact prob_le_one) s
  have hlim : 1 - loop f s Set.univ ≤ 1 - ENNReal.ofReal ε ^ (Hi - Lo).toNat := by
    refine le_of_tendsto (tendsto_loopRun_apply_univ f s) (eventually_atTop.2 ⟨_, fun n hn ↦
      (antitone_loopRun_apply_univ f s hn).trans (key _ s hs ?_)⟩)
    have := hbounds (.yield s) hs
    omega
  rw [ENNReal.sub_le_sub_iff_left (pow_le_one₀ bot_le (hε1 s hs)) ENNReal.one_ne_top,
    ← ENNReal.ofReal_pow hε.le] at hlim
  exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hloop)).1 hlim

/-- **Immediate escape** (McIver and Morgan 2005, p. 54: the stronger condition they remark after
the zero-one law, Lemma 2.6.1).

If, from every non-terminal state of the invariant `I`, one step stops with probability at least
some fixed `ε > 0`, then the program terminates almost surely from `yield b`. This is the condition
of a rejection sampling loop, which stops as soon as its sample satisfies a property of probability
at least `ε`. It is the variant rule with the variant `1` on the non-terminal states and `0` on the
terminal ones. -/
theorem mcIverMorgan_immediateEscape (I : LoopInvariant f) (ε : ℝ) (hε : 0 < ε) (hb : I.running b)
    (hstop : ∀ s, I.running s → ε ≤ (f s {t | t.isDone}).toReal)
    (hf : IsMarkov f := by is_markov) : Terminates f b := by
  refine majumdarSathiyanarayana_variantRule I (fun t ↦ if t.isDone then 0 else 1) 0 2 (ε / 2)
    (half_pos hε) hb (fun t _ ↦ by split_ifs <;> simp) (fun s hs ↦ ?_)
    (Measurable.ite (ForInStep.measurable_isDone (measurableSet_singleton true))
      measurable_const measurable_const) hf
  -- The successors that decrease the variant are the terminal ones.
  refine (half_lt_self hε).trans_le ((hstop s hs).trans_eq ?_)
  congr 2
  ext t
  cases t <;> simp

end Terminates

end MeasurableSpaceMonadWhile
