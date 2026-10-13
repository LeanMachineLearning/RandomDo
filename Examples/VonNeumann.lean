/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Verification
public import RandomDo.Tactic.IsMarkov.Elab

/-!
# Von Neumann's bounded fair-coin sampler

Each attempt draws two independent coins with bias `p`. A differing pair returns its first coin;
a matching pair is discarded. After `n` unsuccessful attempts the sampler returns `none`.

The quantitative Hoare proof uses an invariant for the number of attempts remaining. It determines
the whole output measure, including the probability of exhausting the budget. It is valid even
for the endpoint biases `0` and `1`, at which the sampler always returns `none`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Std.Internal.Do
open scoped ENNReal unitInterval ProbabilityTheory

set_option mvcgen.warning false

namespace Examples.VonNeumann

noncomputable section

/-- Probability that the two coins in one attempt agree. -/
def rejectProb (p : I) : NNReal :=
  unitInterval.toNNReal p ^ 2 + unitInterval.toNNReal (unitInterval.symm p) ^ 2

/-- Probability of either particular differing pair in one attempt. -/
def pairProb (p : I) : NNReal :=
  unitInterval.toNNReal p * unitInterval.toNNReal (unitInterval.symm p)

theorem pairProb_add_pairProb_add_rejectProb (p : I) :
    pairProb p + pairProb p + rejectProb p = 1 := by
  have hp := unitInterval.toNNReal_add_toNNReal_symm p
  calc
    _ = (unitInterval.toNNReal p + unitInterval.toNNReal (unitInterval.symm p)) ^ 2 := by
      unfold pairProb rejectProb
      ring
    _ = 1 := by rw [hp]; norm_num

theorem rejectProb_le_one (p : I) : rejectProb p ≤ 1 := by
  rw [← pairProb_add_pairProb_add_rejectProb p]
  exact le_add_left (le_refl _)

/-- Probability of exhausting `n` attempts. -/
def failureProb (p : I) (n : ℕ) : NNReal := rejectProb p ^ n

/-- Probability of either particular successful Boolean result within `n` attempts. -/
def successProb (p : I) (n : ℕ) : NNReal := (1 - failureProb p n) / 2

@[simp] theorem failureProb_zero (p : I) : failureProb p 0 = 1 := by simp [failureProb]

@[simp] theorem successProb_zero (p : I) : successProb p 0 = 0 := by simp [successProb]

theorem failureProb_le_one (p : I) (n : ℕ) : failureProb p n ≤ 1 :=
  pow_le_one₀ (by positivity) (rejectProb_le_one p)

theorem failureProb_succ (p : I) (n : ℕ) :
    failureProb p (n + 1) = rejectProb p * failureProb p n := by
  simp [failureProb, pow_succ, mul_comm]

theorem successProb_succ (p : I) (n : ℕ) :
    successProb p (n + 1) = pairProb p + rejectProb p * successProb p n := by
  have h := pairProb_add_pairProb_add_rejectProb p
  apply NNReal.eq
  have h' := congrArg (fun x : NNReal ↦ (x : ℝ)) h
  simp only [NNReal.coe_add, NNReal.coe_one] at h'
  simp only [successProb, NNReal.coe_div, NNReal.coe_sub (failureProb_le_one p n),
    NNReal.coe_sub (failureProb_le_one p (n + 1)), NNReal.coe_ofNat, NNReal.coe_mul,
    NNReal.coe_add, NNReal.coe_one]
  rw [failureProb_succ, NNReal.coe_mul]
  nlinarith

theorem failureProb_add_successProb_add_successProb (p : I) (n : ℕ) :
    failureProb p n + successProb p n + successProb p n = 1 := by
  apply NNReal.eq
  simp only [successProb, NNReal.coe_div, NNReal.coe_sub (failureProb_le_one p n),
    NNReal.coe_ofNat, NNReal.coe_add, NNReal.coe_one]
  ring

/-- Attempt to generate a fair coin at most `n` times, using an actual finite `rdo` loop. -/
def sample (p : I) (n : ℕ) : Measure (Option Bool) := rdo
  let mut result := none
  for _ in List.replicate n () rdo
    let a ← Ber(true, false, p)
    let b ← Ber(true, false, p)
    if a ≠ b then
      result := some a
      break
  return result

instance (p : I) (n : ℕ) : IsProbabilityMeasure (sample p n) := by
  have h : IsMarkov (fun _ : Unit ↦ sample p n) := by
    unfold sample
    is_markov
  exact h.isProbabilityMeasure ()

/-- The postexpectation propagated backward through the remaining attempts. -/
def invariant (p : I) (n : ℕ) (Q : Option Bool → ℝ≥0∞) (b : Option Bool) : ℝ≥0∞ :=
  (failureProb p n : ℝ≥0∞) * Q b +
    (successProb p n : ℝ≥0∞) * (Q (some true) + Q (some false))

@[simp] theorem invariant_zero (p : I) (Q : Option Bool → ℝ≥0∞) (b : Option Bool) :
    invariant p 0 Q b = Q b := by simp [invariant]

/-- Every nonnegative postexpectation satisfies the exact distributional lower bound. -/
@[spec] theorem sample_spec (p : I) (n : ℕ) (Q : Option Bool → ℝ≥0∞) :
    Triple (sample p n) (invariant p n Q none) Q ⟨⟩ := by
  vcgen [sample] invariants
  · fun _ suff b ↦ invariant p suff.length Q b
  all_goals try exact Measurable.of_discrete
  all_goals simp only [ENNReal.leanOrder_le_iff, List.length_replicate, List.length_nil,
    invariant_zero, le_refl]
  simp (disch := exact Measurable.of_discrete) only [Measure.wp_mBind, wp_bernoulliMeasure,
    Measure.wp_mPure, List.length_cons, Bool.true_eq_false,
    Bool.false_eq_true, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
  apply le_of_eq
  simp only [invariant, failureProb_succ, successProb_succ, rejectProb, pairProb,
    ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_pow]
  ring

/-- The intended output measure: a possible failure and two equally likely Boolean results. -/
def outputMeasure (p : I) (n : ℕ) : Measure (Option Bool) :=
  failureProb p n • Measure.dirac none +
    successProb p n • Measure.dirac (some true) +
    successProb p n • Measure.dirac (some false)

instance (p : I) (n : ℕ) : IsProbabilityMeasure (outputMeasure p n) where
  measure_univ := by
    simp only [outputMeasure, Measure.add_apply, Measure.smul_apply, measure_univ,
      ENNReal.smul_def, smul_eq_mul, mul_one]
    exact_mod_cast failureProb_add_successProb_add_successProb p n

theorem wp_outputMeasure (p : I) (n : ℕ) (Q : Option Bool → ℝ≥0∞) (E : EPost.Nil) :
    wp (outputMeasure p n) Q E = invariant p n Q none := by
  simp only [Measure.wp_eq_lintegral, outputMeasure, lintegral_add_measure,
    lintegral_smul_measure, lintegral_dirac]
  change (failureProb p n : ℝ≥0∞) * Q none +
    (successProb p n : ℝ≥0∞) * Q (some true) +
    (successProb p n : ℝ≥0∞) * Q (some false) = _
  simp only [invariant]
  ring

/-- Correctness of the sampler, deduced from its quantitative Hoare specification. -/
theorem sample_eq_outputMeasure (p : I) (n : ℕ) : sample p n = outputMeasure p n := by
  apply Measure.eq_of_forall_triple
  intro Q _
  simpa only [wp_outputMeasure] using sample_spec p n Q

@[simp] theorem wp_sample (p : I) (n : ℕ) (Q : Option Bool → ℝ≥0∞) (E : EPost.Nil) :
    wp (sample p n) Q E = invariant p n Q none := by
  rw [sample_eq_outputMeasure, wp_outputMeasure]

@[simp] theorem sample_zero_budget (p : I) : sample p 0 = Measure.dirac none := by
  simp [sample_eq_outputMeasure, outputMeasure]

@[simp] theorem sample_zero (n : ℕ) : sample 0 n = Measure.dirac none := by
  simp [sample_eq_outputMeasure, outputMeasure, failureProb, successProb, rejectProb]

@[simp] theorem sample_one (n : ℕ) : sample 1 n = Measure.dirac none := by
  simp [sample_eq_outputMeasure, outputMeasure, failureProb, successProb, rejectProb]

/-- The probability of exhausting the budget is the probability of `n` matching pairs. -/
@[simp] theorem sample_none (p : I) (n : ℕ) :
    sample p n {none} = (failureProb p n : ℝ≥0∞) := by
  rw [sample_eq_outputMeasure]
  simp [outputMeasure]

/-- Each Boolean outcome receives half of the probability of a successful attempt. -/
@[simp] theorem sample_some (p : I) (n : ℕ) (b : Bool) :
    sample p n {some b} = (successProb p n : ℝ≥0∞) := by
  rw [sample_eq_outputMeasure]
  cases b <;> simp [outputMeasure]

/-- The two successful outcomes are equally likely, for every budget and every bias. -/
theorem sample_fair (p : I) (n : ℕ) : sample p n {some true} = sample p n {some false} := by
  rw [sample_some, sample_some]

end
end Examples.VonNeumann
