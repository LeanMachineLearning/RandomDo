/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import Mathlib.Probability.Distributions.Geometric
public import RandomDo.MeasurableSpaceMonad.Instances.Measure.Loop
public import RandomDo.RDo.Loop
public import RandomDo.Sampling.Measure
public import RandomDo.WP.ForIn
public import RandomDo.WP.Measure
import Lean.Elab.Tactic.VCGen

/-!
# Flipping a coin until heads

`untilHeads` is a polymorphic program counting the tails before the first head. Under `Measure`,
`untilHeads_eq_geometric` proves that its distribution is Mathlib's `geometricMeasure p` for
`p ≠ 0`. In particular, a fair coin returns `n` with probability `2⁻¹ ^ (n + 1)`.

The proof exercises the actual `while` syntax, mutable state, sampling, `break`, the enclosing
`return`, and `invariant` and `decreasing` clauses read by stock `vcgen`. The annotated copy is
definitionally equal to the original program: its extra `target` parameter affects only the
proof annotations.

For each target `k`, the invariant is `(1 - p) ^ (k - n) * p` when the current tail count `n`
is at most `k`, and zero otherwise. On exit it is the indicator of `n = k`. The natural-valued
variant `k + 1 - n` decreases on each continuing step while `n ≤ k`. Once the count exceeds `k`,
the invariant is zero and the verification condition is trivial, even if the loop keeps running.
The variant therefore proves a lower bound on the probability of returning `k`; it does not
impose a cutoff or claim that all executions finish within `k + 1` flips.

These bounds are obtained without assuming almost-sure termination. Summing them gives total
mass at least one for `p ≠ 0`. Probability-preserving steps give total mass at most one, hence
`untilHeads_prob` and `untilHeads_terminates`. Equality with the geometric distribution follows.
This uses the existing well-founded variant rule; no probabilistic termination rule is imported.

The zero-probability case checks that a loop which never exits returns zero measure.
It deliberately differs from Mathlib's convention `geometricMeasure 0 = dirac 0`.
-/

set_option experimental.vcgen true
set_option experimental.intrinsic true

@[expose] public section

open MeasureTheory Measure ProbabilityTheory HasBernoulli Std.WP unitInterval
open scoped ENNReal

namespace TestNext.Geometric

/-- Count tails before the first head, using the chosen sampling and loop interpretations. -/
def untilHeads {m : (α : Type) → [MeasurableSpace α] → Type*}
    [MeasurableSpaceMonad m] [MeasurableSpaceForIn m Lean.Loop Unit]
    {P : Type} [HasBernoulli m P] (p : P) : m ℕ := rdo
  let mut tails := 0
  while true rdo
    let heads ← bernoulli p
    if heads then break
    tails := tails + 1
  return tails

/-- The probability of returning `target` when the loop has already counted `tails` tails. -/
noncomputable def hitProbability (p : unitInterval) (target tails : ℕ) : ℝ≥0∞ :=
  if tails ≤ target then (toNNReal (σ p) : ℝ≥0∞) ^ (target - tails) * toNNReal p else 0

/-- The same program with an invariant and a variant for the event `result = target`. -/
noncomputable def untilHeadsAnnotated (p : unitInterval) (target : ℕ) : Measure ℕ := rdo
  let mut tails := 0
  while true
    invariant done =>
      if done then (if tails = target then 1 else 0 : ℝ≥0∞)
      else hitProbability p target tails
    decreasing target + 1 - tails
  rdo
    let heads ← bernoulli p
    if heads then break
    tails := tails + 1
  return tails

-- An annotation must not change the program, including when its proof parameter changes.
lemma untilHeadsAnnotated_eq (p : unitInterval) (target : ℕ) :
    untilHeadsAnnotated p target = untilHeads p := rfl

-- Expose the generated body for the mass bound and termination statement.
noncomputable def step (p : unitInterval) (tails : ℕ) : Measure (ForInStep ℕ) := rdo
  let heads ← bernoulli p
  if heads then return .done tails
  else return .yield (tails + 1)

lemma untilHeads_eq_loop (p : unitInterval) : untilHeads p = loop (step p) 0 := by
  simp only [untilHeads, mBind_mPure, ite_true]
  rfl

lemma step_eq (p : unitInterval) (tails : ℕ) :
    step p tails = toNNReal p • dirac (.done tails) +
      toNNReal (σ p) • dirac (.yield (tails + 1)) := by
  ext s hs
  simp only [step, mBind, mPure]
  rw [bind_apply hs (measurable_of_countable _).aemeasurable]
  simp [bernoulli, bernoulliMeasure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac]

lemma step_prob (p : unitInterval) (tails : ℕ) : step p tails Set.univ = 1 := by
  simp [step_eq]

lemma hitProbability_step (p : unitInterval) (target tails : ℕ) :
    hitProbability p target tails =
      toNNReal p * (if tails = target then 1 else 0) +
        toNNReal (σ p) * hitProbability p target (tails + 1) := by
  by_cases h : tails = target
  · subst tails
    simp [hitProbability]
  · by_cases hlt : tails < target
    · have he : target - tails = (target - (tails + 1)) + 1 := by omega
      simp [hitProbability, h, Nat.le_of_lt hlt, hlt, he, pow_succ, mul_left_comm, mul_comm]
    · simp [hitProbability, h, show ¬ tails ≤ target by omega,
        show ¬ tails + 1 ≤ target by omega]

-- The one sampling rule needed by vcgen; it is supplied explicitly at the call site.
lemma bernoulli_spec (p : unitInterval) (Q : Bool → ℝ≥0∞) :
    Triple (bernoulli (m := Measure) p)
      (toNNReal p * Q true + toNNReal (σ p) * Q false) Q estack⟨⟩ := by
  constructor
  simp [wp_eq_lintegral, bernoulli, bernoulliMeasure, lintegral_add_measure,
    lintegral_smul_measure, ENNReal.smul_def, -coe_nnreal_smul, lintegral_dirac]

-- The source-level invariant and decreasing clause give the singleton bound without a
-- termination hypothesis, even at p = 0. The zero-invariant branch needs no decrease.
lemma untilHeadsAnnotated_spec (p : unitInterval) (target : ℕ) :
    Triple (untilHeadsAnnotated p target)
      (hitProbability p target 0) (fun n => if n = target then 1 else 0) estack⟨⟩ := by
  simp only [untilHeadsAnnotated, mBind_mPure]
  vcgen [bernoulli_spec]
  all_goals try fun_prop
  all_goals try (solve | simp_all)
  case vc6 mb _ =>
    by_cases heq : target + 1 - tails = mb
    · subst mb
      by_cases hle : tails ≤ target
      · have hlt : target - tails < target + 1 - tails := by omega
        simpa [mPure, wp_eq_lintegral, lintegral_dirac' _
          (measurable_fun_forInStep measurable_from_nat measurable_from_nat), hlt] using
          (hitProbability_step p target tails).le
      · simp [hitProbability, hle]
    · simp [heq]
  case vc8 =>
    exact measurable_fun_forInStep measurable_from_nat measurable_from_nat

lemma singleton_lower_bound (p : unitInterval) (target : ℕ) :
    (toNNReal (σ p) : ℝ≥0∞) ^ target * toNNReal p ≤
      untilHeads (m := Measure) p {target} := by
  have h := (untilHeadsAnnotated_spec p target).le_wp
  rw [untilHeadsAnnotated_eq, wp_eq_lintegral] at h
  rw [← lintegral_indicator_one (measurableSet_singleton target)]
  simpa [hitProbability, Set.indicator_apply] using h

-- Sum the singleton bounds obtained from the variant proof.
lemma geometricMeasure_le_untilHeads {p : unitInterval} (hp : p ≠ 0) :
    geometricMeasure p ≤ untilHeads (m := Measure) p := by
  rw [geometricMeasure_eq hp, ← sum_smul_dirac (untilHeads (m := Measure) p)]
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.tsum_le_tsum
  intro n
  apply mul_le_mul' _ le_rfl
  rw [ENNReal.ofReal_mul (pow_nonneg (sub_nonneg.mpr p.2.2) _),
    ENNReal.ofReal_pow (sub_nonneg.mpr p.2.2)]
  rw [← unitInterval.coe_symm_eq p, ← unitInterval.coe_toNNReal (σ p),
    ← unitInterval.coe_toNNReal p,
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  exact singleton_lower_bound p n

-- The lower bounds exhaust probability one, so no mass can be lost to infinite runs.
lemma untilHeads_prob {p : unitInterval} (hp : p ≠ 0) :
    IsProbabilityMeasure (untilHeads (m := Measure) p) := by
  constructor
  apply le_antisymm
  · rw [untilHeads_eq_loop]
    exact loop_apply_univ_le_one measurable_from_nat (step_prob p) 0
  · simpa using geometricMeasure_le_untilHeads hp Set.univ

lemma untilHeads_terminates {p : unitInterval} (hp : p ≠ 0) :
    Terminates (step p) 0 := by
  apply (isProbabilityMeasure_loop_iff measurable_from_nat (step_prob p) 0).mp
  simpa [untilHeads_eq_loop] using untilHeads_prob hp

-- Equal total mass upgrades domination to equality of measures.
lemma untilHeads_eq_geometric {p : unitInterval} (hp : p ≠ 0) :
    untilHeads (m := Measure) p = geometricMeasure p := by
  have := untilHeads_prob hp
  exact (Measure.eq_of_le_of_isProbabilityMeasure (geometricMeasure_le_untilHeads hp)).symm

lemma untilHeads_singleton {p : unitInterval} (hp : p ≠ 0) (n : ℕ) :
    untilHeads (m := Measure) p {n} = ENNReal.ofReal ((1 - p) ^ n * p) := by
  rw [untilHeads_eq_geometric hp, geometricMeasure_singleton hp]

-- Zero success probability must not normalize an endlessly running loop.
lemma untilHeads_zero : untilHeads (m := Measure) (0 : unitInterval) = 0 := by
  have h : ∀ n tails, loopExit (step 0) n tails = 0 := by
    intro n
    induction n with
    | zero =>
      intro tails
      simp (disch := (apply measurable_fun_forInStep <;> fun_prop))
        [loopExit, step_eq, dirac_bind]
    | succ n ih =>
      intro tails
      simp (disch := (apply measurable_fun_forInStep <;> fun_prop))
        [loopExit, step_eq, dirac_bind, ih]
  simp [untilHeads_eq_loop, loop, h]

/-- The probability parameter for a fair coin. -/
noncomputable def fairCoinProbability : unitInterval := ⟨1 / 2, by norm_num⟩

theorem untilHeads_fair (n : ℕ) :
    untilHeads (m := Measure) fairCoinProbability {n} = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  rw [untilHeads_singleton (by
    norm_num [fairCoinProbability, Subtype.ext_iff] : fairCoinProbability ≠ 0)]
  norm_num [fairCoinProbability, ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    ENNReal.ofReal_div_of_pos, pow_succ]

end TestNext.Geometric
