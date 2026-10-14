/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Kernel.KernelSub
public import RandomDo.ForMathlib.MeasureTheory.Measure.TotalVariation.DataProcessing
public import RandomDo.ForMathlib.Probability.Kernel.Aperiodic
public import RandomDo.ForMathlib.Probability.Kernel.HarrisRecurrent
public import RandomDo.ForMathlib.Probability.Kernel.Invariance
public import RandomDo.ForMathlib.Probability.Kernel.SmallSet.Exists

/-!
# Convergence in total variation of irreducible aperiodic Markov kernels

Let `κ : Kernel α α` be a Markov kernel on a countably generated measurable space, with an
invariant probability measure `π`. If `κ` is irreducible and aperiodic, then for `π`-almost every
`x`, the law `(κ ^ n) x` at time `n` of the Markov chain with kernel `κ` started at `x` converges
to `π` in total variation. If `κ` is Harris recurrent, this holds for every `x`. A Harris recurrent
Markov kernel is irreducible (`Kernel.IsHarrisRecurrent.isIrreducible`), hence the statements for
Harris recurrent kernels do not assume irreducibility.

Note that the total variation distance `tvDist` takes values in `[0, 2]` for probability measures:
it is twice the supremum over measurable sets of the difference of the measures.

## Main statements

* `Kernel.ae_tendsto_tvDist_pow_apply`: `tvDist ((κ ^ n) x) π` tends to zero for `π`-almost
  every `x`.
* `Kernel.tendsto_tvDist_pow_comp`: `tvDist ((κ ^ n) ∘ₘ μ) π` tends to zero for every probability
  measure `μ ≪ π`.
* `Kernel.IsHarrisRecurrent.tendsto_tvDist_pow_apply`: if `κ` is Harris recurrent, then
  `tvDist ((κ ^ n) x) π` tends to zero for every `x`.
* `Kernel.IsHarrisRecurrent.tendsto_tvDist_pow_comp`: if `κ` is Harris recurrent, then
  `tvDist ((κ ^ n) ∘ₘ μ) π` tends to zero for every probability measure `μ`.

Each of these statements has a version for the extended distance `etvDist`.

Intermediate results which do not mention irreducibility or aperiodicity:

* `Kernel.exists_isSmallSet_measure_compl_le`: if a small set is reached from every point at all
  large times, then there are small sets of `π`-measure arbitrarily close to full.
* `Kernel.tendsto_etvDist_pow_comp_of_le`: under the same assumption, `(κ ^ n) ∘ₘ a` tends to
  `a univ • π` in total variation for every measure `a` dominated by a multiple of `π`.

## Proof

The proof does not use the law of the trajectories of the Markov chain: it only manipulates
measures and kernels.

1. There is a small set `C` (`Kernel.exists_isSmallSet`), and by aperiodicity every point
  reaches `C` with positive probability in `n` steps for all `n` large enough
  (`Kernel.IsAperiodic.exists_forall_pow_apply_pos`). It follows that for every `θ > 0` there is a
  small set `B` with `π Bᶜ ≤ θ` (`Kernel.exists_isSmallSet_measure_compl_le`).
2. Let `a ≤ K • π` be an initial measure. We write `(κ ^ (j * i)) ∘ₘ a` and `a univ • π` as sums of
  a common part and of remainders with equal mass, which are still dominated by `K • π`. The
  remainders give mass at most `K * θ` to `Bᶜ`, and their restrictions to the small set `B` have a
  common part after `j` more steps. Hence the mass of the remainders decreases geometrically
  with `i`, up to a term of order `K * θ` (`Kernel.etvDist_pow_comp_le`). Since `θ` is arbitrary,
  `(κ ^ n) ∘ₘ a` tends to `a univ • π` (`Kernel.tendsto_etvDist_pow_comp_of_le`).
3. For a general starting point `x`, let `r i x` be the mass of `(κ ^ i) x - i • π`, the part of
  `(κ ^ i) x` which is not dominated by `i • π`. It is nonincreasing in `i`, and its limit `ρ x` is
  a subharmonic function of `x`: `ρ x ≤ ∫⁻ y, ρ y ∂κ x`. The existence of a small set gives
  `ρ x < 1` for all `x`, and a subharmonic function of an irreducible kernel with an invariant
  probability measure is almost everywhere less than any level which it does not exceed on a set of
  positive measure (`Kernel.Invariant.ae_le_of_le_lintegral`). Hence `ρ ≤ t` almost everywhere for
  some `t < 1`. Together with the inequality `ρ x ≤ ∫⁻ y, ρ y ∂((κ ^ i) x - i • π)`, this gives
  `ρ x ≤ t * ρ x` and then `ρ x = 0` for almost every `x`.
4. If `ρ x = 0`, then `(κ ^ i) x` is the sum of a measure dominated by `i • π`, to which step 2
  applies, and of a measure with arbitrarily small mass.
5. If `κ` is Harris recurrent, then `ρ x = 0` for every `x`: by subharmonicity and since `ρ`
  vanishes on a set `G` of positive measure, `ρ x` is at most the probability that the chain
  started at `x` does not visit `G` during its first `n` steps, which tends to zero.

## References

* [Meyn, S.P. and Tweedie, R.L., *Markov Chains and Stochastic Stability*][meyntweedie1993]
* [G. O. Roberts, J. S. Rosenthal, *General state space Markov chains and MCMC algorithms*,
  Probability Surveys, 2004][robertsrosenthal2004]
* [L. Tierney, *Markov chains for exploring posterior distributions*, Annals of Statistics,
  1994][tierney1994]
-/

@[expose] public section

open MeasureTheory Filter Topology

open scoped ENNReal NNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {π ν : Measure α}

/-! ### Small sets of large measure -/

/-- If every point reaches a small set `C` with positive probability in `n` steps for all `n`
large enough, then there are small sets of measure arbitrarily close to full, for any finite
measure `π`. -/
lemma exists_isSmallSet_measure_compl_le [IsFiniteMeasure π] {C : Set α}
    (hC : MeasurableSet C) {k : ℕ} (hsmall : IsSmallSet κ C k ν)
    (hreach : ∀ x, ∃ N, ∀ n ≥ N, 0 < (κ ^ n) x C) {θ : ℝ≥0∞} (hθ : θ ≠ 0) :
    ∃ (B : Set α) (j : ℕ) (δ : ℝ≥0∞), MeasurableSet B ∧ π Bᶜ ≤ θ ∧ δ ≠ 0 ∧ δ ≠ ∞ ∧
      IsSmallSet κ B j (δ • ν) := by
  rcases eq_or_ne (π Set.univ) 0 with h0 | h0
  · exact ⟨∅, 0, 1, .empty, by simp [Measure.measure_univ_eq_zero.mp h0], one_ne_zero,
      ENNReal.one_ne_top, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
  have hlt : π Set.univ - θ < π Set.univ := ENNReal.sub_lt_self (measure_ne_top _ _) h0 hθ
  -- first, the points which reach `C` in `n` steps for all `n ≥ N`
  let W : ℕ → Set α := fun N ↦ ⋂ n, ⋂ (_ : N ≤ n), {x | 0 < (κ ^ n) x C}
  have hW_mono : Monotone W := fun N M hNM x hx ↦ by
    simp only [W, Set.mem_iInter] at hx ⊢
    exact fun n hn ↦ hx n (hNM.trans hn)
  have hW_univ : ⋃ N, W N = Set.univ := by
    ext x
    simpa [W] using hreach x
  obtain ⟨N, hN⟩ : ∃ N, π Set.univ - θ < π (W N) := by
    have h_tendsto := tendsto_measure_iUnion_atTop (μ := π) hW_mono
    rw [hW_univ] at h_tendsto
    exact (h_tendsto.eventually_const_lt hlt).exists
  -- then the points which reach `C` in `N` steps with probability at least `1 / (i + 1)`
  let V : ℕ → Set α := fun i ↦ {x | ((i : ℝ≥0∞) + 1)⁻¹ ≤ (κ ^ N) x C}
  have hV_meas : ∀ i, MeasurableSet (V i) :=
    fun i ↦ measurableSet_le measurable_const ((κ ^ N).measurable_coe hC)
  have hV_mono : Monotone V := fun i j hij x hx ↦
    (ENNReal.inv_le_inv.mpr (by gcongr : (i : ℝ≥0∞) + 1 ≤ j + 1)).trans hx
  have hWV : W N ⊆ ⋃ i, V i := by
    intro x hx
    have hx_pos : 0 < (κ ^ N) x C := by
      simp only [W, Set.mem_iInter] at hx
      exact hx N le_rfl
    obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt hx_pos.ne'
    exact Set.mem_iUnion.mpr ⟨i, (ENNReal.inv_le_inv.mpr le_self_add).trans hi.le⟩
  obtain ⟨i, hi⟩ : ∃ i, π Set.univ - θ < π (V i) :=
    ((tendsto_measure_iUnion_atTop (μ := π) hV_mono).eventually_const_lt
      (hN.trans_le (measure_mono hWV))).exists
  refine ⟨V i, k + N, ((i : ℝ≥0∞) + 1)⁻¹, hV_meas i, ?_, by simp, by simp, fun x hx ↦ ?_⟩
  · rw [measure_compl (hV_meas i) (measure_ne_top _ _), tsub_le_iff_left]
    exact tsub_le_iff_right.mp hi.le
  · refine le_trans ?_ (hsmall.smul_le_pow_add_apply N x)
    refine Measure.le_iff.mpr fun s _ ↦ ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    exact hx

/-! ### Convergence for initial measures dominated by the invariant measure -/

/-- Auxiliary lemma for `etvDist_pow_comp_le`. The measures `(κ ^ (j * i)) ∘ₘ a` and
`a univ • π` are the sums of a common part `g` and of remainders `a'` and `b'` whose mass
decreases geometrically with `i`, up to a small term. -/
private lemma exists_split_pow_comp [IsMarkovKernel κ] [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) {B : Set α} (hB : MeasurableSet B) {j : ℕ}
    (hsmall : IsSmallSet κ B j ν) {K : ℝ≥0∞} (hK : K ≠ ∞) {a : Measure α} (ha : a ≤ K • π)
    (i : ℕ) :
    ∃ g a' b' : Measure α, IsFiniteMeasure g ∧ (κ ^ (j * i)) ∘ₘ a = g + a'
      ∧ a Set.univ • π = g + b' ∧ a' ≤ K • π ∧ b' ≤ K • π ∧ a' Set.univ = b' Set.univ
      ∧ a' Set.univ ≤ K * π Bᶜ + (1 - ν Set.univ) ^ i * a Set.univ := by
  have ha_univ : a Set.univ ≤ K := by simpa using ha Set.univ
  have hKπ : IsFiniteMeasure (K • π) := ⟨by simp [hK.lt_top]⟩
  induction i with
  | zero =>
    refine ⟨0, a, a Set.univ • π, inferInstance, ?_, ?_, ha, ?_, ?_, ?_⟩
    · rw [Nat.mul_zero, pow_zero_comp, zero_add]
    · simp
    · refine Measure.le_iff.mpr fun s _ ↦ ?_
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr
    · simp
    · simp
  | succ i ih =>
    obtain ⟨g, a', b', hg, hag, hbg, ha', hb', hab, h_le⟩ := ih
    have ha'_fin : IsFiniteMeasure a' := isFiniteMeasure_of_le _ ha'
    have hb'_fin : IsFiniteMeasure b' := isFiniteMeasure_of_le _ hb'
    set c := a' Set.univ - K * π Bᶜ with hc
    have key : ∀ d : Measure α, d ≤ K • π → d Set.univ = a' Set.univ → c • ν ≤ (κ ^ j) ∘ₘ d := by
      intro d hd hd_univ
      have hdB : c ≤ d B := by
        rw [hc, tsub_le_iff_right, ← hd_univ, ← measure_add_measure_compl hB]
        gcongr
        simpa using hd Bᶜ
      refine le_trans ?_ (hsmall.smul_le_comp d)
      refine Measure.le_iff.mpr fun s _ ↦ ?_
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr
    have hca := key a' ha' rfl
    have hcb := key b' hb' hab.symm
    -- `c • ν` is finite since it is dominated by the finite measure `(κ ^ j) ∘ₘ a'`
    have hcν : IsFiniteMeasure (c • ν) := isFiniteMeasure_of_le _ hca
    refine ⟨(κ ^ j) ∘ₘ g + c • ν, (κ ^ j) ∘ₘ a' - c • ν, (κ ^ j) ∘ₘ b' - c • ν, inferInstance,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.mul_succ, add_comm, pow_add_comp, hag, Measure.comp_add, add_assoc,
        add_comm (c • ν), Measure.sub_add_cancel_of_le hca]
    · calc a Set.univ • π = (κ ^ j) ∘ₘ (a Set.univ • π) := (hπ.pow_comp_smul j _).symm
      _ = (κ ^ j) ∘ₘ g + c • ν + ((κ ^ j) ∘ₘ b' - c • ν) := by
        rw [hbg, Measure.comp_add, add_assoc, add_comm (c • ν),
          Measure.sub_add_cancel_of_le hcb]
    · exact Measure.sub_le.trans
        ((Measure.comp_le_comp_right ha' _).trans_eq (hπ.pow_comp_smul j K))
    · exact Measure.sub_le.trans
        ((Measure.comp_le_comp_right hb' _).trans_eq (hπ.pow_comp_smul j K))
    · rw [Measure.sub_apply .univ hca, Measure.sub_apply .univ hcb, Measure.comp_apply_univ,
        Measure.comp_apply_univ, hab]
    · rw [Measure.sub_apply .univ hca, Measure.comp_apply_univ, Measure.smul_apply, smul_eq_mul,
        tsub_le_iff_right]
      have h1 : c ≤ c * ν Set.univ + c * (1 - ν Set.univ) := by
        rw [← mul_add]
        exact le_mul_of_one_le_right' le_add_tsub
      have h2 : c ≤ (1 - ν Set.univ) ^ i * a Set.univ := by
        rw [hc, tsub_le_iff_left]
        exact h_le
      calc a' Set.univ ≤ K * π Bᶜ + c := le_add_tsub
      _ ≤ K * π Bᶜ + (c * ν Set.univ + c * (1 - ν Set.univ)) := by gcongr
      _ ≤ K * π Bᶜ
          + (c * ν Set.univ + (1 - ν Set.univ) ^ i * a Set.univ * (1 - ν Set.univ)) := by gcongr
      _ = K * π Bᶜ + (1 - ν Set.univ) ^ (i + 1) * a Set.univ + c * ν Set.univ := by
        rw [pow_succ]
        ring

/-- If `B` is a `(j, ν)`-small set and `a ≤ K • π` for an invariant probability measure `π`, then
the total variation distance between `(κ ^ (j * i)) ∘ₘ a` and `a univ • π` decreases geometrically
with `i`, up to a term proportional to `π Bᶜ`. -/
lemma etvDist_pow_comp_le [IsMarkovKernel κ] [IsProbabilityMeasure π] (hπ : κ.Invariant π)
    {B : Set α} (hB : MeasurableSet B) {j : ℕ} (hsmall : IsSmallSet κ B j ν)
    {K : ℝ≥0∞} (hK : K ≠ ∞) {a : Measure α} (ha : a ≤ K • π) (i : ℕ) :
    etvDist ((κ ^ (j * i)) ∘ₘ a) (a Set.univ • π)
      ≤ 2 * (K * π Bᶜ + (1 - ν Set.univ) ^ i * a Set.univ) := by
  obtain ⟨g, a', b', hg, hag, hbg, ha', hb', hab, h_le⟩ :=
    exists_split_pow_comp hπ hB hsmall hK ha i
  rw [hag, hbg]
  calc etvDist (g + a') (g + b') ≤ a' Set.univ + b' Set.univ :=
    (etvDist_add_left g a' b').trans_le etvDist_le_add
  _ = 2 * a' Set.univ := by rw [← hab, two_mul]
  _ ≤ 2 * (K * π Bᶜ + (1 - ν Set.univ) ^ i * a Set.univ) := by gcongr

/-- The total variation distance to a multiple of an invariant measure is nonincreasing along
the iterates of a Markov kernel. -/
lemma antitone_etvDist_pow_comp [IsMarkovKernel κ] (hπ : κ.Invariant π) (a : Measure α)
    (c : ℝ≥0∞) :
    Antitone fun n : ℕ ↦ etvDist ((κ ^ n) ∘ₘ a) (c • π) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  calc etvDist ((κ ^ (n + 1)) ∘ₘ a) (c • π)
  _ = etvDist (κ ∘ₘ ((κ ^ n) ∘ₘ a)) (κ ∘ₘ (c • π)) := by
    rw [pow_succ_comp', Measure.comp_smul, hπ.def]
  _ ≤ etvDist ((κ ^ n) ∘ₘ a) (c • π) := etvDist_comp_le κ _ _

/-- If a measure `a` is dominated by a multiple of the invariant probability measure `π` of a
Markov kernel `κ`, and every point reaches a small set `C` with positive probability in `n` steps
for all `n` large enough, then `(κ ^ n) ∘ₘ a` tends to `a univ • π` in total variation. -/
theorem tendsto_etvDist_pow_comp_of_le [IsMarkovKernel κ] [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) {C : Set α} (hC : MeasurableSet C) {k : ℕ}
    (hν : ν ≠ 0) (hsmall : IsSmallSet κ C k ν) (hreach : ∀ x, ∃ N, ∀ n ≥ N, 0 < (κ ^ n) x C)
    {K : ℝ≥0∞} (hK : K ≠ ∞) {a : Measure α} (ha : a ≤ K • π) :
    Tendsto (fun n : ℕ ↦ etvDist ((κ ^ n) ∘ₘ a) (a Set.univ • π)) atTop (𝓝 0) := by
  have ha_univ : a Set.univ ≤ K := by simpa using ha Set.univ
  have h_event : ∀ θ : ℝ≥0∞, θ ≠ 0 →
      ∀ᶠ n : ℕ in atTop, etvDist ((κ ^ n) ∘ₘ a) (a Set.univ • π) ≤ 2 * (K * θ + θ) := by
    intro θ hθ
    obtain ⟨B, j, δ, hB, hBθ, hδ0, hδ_top, hB_small⟩ :=
      exists_isSmallSet_measure_compl_le (π := π) hC hsmall hreach hθ
    have hδν : (δ • ν) Set.univ ≠ 0 := by simp [hδ0, hν]
    have hq : 1 - (δ • ν) Set.univ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδν
    have h_tendsto : Tendsto (fun i : ℕ ↦ (1 - (δ • ν) Set.univ) ^ i * a Set.univ) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.mul_const (b := a Set.univ)
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) (Or.inr (ne_top_of_le_ne_top hK ha_univ))
      simpa using h
    obtain ⟨i, hi⟩ := (h_tendsto.eventually_lt_const (pos_iff_ne_zero.mpr hθ)).exists
    refine eventually_atTop.mpr ⟨j * i, fun n hn ↦ ?_⟩
    calc etvDist ((κ ^ n) ∘ₘ a) (a Set.univ • π)
    _ ≤ etvDist ((κ ^ (j * i)) ∘ₘ a) (a Set.univ • π) := antitone_etvDist_pow_comp hπ a _ hn
    _ ≤ 2 * (K * π Bᶜ + (1 - (δ • ν) Set.univ) ^ i * a Set.univ) :=
      etvDist_pow_comp_le hπ hB hB_small hK ha i
    _ ≤ 2 * (K * θ + θ) := by gcongr
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hε_top
  · simp
  have h2K : 2 * (K + 1) ≠ 0 := by simp
  have h2K' : 2 * (K + 1) ≠ ∞ := ENNReal.mul_ne_top (by simp) (by simp [hK])
  refine (h_event (ε / (2 * (K + 1))) (ENNReal.div_pos hε.ne' h2K').ne').mono
    fun n hn ↦ hn.trans_eq ?_
  rw [← add_one_mul, ← mul_assoc, ENNReal.mul_div_cancel h2K h2K']

/-- If a probability measure `μ` is the sum of a measure `ζ` dominated by a multiple of the
invariant probability measure `π` and of a measure `ξ`, then the total variation distance between
`(κ ^ n) ∘ₘ μ` and `π` is eventually at most `2 * ξ univ + ε`. -/
lemma eventually_etvDist_pow_comp_le [IsMarkovKernel κ] [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) {C : Set α} (hC : MeasurableSet C) {k : ℕ}
    (hν : ν ≠ 0) (hsmall : IsSmallSet κ C k ν) (hreach : ∀ x, ∃ N, ∀ n ≥ N, 0 < (κ ^ n) x C)
    {μ ζ ξ : Measure α} [IsProbabilityMeasure μ] (hμ : μ = ζ + ξ) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hζ : ζ ≤ K • π) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∀ᶠ n : ℕ in atTop, etvDist ((κ ^ n) ∘ₘ μ) π ≤ 2 * ξ Set.univ + ε := by
  have hζμ : ζ ≤ μ := hμ ▸ Measure.le_add_right le_rfl
  have hζ_fin : IsFiniteMeasure ζ := isFiniteMeasure_of_le μ hζμ
  have h_univ : ζ Set.univ + ξ Set.univ = 1 := by rw [← Measure.add_apply, ← hμ, measure_univ]
  have hζ_smul : ζ Set.univ • π ≤ π := by
    refine Measure.le_iff.mpr fun s _ ↦ ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_of_le_one_left' (h_univ ▸ le_self_add)
  have hζ_smul_fin : IsFiniteMeasure (ζ Set.univ • π) := isFiniteMeasure_of_le π hζ_smul
  have h_tendsto := tendsto_etvDist_pow_comp_of_le hπ hC hν hsmall hreach hK hζ
  filter_upwards [ENNReal.tendsto_nhds_zero.mp h_tendsto ε (pos_iff_ne_zero.mpr hε)] with n hn
  set η : Kernel α α := κ ^ n
  have h1 : etvDist (η ∘ₘ μ) (η ∘ₘ ζ) = ξ Set.univ := by
    rw [hμ, Measure.comp_add, etvDist_of_ge (Measure.le_add_right le_rfl), Measure.add_apply,
      Measure.comp_apply_univ, Measure.comp_apply_univ,
      ENNReal.add_sub_cancel_left (measure_ne_top _ _)]
  have h2 : etvDist (ζ Set.univ • π) π ≤ ξ Set.univ := by
    rw [etvDist_of_le hζ_smul, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
      tsub_le_iff_left, h_univ]
  calc etvDist (η ∘ₘ μ) π
  _ ≤ etvDist (η ∘ₘ μ) (η ∘ₘ ζ) + etvDist (η ∘ₘ ζ) π := etvDist_triangle _ _ _
  _ ≤ etvDist (η ∘ₘ μ) (η ∘ₘ ζ)
      + (etvDist (η ∘ₘ ζ) (ζ Set.univ • π) + etvDist (ζ Set.univ • π) π) := by
    gcongr
    exact etvDist_triangle _ _ _
  _ ≤ ξ Set.univ + (ε + ξ Set.univ) := by
    rw [h1]
    gcongr
  _ = 2 * ξ Set.univ + ε := by ring

/-! ### The part of `κ ^ i` which is not dominated by the invariant measure -/

section Excess

variable [MeasurableSpace.CountablyGenerated α]

open Classical in
/-- `excess κ π i x` is the part of the measure `(κ ^ i) x` which exceeds `i • π`. -/
private noncomputable def excess (κ : Kernel α α) (π : Measure α) (i : ℕ) : Kernel α α :=
  κ ^ i - Kernel.const α ((i : ℝ≥0) • π)

/-- The infimum over `i` of the mass of the part of `(κ ^ i) x` which exceeds `i • π`. -/
private noncomputable def excessMass (κ : Kernel α α) (π : Measure α) (x : α) : ℝ≥0∞ :=
  ⨅ i, excess κ π i x Set.univ

variable [IsMarkovKernel κ] [IsFiniteMeasure π]

private lemma excess_apply (i : ℕ) (x : α) :
    excess κ π i x = (κ ^ i) x - (i : ℝ≥0) • π := by
  classical
  rw [excess, Kernel.sub_apply, const_apply]

private lemma excess_apply_le (i : ℕ) (x : α) : excess κ π i x ≤ (κ ^ i) x := by
  rw [excess_apply]
  exact Measure.sub_le

private lemma pow_apply_le_excess_add (i : ℕ) (x : α) :
    (κ ^ i) x ≤ excess κ π i x + (i : ℝ≥0) • π := by
  rw [excess_apply]
  exact Measure.sub_le_iff_le_add.mp le_rfl

private lemma excess_apply_univ_le_of_le {i : ℕ} {x : α} {d : Measure α}
    (h : (κ ^ i) x ≤ d + (i : ℝ≥0) • π) :
    excess κ π i x Set.univ ≤ d Set.univ := by
  rw [excess_apply]
  exact Measure.sub_le_of_le_add h Set.univ

private lemma excess_apply_univ_le_one (i : ℕ) (x : α) : excess κ π i x Set.univ ≤ 1 :=
  (excess_apply_le i x Set.univ).trans prob_le_one

private lemma pow_comp_le_excess_comp_add (i : ℕ) (μ : Measure α) :
    (κ ^ i) ∘ₘ μ ≤ (excess κ π i) ∘ₘ μ + μ Set.univ • ((i : ℝ≥0) • π) := by
  calc (κ ^ i) ∘ₘ μ
  _ ≤ (excess κ π i + Kernel.const α ((i : ℝ≥0) • π)) ∘ₘ μ :=
    Measure.comp_le_comp_left μ fun x ↦ by
      rw [FunLike.coe_add, Pi.add_apply, const_apply]
      exact pow_apply_le_excess_add i x
  _ = (excess κ π i) ∘ₘ μ + μ Set.univ • ((i : ℝ≥0) • π) := by
    rw [Measure.add_comp, Measure.const_comp]

private lemma excess_add_apply_univ_le (hπ : κ.Invariant π) (m i : ℕ) (x : α) :
    excess κ π (m + i) x Set.univ ≤ ∫⁻ y, excess κ π m y Set.univ ∂(excess κ π i x) := by
  rw [← Measure.bind_apply .univ (excess κ π m).aemeasurable]
  refine excess_apply_univ_le_of_le ?_
  set η : Kernel α α := κ ^ m
  have h_inv : η ∘ₘ ((i : ℝ≥0) • π) = (i : ℝ≥0) • π := hπ.pow_comp_smul m (i : ℝ≥0)
  have h_le_one : excess κ π i x Set.univ • ((m : ℝ≥0) • π) ≤ (m : ℝ≥0) • π := by
    refine Measure.le_iff.mpr fun s _ ↦ ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_le_of_le_one_left' (excess_apply_univ_le_one i x)
  calc (κ ^ (m + i)) x = η ∘ₘ (κ ^ i) x := pow_add_apply κ m i x
  _ ≤ η ∘ₘ (excess κ π i x + (i : ℝ≥0) • π) :=
    Measure.comp_le_comp_right (pow_apply_le_excess_add i x) _
  _ = η ∘ₘ (excess κ π i x) + (i : ℝ≥0) • π := by rw [Measure.comp_add, h_inv]
  _ ≤ (excess κ π m) ∘ₘ (excess κ π i x) + excess κ π i x Set.univ • ((m : ℝ≥0) • π)
      + (i : ℝ≥0) • π := by
    gcongr
    exact pow_comp_le_excess_comp_add m _
  _ ≤ (excess κ π m) ∘ₘ (excess κ π i x) + (m : ℝ≥0) • π + (i : ℝ≥0) • π := by gcongr
  _ = (excess κ π m) ∘ₘ (excess κ π i x) + ((m + i : ℕ) : ℝ≥0) • π := by
    rw [add_assoc, ← add_smul, Nat.cast_add]

private lemma antitone_excess_apply_univ (hπ : κ.Invariant π) (x : α) :
    Antitone fun i ↦ excess κ π i x Set.univ := by
  refine antitone_nat_of_succ_le fun i ↦ ?_
  calc excess κ π (i + 1) x Set.univ = excess κ π (1 + i) x Set.univ := by rw [add_comm]
  _ ≤ ∫⁻ y, excess κ π 1 y Set.univ ∂(excess κ π i x) := excess_add_apply_univ_le hπ 1 i x
  _ ≤ ∫⁻ _, 1 ∂(excess κ π i x) := lintegral_mono fun y ↦ excess_apply_univ_le_one 1 y
  _ = excess κ π i x Set.univ := by simp

private lemma excess_succ_apply_univ_le (hπ : κ.Invariant π) (i : ℕ) (x : α) :
    excess κ π (i + 1) x Set.univ ≤ ∫⁻ y, excess κ π i y Set.univ ∂κ x := by
  calc excess κ π (i + 1) x Set.univ
  _ ≤ ∫⁻ y, excess κ π i y Set.univ ∂(excess κ π 1 x) := excess_add_apply_univ_le hπ i 1 x
  _ ≤ ∫⁻ y, excess κ π i y Set.univ ∂κ x :=
    lintegral_mono' (by simpa using excess_apply_le (κ := κ) (π := π) 1 x) le_rfl

omit [IsMarkovKernel κ] [IsFiniteMeasure π] in
private lemma measurable_excessMass : Measurable (excessMass κ π) :=
  Measurable.iInf fun i ↦ (excess κ π i).measurable_coe .univ

private lemma excessMass_le_one (x : α) : excessMass κ π x ≤ 1 :=
  (iInf_le _ 0).trans (excess_apply_univ_le_one 0 x)

private lemma lintegral_excessMass (hπ : κ.Invariant π) (μ : Measure α) [IsFiniteMeasure μ] :
    ∫⁻ y, excessMass κ π y ∂μ = ⨅ i, ∫⁻ y, excess κ π i y Set.univ ∂μ := by
  refine lintegral_iInf (fun i ↦ (excess κ π i).measurable_coe .univ)
    (fun i j hij y ↦ antitone_excess_apply_univ hπ y hij) ?_
  refine ((lintegral_mono fun y ↦ excess_apply_univ_le_one 0 y).trans_lt ?_).ne
  simp

private lemma excessMass_le_lintegral (hπ : κ.Invariant π) (x : α) :
    excessMass κ π x ≤ ∫⁻ y, excessMass κ π y ∂κ x := by
  rw [lintegral_excessMass hπ]
  exact le_iInf fun i ↦ (iInf_le _ (i + 1)).trans (excess_succ_apply_univ_le hπ i x)

private lemma excessMass_lt_one (hπ : κ.Invariant π) {c : ℝ≥0} (hνc : ν ≤ c • π) (hν : ν ≠ 0)
    {w : ℝ≥0∞} (hw : w ≠ 0) (hw1 : w ≤ 1) {n : ℕ} {x : α} (h : w • ν ≤ (κ ^ n) x) :
    excessMass κ π x < 1 := by
  have hwν_fin : IsFiniteMeasure (w • ν) := isFiniteMeasure_of_le _ h
  have hwν : w • ν ≤ ν := by
    refine Measure.le_iff.mpr fun s _ ↦ ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_le_of_le_one_left' hw1
  set p := ⌈c⌉₊
  set η : Kernel α α := κ ^ p
  have hcp : c • π ≤ ((p + n : ℕ) : ℝ≥0) • π := by
    refine Measure.le_iff.mpr fun s _ ↦ ?_
    rw [Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
    gcongr
    exact (Nat.le_ceil c).trans (by exact_mod_cast Nat.le_add_right ⌈c⌉₊ n)
  have h_inv : η ∘ₘ (c • π) = c • π := hπ.pow_comp_smul p c
  have h_le : (κ ^ (p + n)) x ≤ η ∘ₘ ((κ ^ n) x - w • ν) + ((p + n : ℕ) : ℝ≥0) • π := by
    calc (κ ^ (p + n)) x = η ∘ₘ (κ ^ n) x := pow_add_apply κ p n x
    _ = η ∘ₘ ((κ ^ n) x - w • ν) + η ∘ₘ (w • ν) := by
      rw [← Measure.comp_add, Measure.sub_add_cancel_of_le h]
    _ ≤ η ∘ₘ ((κ ^ n) x - w • ν) + η ∘ₘ (c • π) := by
      gcongr
      exact hwν.trans hνc
    _ = η ∘ₘ ((κ ^ n) x - w • ν) + c • π := by rw [h_inv]
    _ ≤ η ∘ₘ ((κ ^ n) x - w • ν) + ((p + n : ℕ) : ℝ≥0) • π := by gcongr
  calc excessMass κ π x ≤ excess κ π (p + n) x Set.univ := iInf_le _ _
  _ ≤ (η ∘ₘ ((κ ^ n) x - w • ν)) Set.univ := excess_apply_univ_le_of_le h_le
  _ = 1 - w * ν Set.univ := by
    rw [Measure.comp_apply_univ, Measure.sub_apply .univ h, measure_univ, Measure.smul_apply,
      smul_eq_mul]
  _ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (mul_ne_zero hw (by simpa using hν))

private lemma ae_excessMass_eq_zero [IsProbabilityMeasure π] {φ : Measure α} [IsIrreducible φ κ]
    (hφ : φ ≠ 0) (hπ : κ.Invariant π) (h_lt : ∀ x, excessMass κ π x < 1) :
    ∀ᵐ x ∂π, excessMass κ π x = 0 := by
  -- there is a level `t < 1` such that the set `{x | excessMass κ π x ≤ t}` is not null
  obtain ⟨t, ht1, ht⟩ : ∃ t : ℝ≥0∞, t < 1 ∧ π {x | excessMass κ π x ≤ t} ≠ 0 := by
    by_contra! h
    have h_univ : (Set.univ : Set α) = ⋃ q : {q : ℚ // ((q : ℝ).toNNReal : ℝ≥0∞) < 1},
        {x | excessMass κ π x ≤ ((q : ℝ).toNNReal : ℝ≥0∞)} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp (h_lt x)
      exact ⟨⟨q, hq2⟩, hq1.le⟩
    have h_zero : π Set.univ = 0 := by
      rw [h_univ]
      exact measure_iUnion_null fun q ↦ h _ q.2
    simp at h_zero
  -- hence the excess mass is at most `t` almost everywhere, since it is subharmonic
  have h_ae : ∀ᵐ x ∂π, excessMass κ π x ≤ t := by
    refine hπ.ae_le_of_le_lintegral hφ measurable_excessMass ?_
      (ae_of_all _ (excessMass_le_lintegral hπ)) ht
    refine ((lintegral_mono fun y ↦ excessMass_le_one y).trans_lt ?_).ne
    simp
  filter_upwards [hπ.ae_ae_pow h_ae] with x hx
  have h1 : ∀ i, excessMass κ π x ≤ t * excess κ π i x Set.univ := by
    intro i
    have h_fin : IsFiniteMeasure (excess κ π i x) := isFiniteMeasure_of_le _ (excess_apply_le i x)
    calc excessMass κ π x
    _ ≤ ⨅ m, ∫⁻ y, excess κ π m y Set.univ ∂(excess κ π i x) :=
      le_iInf fun m ↦ (iInf_le _ (m + i)).trans (excess_add_apply_univ_le hπ m i x)
    _ = ∫⁻ y, excessMass κ π y ∂(excess κ π i x) := (lintegral_excessMass hπ _).symm
    _ ≤ ∫⁻ _, t ∂(excess κ π i x) :=
      lintegral_mono_ae ((hx i).filter_mono (ae_mono (excess_apply_le i x)))
    _ = t * excess κ π i x Set.univ := MeasureTheory.lintegral_const _
  have h2 : excessMass κ π x ≤ t * excessMass κ π x := by
    rcases eq_or_ne t 0 with rfl | ht0
    · simpa using h1 0
    · have h_eq : t * excessMass κ π x = ⨅ i, t * excess κ π i x Set.univ :=
        ENNReal.mul_iInf_of_ne ht0 (ht1.trans_le le_top).ne
      rw [h_eq]
      exact le_iInf h1
  by_contra h0
  have h_fin : excessMass κ π x ≠ ∞ := ((excessMass_le_one x).trans_lt ENNReal.one_lt_top).ne
  have h3 : t * excessMass κ π x < 1 * excessMass κ π x := ENNReal.mul_lt_mul_left h0 h_fin ht1
  rw [one_mul] at h3
  exact not_le.mpr h3 h2

private lemma tendsto_etvDist_pow_comp_of_lintegral_excessMass_eq_zero [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) {C : Set α} (hC : MeasurableSet C) {k : ℕ}
    (hν : ν ≠ 0) (hsmall : IsSmallSet κ C k ν) (hreach : ∀ x, ∃ N, ∀ n ≥ N, 0 < (κ ^ n) x C)
    {μ : Measure α} [IsProbabilityMeasure μ] (hμ : ∫⁻ x, excessMass κ π x ∂μ = 0) :
    Tendsto (fun n : ℕ ↦ etvDist ((κ ^ n) ∘ₘ μ) π) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  have hε4 : 0 < ε / 2 / 2 := ENNReal.half_pos hε2
  obtain ⟨i, hi⟩ : ∃ i, ∫⁻ x, excess κ π i x Set.univ ∂μ < ε / 2 / 2 := by
    by_contra! h
    have h_le : ε / 2 / 2 ≤ ∫⁻ x, excessMass κ π x ∂μ := by
      rw [lintegral_excessMass hπ]
      exact le_iInf h
    rw [hμ] at h_le
    exact (hε4.trans_le h_le).false
  -- we split `(κ ^ i) ∘ₘ μ` into a part `ξ` of small mass and a part dominated by `i • π`
  set θ : Kernel α α := κ ^ i with hθ
  set ξ := (excess κ π i) ∘ₘ μ
  have hξ_univ : ξ Set.univ = ∫⁻ x, excess κ π i x Set.univ ∂μ :=
    Measure.bind_apply .univ (excess κ π i).aemeasurable
  have hξ_le : ξ ≤ θ ∘ₘ μ := Measure.comp_le_comp_left μ (excess_apply_le i)
  have hξ_fin : IsFiniteMeasure ξ := isFiniteMeasure_of_le _ hξ_le
  have hμ' : θ ∘ₘ μ = (θ ∘ₘ μ - ξ) + ξ := (Measure.sub_add_cancel_of_le hξ_le).symm
  have hζ : θ ∘ₘ μ - ξ ≤ ((i : ℝ≥0) : ℝ≥0∞) • π := by
    refine Measure.sub_le_of_le_add ?_
    have h := pow_comp_le_excess_comp_add (κ := κ) (π := π) i μ
    rwa [measure_univ, one_smul, add_comm] at h
  have h_event :=
    eventually_etvDist_pow_comp_le hπ hC hν hsmall hreach hμ' ENNReal.coe_ne_top hζ hε2
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_event
  refine eventually_atTop.mpr ⟨N + i, fun n hn ↦ ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + i := ⟨n - i, (Nat.sub_add_cancel (by omega)).symm⟩
  have hN' := hN n' (by omega)
  rw [hθ, ← pow_add_comp] at hN'
  calc etvDist ((κ ^ (n' + i)) ∘ₘ μ) π ≤ 2 * ξ Set.univ + ε / 2 := hN'
  _ ≤ 2 * (ε / 2 / 2) + ε / 2 := by
    rw [hξ_univ]
    gcongr
  _ = ε := by rw [two_mul, ENNReal.add_halves, ENNReal.add_halves]

private lemma excessMass_eq_zero_of_isHarrisRecurrent {φ : Measure α} (hφ : φ ≠ 0) (hφπ : φ ≪ π)
    (hπ : κ.Invariant π) (hH : κ.IsHarrisRecurrent φ) (h_ae : ∀ᵐ x ∂π, excessMass κ π x = 0)
    (x : α) :
    excessMass κ π x = 0 := by
  -- `G` is the set on which the excess mass vanishes. It has positive `φ`-measure.
  have hG : MeasurableSet {x | excessMass κ π x = 0} :=
    measurable_excessMass (measurableSet_singleton 0)
  set G : Set α := {x | excessMass κ π x = 0}
  have hφG : 0 < φ G := by
    rw [pos_iff_ne_zero]
    intro h0
    refine hφ ?_
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self G]
    refine measure_union_null h0 (hφπ (measure_eq_zero_iff_ae_notMem.mpr ?_))
    filter_upwards [h_ae] with y hy using fun h ↦ h hy
  -- the excess mass at `y` is at most its integral against one step of the chain killed in `G`
  have h_step : ∀ y, excessMass κ π y ≤ ∫⁻ z, excessMass κ π z ∂(κ.restrict hG.compl y) := by
    intro y
    calc excessMass κ π y ≤ ∫⁻ z, excessMass κ π z ∂κ y := excessMass_le_lintegral hπ y
    _ = ∫⁻ z in G, excessMass κ π z ∂κ y + ∫⁻ z in Gᶜ, excessMass κ π z ∂κ y :=
      (lintegral_add_compl _ hG).symm
    _ = ∫⁻ z, excessMass κ π z ∂(κ.restrict hG.compl y) := by
      rw [setLIntegral_congr_fun hG (fun z hz ↦ hz), lintegral_zero, zero_add, restrict_apply]
  -- hence it is at most the probability that the chain avoids `G` for `n` steps
  have h_pow : ∀ n : ℕ, ∀ y,
      excessMass κ π y ≤ ∫⁻ z, excessMass κ π z ∂((κ.restrict hG.compl) ^ n) y := by
    intro n
    induction n with
    | zero =>
      intro y
      rw [pow_zero_apply, lintegral_dirac' _ measurable_excessMass]
    | succ n ih =>
      intro y
      calc excessMass κ π y ≤ ∫⁻ z, excessMass κ π z ∂((κ.restrict hG.compl) ^ n) y := ih y
      _ ≤ ∫⁻ z, ∫⁻ z', excessMass κ π z' ∂(κ.restrict hG.compl z)
          ∂((κ.restrict hG.compl) ^ n) y := lintegral_mono h_step
      _ = ∫⁻ z, excessMass κ π z ∂((κ.restrict hG.compl) ^ (n + 1)) y := by
        rw [pow_succ_apply', Measure.lintegral_bind (Kernel.aemeasurable _)
          measurable_excessMass.aemeasurable]
  refine le_antisymm (ge_of_tendsto' (hH hG hφG x) fun n ↦ ?_) bot_le
  calc excessMass κ π x ≤ ∫⁻ z, excessMass κ π z ∂((κ.restrict hG.compl) ^ n) x := h_pow n x
  _ ≤ ∫⁻ _, 1 ∂((κ.restrict hG.compl) ^ n) x := lintegral_mono fun z ↦ excessMass_le_one z
  _ = ((κ.restrict hG.compl) ^ n) x Set.univ := by simp

end Excess

/-! ### Main results -/

private lemma tendsto_tvDist_of_tendsto_etvDist {ι : Type*} {l : Filter ι}
    {μ ν : ι → Measure α} (h : Tendsto (fun i ↦ etvDist (μ i) (ν i)) l (𝓝 0)) :
    Tendsto (fun i ↦ tvDist (μ i) (ν i)) l (𝓝 0) := by
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at h'
  exact h'

section SmallSet

variable [MeasurableSpace.CountablyGenerated α] [IsMarkovKernel κ] [IsFiniteMeasure π] [NeZero π]
  {φ : Measure α} [hφ : NeZero φ] [hκφ : IsIrreducible φ κ]

include hφ hκφ

/-- An irreducible aperiodic Markov kernel `κ` on a countably generated measurable space, with a
nonzero finite invariant measure `π`, has a small set `C` which is reached with positive
probability from every point in `n` steps, for all `n` large enough. The measure `ν` of the small
set can be chosen to be dominated by a multiple of `π`. -/
lemma exists_isSmallSet_forall_pow_apply_pos (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π) :
    ∃ (C : Set α) (k : ℕ) (ν : Measure α) (c : ℝ≥0), MeasurableSet C ∧ ν ≠ 0 ∧ ν ≤ c • π ∧
      IsSmallSet κ C k ν ∧ ∀ x, ∃ N, ∀ n ≥ N, 0 < (κ ^ n) x C := by
  -- we can assume that the irreducibility measure is finite and dominated by `π`
  obtain ⟨φ', hφ'π, hφ'0, hφ'⟩ := IsIrreducible.exists_measure_le (κ := κ) (NeZero.ne φ)
    (IsIrreducible.absolutelyContinuous hπ (NeZero.ne π))
  have hφ'_fin : IsFiniteMeasure φ' := isFiniteMeasure_of_le π hφ'π
  -- there is a small set `C`
  obtain ⟨C, D, k, c, hC, hD, -, hφC, hφD, hk, hc, hsmall⟩ := exists_isSmallSet (κ := κ) (φ := φ')
    MeasurableSet.univ (by simpa [pos_iff_ne_zero] using hφ'0)
  have hν0 : c • φ'.restrict D ≠ 0 := by
    rw [← Measure.measure_univ_ne_zero, Measure.coe_nnreal_smul_apply,
      Measure.restrict_apply_univ]
    exact mul_ne_zero (by simpa using hc.ne') hφD.ne'
  have hνπ : c • φ'.restrict D ≤ c • π := by
    refine Measure.le_iff.mpr fun s _ ↦ ?_
    rw [Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
    gcongr
    exact Measure.restrict_le_self.trans hφ'π
  -- by aperiodicity, every point reaches `C` at all large times
  exact ⟨C, k, c • φ'.restrict D, c, hC, hν0, hνπ, hsmall, fun x ↦
    hκ.exists_forall_pow_apply_pos (φ := φ') hC hφC hk hν0
      (Measure.absolutelyContinuous_of_le_smul hνπ) hsmall x⟩

end SmallSet

section Main

variable [MeasurableSpace.CountablyGenerated α] [IsMarkovKernel κ] [IsProbabilityMeasure π]
  {φ : Measure α} [hφ : NeZero φ] [hκφ : IsIrreducible φ κ] {μ : Measure α}

include hφ hκφ

private lemma ae_excessMass_eq_zero_of_isAperiodic (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π) :
    ∀ᵐ x ∂π, excessMass κ π x = 0 := by
  obtain ⟨C, k, ν, c, -, hν0, hνπ, hsmall, hreach⟩ :=
    exists_isSmallSet_forall_pow_apply_pos (φ := φ) hπ hκ
  refine ae_excessMass_eq_zero (NeZero.ne φ) hπ fun x ↦ ?_
  obtain ⟨N, hN⟩ := hreach x
  exact excessMass_lt_one hπ hνπ hν0 (hN N le_rfl).ne' prob_le_one
    (hsmall.smul_le_pow_add_apply N x)

private lemma tendsto_etvDist_pow_comp_of_isAperiodic (hπ : κ.Invariant π)
    (hκ : κ.IsAperiodic π) [IsProbabilityMeasure μ] (hμ : ∫⁻ x, excessMass κ π x ∂μ = 0) :
    Tendsto (fun n : ℕ ↦ etvDist ((κ ^ n) ∘ₘ μ) π) atTop (𝓝 0) := by
  obtain ⟨C, k, ν, c, hC, hν0, hνπ, hsmall, hreach⟩ :=
    exists_isSmallSet_forall_pow_apply_pos (φ := φ) hπ hκ
  exact tendsto_etvDist_pow_comp_of_lintegral_excessMass_eq_zero hπ hC hν0 hsmall hreach hμ

private lemma tendsto_etvDist_pow_apply_of_isAperiodic (hπ : κ.Invariant π)
    (hκ : κ.IsAperiodic π) {x : α} (hx : excessMass κ π x = 0) :
    Tendsto (fun n : ℕ ↦ etvDist ((κ ^ n) x) π) atTop (𝓝 0) := by
  have h := tendsto_etvDist_pow_comp_of_isAperiodic (φ := φ) (μ := Measure.dirac x) hπ hκ
    (by rw [lintegral_dirac' _ measurable_excessMass, hx])
  simpa only [Measure.dirac_bind (Kernel.measurable _)] using h

/-- **Ergodic theorem for Markov kernels**. Let `κ` be a Markov kernel on a countably generated
measurable space, with an invariant probability measure `π`. If `κ` is irreducible with respect
to a nonzero measure `φ` and aperiodic, then for `π`-almost every `x`, the measures `(κ ^ n) x`
converge to `π` in total variation.
Ref. *Roberts-Rosenthal* Theorem 4, *Tierney* Theorem 1. -/
theorem ae_tendsto_etvDist_pow_apply (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π) :
    ∀ᵐ x ∂π, Tendsto (fun n : ℕ ↦ etvDist ((κ ^ n) x) π) atTop (𝓝 0) := by
  filter_upwards [ae_excessMass_eq_zero_of_isAperiodic (φ := φ) hπ hκ] with x hx
  exact tendsto_etvDist_pow_apply_of_isAperiodic (φ := φ) hπ hκ hx

/-- **Ergodic theorem for Markov kernels**. Let `κ` be a Markov kernel on a countably generated
measurable space, with an invariant probability measure `π`. If `κ` is irreducible with respect
to a nonzero measure `φ` and aperiodic, then for `π`-almost every `x`, the measures `(κ ^ n) x`
converge to `π` in total variation.
Ref. *Roberts-Rosenthal* Theorem 4, *Tierney* Theorem 1. -/
theorem ae_tendsto_tvDist_pow_apply (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π) :
    ∀ᵐ x ∂π, Tendsto (fun n : ℕ ↦ tvDist ((κ ^ n) x) π) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_etvDist_pow_apply (φ := φ) hπ hκ] with x hx
  exact tendsto_tvDist_of_tendsto_etvDist hx

/-- Let `κ` be an irreducible aperiodic Markov kernel on a countably generated measurable space,
with an invariant probability measure `π`. For every initial probability measure `μ` which is
absolutely continuous with respect to `π`, the measures `(κ ^ n) ∘ₘ μ` converge to `π` in total
variation. -/
theorem tendsto_etvDist_pow_comp (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π)
    [IsProbabilityMeasure μ] (hμ : μ ≪ π) :
    Tendsto (fun n : ℕ ↦ etvDist ((κ ^ n) ∘ₘ μ) π) atTop (𝓝 0) := by
  refine tendsto_etvDist_pow_comp_of_isAperiodic (φ := φ) hπ hκ ?_
  rw [lintegral_eq_zero_iff measurable_excessMass]
  exact hμ.ae_le (ae_excessMass_eq_zero_of_isAperiodic (φ := φ) hπ hκ)

/-- Let `κ` be an irreducible aperiodic Markov kernel on a countably generated measurable space,
with an invariant probability measure `π`. For every initial probability measure `μ` which is
absolutely continuous with respect to `π`, the measures `(κ ^ n) ∘ₘ μ` converge to `π` in total
variation. -/
theorem tendsto_tvDist_pow_comp (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π)
    [IsProbabilityMeasure μ] (hμ : μ ≪ π) :
    Tendsto (fun n : ℕ ↦ tvDist ((κ ^ n) ∘ₘ μ) π) atTop (𝓝 0) :=
  tendsto_tvDist_of_tendsto_etvDist (tendsto_etvDist_pow_comp (φ := φ) hπ hκ hμ)

end Main

section Harris

variable [MeasurableSpace.CountablyGenerated α] [IsMarkovKernel κ] [IsProbabilityMeasure π]
  {φ : Measure α} [hφ : NeZero φ]

include hφ

/-- **Ergodic theorem for Harris recurrent Markov kernels**. Let `κ` be a Markov kernel on a
countably generated measurable space, with an invariant probability measure `π`. If `κ` is Harris
recurrent with respect to a nonzero measure `φ` and aperiodic, then for
every initial probability measure `μ`, the measures `(κ ^ n) ∘ₘ μ` converge to `π` in total
variation.
Ref. *Meyn-Tweedie* Theorem 13.0.1, *Tierney* Theorem 1. -/
theorem IsHarrisRecurrent.tendsto_etvDist_pow_comp (hH : κ.IsHarrisRecurrent φ)
    (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π) (μ : Measure α) [IsProbabilityMeasure μ] :
    Tendsto (fun n : ℕ ↦ etvDist ((κ ^ n) ∘ₘ μ) π) atTop (𝓝 0) := by
  have hκφ : IsIrreducible φ κ := hH.isIrreducible
  refine tendsto_etvDist_pow_comp_of_isAperiodic (φ := φ) hπ hκ ?_
  have h_zero : ∀ x, excessMass κ π x = 0 :=
    excessMass_eq_zero_of_isHarrisRecurrent (NeZero.ne φ)
      (IsIrreducible.absolutelyContinuous hπ (NeZero.ne π)) hπ hH
      (ae_excessMass_eq_zero_of_isAperiodic (φ := φ) hπ hκ)
  simp [h_zero]

/-- **Ergodic theorem for Harris recurrent Markov kernels**. Let `κ` be a Markov kernel on a
countably generated measurable space, with an invariant probability measure `π`. If `κ` is Harris
recurrent with respect to a nonzero measure `φ` and aperiodic, then for
every initial probability measure `μ`, the measures `(κ ^ n) ∘ₘ μ` converge to `π` in total
variation.
Ref. *Meyn-Tweedie* Theorem 13.0.1, *Tierney* Theorem 1. -/
theorem IsHarrisRecurrent.tendsto_tvDist_pow_comp (hH : κ.IsHarrisRecurrent φ)
    (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π) (μ : Measure α) [IsProbabilityMeasure μ] :
    Tendsto (fun n : ℕ ↦ tvDist ((κ ^ n) ∘ₘ μ) π) atTop (𝓝 0) :=
  tendsto_tvDist_of_tendsto_etvDist (hH.tendsto_etvDist_pow_comp hπ hκ μ)

/-- **Ergodic theorem for Harris recurrent Markov kernels**. Let `κ` be a Markov kernel on a
countably generated measurable space, with an invariant probability measure `π`. If `κ` is Harris
recurrent with respect to a nonzero measure `φ` and aperiodic, then for
every `x`, the measures `(κ ^ n) x` converge to `π` in total variation.
Ref. *Meyn-Tweedie* Theorem 13.0.1, *Tierney* Theorem 1. -/
theorem IsHarrisRecurrent.tendsto_etvDist_pow_apply (hH : κ.IsHarrisRecurrent φ)
    (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π) (x : α) :
    Tendsto (fun n : ℕ ↦ etvDist ((κ ^ n) x) π) atTop (𝓝 0) := by
  have h := hH.tendsto_etvDist_pow_comp hπ hκ (Measure.dirac x)
  simpa only [Measure.dirac_bind (Kernel.measurable _)] using h

/-- **Ergodic theorem for Harris recurrent Markov kernels**. Let `κ` be a Markov kernel on a
countably generated measurable space, with an invariant probability measure `π`. If `κ` is Harris
recurrent with respect to a nonzero measure `φ` and aperiodic, then for
every `x`, the measures `(κ ^ n) x` converge to `π` in total variation.
Ref. *Meyn-Tweedie* Theorem 13.0.1, *Tierney* Theorem 1. -/
theorem IsHarrisRecurrent.tendsto_tvDist_pow_apply (hH : κ.IsHarrisRecurrent φ)
    (hπ : κ.Invariant π) (hκ : κ.IsAperiodic π) (x : α) :
    Tendsto (fun n : ℕ ↦ tvDist ((κ ^ n) x) π) atTop (𝓝 0) :=
  tendsto_tvDist_of_tendsto_etvDist (hH.tendsto_etvDist_pow_apply hπ hκ x)

end Harris

end ProbabilityTheory.Kernel
