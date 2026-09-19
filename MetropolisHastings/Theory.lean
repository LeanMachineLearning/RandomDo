/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MetropolisHastings.Defs
public import Mathlib.Probability.Kernel.Invariance

/-!
# Random-walk Metropolis–Hastings leaves its target invariant

We prove that one step of the chain, `mhStep logπ s`, satisfies detailed balance with respect to
the target `π(dx) = exp (logπ x) dx`, hence leaves it invariant, and that so does the whole chain
`mhChain logπ s n` for every number of steps `n`: started from the target, the chain has the target
as its law at every step.

The log-density is assumed measurable, through the instance `Fact (Measurable logπ)`, so that the
programs are Markov kernels: that is the instance `isMarkov_mhStep`, proved by `is_markov`.

## The proof

A step proposes `y ∼ Q x` and moves there with probability `p x y`. The mass it sends from a set
`A` into a set `B` is then the *flow* of accepted moves from `A` to `B`, plus the mass of `A ∩ B`
that stays put on rejection. The second term is symmetric in `A` and `B`, so the kernel satisfies
detailed balance as soon as the flow is: that is `isReversible_acceptReject`, for any proposal.

For the Gaussian proposal, the flow has density `min (π x) (π y) · φ_s(y - x)` against Lebesgue on
`ℝ × ℝ` (`flow_eq`), which is symmetric in `x` and `y`. Swapping the two integrals (Tonelli) gives
the symmetry of the flow (`flow_symm`).

## Main results

* `isReversible_acceptReject`: a proposal followed by an accept-reject step satisfies detailed
  balance as soon as its flow of accepted moves is symmetric.
* `isReversible_mhStep`: **detailed balance** of `mhStep logπ s` with respect to `target logπ`.
* `invariant_mhStep`: `target logπ` is invariant for `mhStep logπ s`.
* `mhChain_zero`, `mhChain_succ`: the `for` loop of `mhChain` unrolled, one step at a time.
* `invariant_mhChain`: `target logπ` is invariant for `mhChain logπ s n`, for every `n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval Function
open MeasurableSpacePure LawfulMeasurableSpaceMonad
open scoped ENNReal NNReal

namespace MetropolisHastings

section AcceptReject

variable {α : Type*} [MeasurableSpace α]

lemma bernoulliMeasure_apply_eq (y x : α) (q : I) {B : Set α} (hB : MeasurableSet B) :
    Ber(y, x, q) B = toNNReal q * B.indicator 1 y + toNNReal (σ q) * B.indicator 1 x := by
  simp only [bernoulliMeasure_def, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hB, ENNReal.smul_def, smul_eq_mul]

/-- The mass a proposal from `Q x` followed by an accept-reject step sends into `B`: the accepted
moves into `B`, and, when `x ∈ B`, the rejected ones. -/
lemma acceptReject_apply (Q : Kernel α α) {p : α → α → I} (hp : Measurable (uncurry p))
    (x : α) {B : Set α} (hB : MeasurableSet B) :
    ((Q x).bind fun y ↦ Ber(y, x, p x y)) B
      = ∫⁻ y in B, (toNNReal (p x y) : ℝ≥0∞) ∂Q x
        + B.indicator (fun x ↦ ∫⁻ y, (toNNReal (σ (p x y)) : ℝ≥0∞) ∂Q x) x := by
  have hpx : Measurable (p x) := hp.comp (measurable_const.prodMk measurable_id)
  have hmeas : Measurable fun y ↦ Ber(y, x, p x y) :=
    (IsMarkov.bernoulliMeasure measurable_id measurable_const hpx).measurable
  rw [Measure.bind_apply hB hmeas.aemeasurable]
  simp_rw [bernoulliMeasure_apply_eq _ _ _ hB]
  rw [lintegral_add_left (by fun_prop), lintegral_mul_const _ (by fun_prop),
    ← lintegral_indicator hB]
  congr 1
  · congr with y
    by_cases hy : y ∈ B <;> simp [hy]
  · by_cases hx : x ∈ B <;> simp [hx]

/-- A proposal from `Q` followed by an accept-reject step with acceptance probability `p` satisfies
detailed balance with respect to `π` as soon as its flow of accepted moves is symmetric. -/
lemma isReversible_acceptReject {κ : Kernel α α} (Q : Kernel α α) [IsSFiniteKernel Q]
    {p : α → α → I} (hp : Measurable (uncurry p))
    (hκ : ∀ x, κ x = (Q x).bind fun y ↦ Ber(y, x, p x y)) {π : Measure α}
    (hflow : ∀ ⦃A B⦄, MeasurableSet A → MeasurableSet B →
      ∫⁻ x in A, ∫⁻ y in B, (toNNReal (p x y) : ℝ≥0∞) ∂Q x ∂π
        = ∫⁻ x in B, ∫⁻ y in A, (toNNReal (p x y) : ℝ≥0∞) ∂Q x ∂π) :
    κ.IsReversible π := by
  intro A B hA hB
  simp_rw [hκ, acceptReject_apply Q hp _ hB, acceptReject_apply Q hp _ hA]
  have hrej : Measurable fun x ↦ ∫⁻ y, (toNNReal (σ (p x y)) : ℝ≥0∞) ∂Q x :=
    Measurable.lintegral_kernel_prod_right' (f := fun z ↦ (toNNReal (σ (p z.1 z.2)) : ℝ≥0∞))
      (by fun_prop)
  rw [lintegral_add_right _ (hrej.indicator hB), lintegral_add_right _ (hrej.indicator hA),
    hflow hA hB, lintegral_indicator hB, lintegral_indicator hA, Measure.restrict_restrict hB,
    Measure.restrict_restrict hA, Set.inter_comm]

end AcceptReject

section Gaussian

variable {logπ : ℝ → ℝ} {s : ℝ≥0}

instance : IsMarkov fun x : ℝ ↦ gaussianReal x s :=
  IsMarkov.gaussianReal measurable_id measurable_const

/-- A step of the chain is a Gaussian proposal followed by an accept-reject step. -/
lemma mhStep_eq_bind (logπ : ℝ → ℝ) (s : ℝ≥0) (x : ℝ) :
    mhStep logπ s x = (gaussianReal x s).bind fun y ↦ Ber(y, x, acceptProb logπ x y) := by
  change (gaussianReal x s).bind (fun y ↦ (Ber(true, false, acceptProb logπ x y)).bind
    fun b ↦ Measure.dirac (if b = true then y else x)) = _
  congr with y : 1
  rw [Measure.bind_dirac_eq_map _ (by fun_prop), map_bernoulliMeasure]
  simp

lemma coe_toNNReal_eq_ofReal (q : I) : (toNNReal q : ℝ≥0∞) = ENNReal.ofReal q := by
  rw [← ENNReal.ofReal_coe_nnreal, coe_toNNReal]

/-- The density of the flow of accepted moves, `π(dx) 𝒩(x, s)(dy) a(x, y)`, against Lebesgue on
`ℝ × ℝ`: `min (π x) (π y)` times the Gaussian density. -/
noncomputable def flowDensity (logπ : ℝ → ℝ) (s : ℝ≥0) (x y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (min (Real.exp (logπ x)) (Real.exp (logπ y))) * gaussianPDF x s y

lemma flowDensity_comm (x y : ℝ) : flowDensity logπ s x y = flowDensity logπ s y x := by
  simp only [flowDensity, gaussianPDF, gaussianPDFReal, min_comm]
  congr 4
  ring

lemma measurable_flowDensity (hπ : Measurable logπ) : Measurable (uncurry (flowDensity logπ s)) :=
  (by fun_prop : Measurable fun z : ℝ × ℝ ↦
      ENNReal.ofReal (min (Real.exp (logπ z.1)) (Real.exp (logπ z.2)))).mul
    (measurable_uncurry_gaussianPDF.comp (measurable_fst.prodMk (measurable_const.prodMk
      measurable_snd)))

/-- The heart of the matter: the density of the target at `x`, times the probability of accepting a
move from `x` to `y`, is the smaller of the densities at `x` and `y`. -/
lemma exp_mul_acceptProb (x y : ℝ) :
    ENNReal.ofReal (Real.exp (logπ x)) * (toNNReal (acceptProb logπ x y) : ℝ≥0∞)
      = ENNReal.ofReal (min (Real.exp (logπ x)) (Real.exp (logπ y))) := by
  rw [coe_toNNReal_eq_ofReal, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  simp only [acceptProb]
  rw [mul_min_of_nonneg _ _ (Real.exp_nonneg _), mul_one, ← Real.exp_add, add_sub_cancel]

lemma flow_eq (hπ : Measurable logπ) (hs : s ≠ 0) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ∫⁻ x in A, ∫⁻ y in B, (toNNReal (acceptProb logπ x y) : ℝ≥0∞) ∂gaussianReal x s ∂target logπ
      = ∫⁻ x in A, ∫⁻ y in B, flowDensity logπ s x y := by
  rw [target, restrict_withDensity hA, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (by fun_prop) (by simp)]
  congr with x
  rw [Pi.mul_apply, gaussianReal_of_var_ne_zero _ hs, restrict_withDensity hB,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_gaussianPDF _ _)
      (by simp [gaussianPDF_lt_top]), ← lintegral_const_mul' _ _ (by simp)]
  congr with y
  rw [flowDensity, ← exp_mul_acceptProb, Pi.mul_apply]
  ring

/-- With zero variance the proposal is the current state, and the flow from `A` to `B` is the
mass of `A ∩ B`. -/
lemma flow_zero_var {A B : Set ℝ} (hB : MeasurableSet B) :
    ∫⁻ x in A, ∫⁻ y in B, (toNNReal (acceptProb logπ x y) : ℝ≥0∞) ∂gaussianReal x 0 ∂target logπ
      = ∫⁻ x in A ∩ B, (toNNReal (acceptProb logπ x x) : ℝ≥0∞) ∂target logπ := by
  classical
  simp_rw [gaussianReal_zero_var, setLIntegral_dirac]
  rw [Set.inter_comm, ← Measure.restrict_restrict hB, ← lintegral_indicator hB]
  simp only [Set.indicator_apply]

lemma flow_symm (hπ : Measurable logπ) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ∫⁻ x in A, ∫⁻ y in B, (toNNReal (acceptProb logπ x y) : ℝ≥0∞) ∂gaussianReal x s ∂target logπ
      = ∫⁻ x in B, ∫⁻ y in A, (toNNReal (acceptProb logπ x y) : ℝ≥0∞) ∂gaussianReal x s
          ∂target logπ := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [flow_zero_var hB, flow_zero_var hA, Set.inter_comm]
  rw [flow_eq hπ hs hA hB, flow_eq hπ hs hB hA,
    lintegral_lintegral_swap (measurable_flowDensity hπ).aemeasurable]
  exact lintegral_congr fun y ↦ lintegral_congr fun x ↦ flowDensity_comm x y

end Gaussian

section Theorems

variable (logπ : ℝ → ℝ) (s : ℝ≥0) [hπ : Fact (Measurable logπ)]

instance isMarkov_mhStep : IsMarkov (mhStep logπ s) := by
  have := hπ.out
  is_markov

instance isMarkov_mhChain (n : ℕ) : IsMarkov (mhChain logπ s n) := by
  have := hπ.out
  is_markov

/-- **Detailed balance** of random-walk Metropolis–Hastings: the flow of mass from `A` to `B` under
the target equals the flow from `B` to `A`. -/
theorem isReversible_mhStep :
    (IsMarkov.toKernel (mhStep logπ s)).IsReversible (target logπ) :=
  isReversible_acceptReject (IsMarkov.toKernel fun x ↦ gaussianReal x s) (p := acceptProb logπ)
    (measurable_acceptProb hπ.out measurable_fst measurable_snd) (mhStep_eq_bind logπ s)
    fun _ _ hA hB ↦ flow_symm hπ.out hA hB

/-- The target is invariant for one step of random-walk Metropolis–Hastings. -/
theorem invariant_mhStep : (target logπ).bind (mhStep logπ s) = target logπ :=
  (isReversible_mhStep logπ s).invariant

omit hπ in
/-- A `for` loop whose body does not look at the index only sees the length of the list. -/
lemma forIn_congr_length {ι : Type} (g : ℝ → Measure (ForInStep ℝ)) :
    ∀ (l l' : List ι), l.length = l'.length → ∀ x : ℝ,
      MeasurableSpaceForIn.forIn (m := Measure) l x (fun _ ↦ g)
        = MeasurableSpaceForIn.forIn (m := Measure) l' x (fun _ ↦ g)
  | [], [], _, _ => rfl
  | _ :: l, _ :: l', h, x => by
    rw [IsMarkov.forIn_cons, IsMarkov.forIn_cons]
    refine MeasurableSpaceBind.bind_congr fun step ↦ ?_
    cases step with
    | done => rfl
    | yield y => exact forIn_congr_length g l l' (by simpa using h) y

omit hπ in
lemma mhChain_eq_forIn (n : ℕ) (x₀ : ℝ) :
    mhChain logπ s n x₀ = MeasurableSpaceForIn.forIn (m := Measure) (List.range n) x₀
      (fun _ z ↦ mhStep logπ s z >>=ₘ fun y ↦ mPure (ForInStep.yield y)) :=
  mBind_mPure _

omit hπ in
lemma mhChain_zero (x₀ : ℝ) : mhChain logπ s 0 x₀ = Measure.dirac x₀ := by
  rw [mhChain_eq_forIn, List.range_zero, IsMarkov.forIn_nil]
  rfl

/-- `n + 1` steps of the chain are one step, followed by `n` steps. -/
lemma mhChain_succ (n : ℕ) (x₀ : ℝ) :
    mhChain logπ s (n + 1) x₀ = (mhStep logπ s x₀).bind (mhChain logπ s n) := by
  rw [mhChain_eq_forIn, List.range_succ_eq_map, IsMarkov.forIn_cons]
  have hk : Measurable fun step : ForInStep ℝ ↦ ForInStep.casesOn (motive := fun _ ↦ Measure ℝ)
      step mPure (mhChain logπ s n) :=
    (ForInStep.measurable_CasesOn (done := fun (_ : Unit) (b : ℝ) ↦ (mPure b : Measure ℝ))
      (yield := fun _ b ↦ mhChain logπ s n b) (by fun_prop)
      ((isMarkov_mhChain logπ s n).measurable.comp measurable_snd)).comp
      (measurable_const.prodMk measurable_id : Measurable fun step : ForInStep ℝ ↦ ((), step))
  have hloop : ∀ step : ForInStep ℝ, ForInStep.casesOn (motive := fun _ ↦ Measure ℝ) step mPure
      (fun b' ↦ MeasurableSpaceForIn.forIn (m := Measure) (List.map Nat.succ (List.range n)) b'
        (fun _ z ↦ mhStep logπ s z >>=ₘ fun y ↦ mPure (ForInStep.yield y)))
      = ForInStep.casesOn (motive := fun _ ↦ Measure ℝ) step mPure (mhChain logπ s n) := by
    rintro (b | b)
    · rfl
    · exact (forIn_congr_length _ _ _ (by simp) b).trans (mhChain_eq_forIn logπ s n b).symm
  rw [MeasurableSpaceBind.bind_congr hloop, mBind_assoc _ (by fun_prop) hk]
  refine MeasurableSpaceBind.bind_congr fun y ↦ ?_
  rw [mPure_mBind _ hk]

/-- **Stationarity**: the target is invariant for `n` steps of random-walk Metropolis–Hastings. -/
theorem invariant_mhChain (n : ℕ) : (target logπ).bind (mhChain logπ s n) = target logπ := by
  induction n with
  | zero =>
    rw [funext (mhChain_zero logπ s)]
    exact Measure.bind_dirac
  | succ n ih =>
    rw [funext (mhChain_succ logπ s n), ← Measure.bind_bind
      (isMarkov_mhStep logπ s).measurable.aemeasurable
      (isMarkov_mhChain logπ s n).measurable.aemeasurable, invariant_mhStep, ih]

/-- Stationarity, for any multiple of the target: in particular for the normalised target, a
probability measure when the total mass of `target logπ` is finite and positive. Started from it,
the chain has it as its law at every step. -/
theorem invariant_mhChain_smul (c : ℝ≥0∞) (n : ℕ) :
    (c • target logπ).bind (mhChain logπ s n) = c • target logπ := by
  rw [Measure.bind_smul _ _ (isMarkov_mhChain logπ s n).measurable.aemeasurable,
    invariant_mhChain]

end Theorems

end MetropolisHastings
