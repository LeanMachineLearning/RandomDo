module

public import Test.Common
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.Probability.Distributions.Binomial

set_option linter.style.header false

/-!
# Independent draws and Bernoulli sums

These tests use uncountable stream spaces without a `MeasurableEvalDomain` assumption.
They check exact state consumption, independent draws from measures, dependent kernel draws,
and the binomial law of a sum of `n` Bernoulli samples.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableSpacePure MeasurableSpaceBind MeasurableSpaceFunctor
open scoped BigOperators

namespace Test.SampleM

/-- Draw two fair coins directly from a stream of fair coins. -/
noncomputable def twoFairCoins : SampleM Bool fairCoin (Bool × Bool) := rdo
  let a ← SampleM.draw fairCoin
  let b ← SampleM.draw fairCoin
  return (a, b)

example (ω : ℕ → Bool) :
    twoFairCoins.sample ω = ((ω 0, ω 1), fun n ↦ ω (n + 2)) := by
  simp [twoFairCoins, Nat.add_assoc]

theorem law_twoFairCoins : twoFairCoins.law = fairCoin.prod fairCoin := by
  change (SampleM.draw fairCoin >>=ₘ fun a ↦ Prod.mk a <$>ₘ SampleM.draw fairCoin).law = _
  rw [RandomM.law_mBind_mMap_pair]
  simp

example (a b : Bool) : twoFairCoins.law {(a, b)} = (1 : ENNReal) / 4 := by
  have h (b : Bool) : fairCoin {b} = (1 : ENNReal) / 2 := by
    cases b <;> norm_num [fairCoin, bernoulliMeasure_apply, unitInterval.toNNReal] <;>
      change ((1 / 2 : NNReal) : ENNReal) = _ <;> norm_num
  rw [law_twoFairCoins, ← Set.singleton_prod_singleton, Measure.prod_prod, h, h]
  norm_num [← ENNReal.mul_inv]

section Constructors

universe u

variable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-- Different probability measures can be sampled within the same computation. -/
noncomputable def independentDraws [StandardBorelSpace α] [StandardBorelSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    SampleM unitInterval volume (α × β) := rdo
  let a ← SampleM.ofMeasure μ
  let b ← SampleM.ofMeasure ν
  return (a, b)

example [StandardBorelSpace α] [StandardBorelSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (independentDraws μ ν).law = μ.prod ν := by
  change (SampleM.ofMeasure μ >>=ₘ fun a ↦ Prod.mk a <$>ₘ SampleM.ofMeasure ν).law = _
  rw [RandomM.law_mBind_mMap_pair]
  simp

variable [StandardBorelSpace β] [Nonempty β]

/-- A kernel draw may depend on the previous result, using fresh randomness. -/
noncomputable def dependentDraws (x : SampleM unitInterval volume α)
    (κ : Kernel α β) [IsMarkovKernel κ] : SampleM unitInterval volume β := rdo
  let a ← x
  SampleM.ofKernel κ a

example (x : SampleM unitInterval volume α) (κ : Kernel α β) [IsMarkovKernel κ] :
    (dependentDraws x κ).law = x.law.bind κ := by simp [dependentDraws]

example (κ : Kernel α β) [IsMarkovKernel κ] : Measurable (SampleM.ofKernel κ) := by fun_prop

example (κ : Kernel α β) [IsMarkovKernel κ] :
    Measurable (fun p : α × (ℕ → unitInterval) ↦ (SampleM.ofKernel κ p.1).sample p.2) := by
  fun_prop

end Constructors

universe v

/-- One polymorphic program for counting successes, interpreted as either a sampler or a measure. -/
def sumDraws {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] (coin : m Bool) : ℕ → m ℕ
  | 0 => rdo return 0
  | n + 1 => rdo
    let b ← coin
    let s ← sumDraws coin n
    return b.toNat + s

attribute [rdo_program] sumDraws

/-- Taking the sampler's law agrees with interpreting the same program in the measure monad. -/
theorem law_sumDraws {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (coin : RandomM Ω P Bool) (n : ℕ) :
    (sumDraws coin n).law = sumDraws (m := Measure) coin.law n :=
  sumDraws.law coin n

theorem law_sumDraws_congr {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (coin : RandomM Ω P Bool) (coin' : RandomM Ω' P' Bool) (h : coin.law = coin'.law)
    (n : ℕ) : (sumDraws coin n).law = (sumDraws coin' n).law := by
  induction n with
  | zero => simp [sumDraws]
  | succ n ih => simp only [sumDraws, RandomM.law_mBind_of_countable, RandomM.law_mPure, h, ih]

theorem sample_sumDraws_draw (P : Measure Bool) [IsProbabilityMeasure P]
    (n : ℕ) (ω : ℕ → Bool) :
    (sumDraws (SampleM.draw P) n).sample ω =
      (∑ i ∈ Finset.range n, (ω i).toNat, fun i ↦ ω (i + n)) := by
  induction n generalizing ω with
  | zero => simp [sumDraws]
  | succ n ih =>
    simp [sumDraws, ih, Finset.sum_range_succ', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private theorem ncard_successes (n : ℕ) (ω : ℕ → Bool) :
    {i | i < n ∧ ω i = true}.ncard = ∑ i ∈ Finset.range n, (ω i).toNat := by
  have hs : {i | i < n ∧ ω i = true} = ↑((Finset.range n).filter fun i ↦ ω i = true) := by
    ext i
    simp
  rw [hs, Set.ncard_coe_finset, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases ω i <;> rfl

private theorem law_successes (n : ℕ) (p : unitInterval) :
    (Measure.infinitePi fun _ : ℕ ↦ bernoulliMeasure true false p).map
      (fun ω : ℕ → Bool ↦ {i | i < n ∧ ω i = true}) = setBernoulli (Set.Iio n) p := by
  rw [setBernoulli_eq_map]
  have h : (Measure.infinitePi fun _ : ℕ ↦ bernoulliMeasure true false p).map
      (fun ω : ℕ → Bool ↦ fun i ↦ i < n ∧ ω i = true) =
      Measure.infinitePi (fun i : ℕ ↦ bernoulliMeasure (i < n) False p) := by
    rw [Measure.infinitePi_map_pi _ (f := fun i (b : Bool) ↦ i < n ∧ b = true) (by fun_prop)]
    congr 1
    funext i
    rw [map_bernoulliMeasure' _ _ (by fun_prop)]
    simp
  have h' := congrArg (Measure.map (fun f : ℕ → Prop ↦ {i | f i})) h
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h'
  simpa only [Function.comp_def, Set.mem_Iio] using h'

theorem law_sumDraws_draw (n : ℕ) (p : unitInterval) :
    (sumDraws (SampleM.draw (bernoulliMeasure true false p)) n).law = binomial n p := by
  have hs :
      (fun ω : ℕ → Bool ↦
        ((sumDraws (SampleM.draw (bernoulliMeasure true false p)) n).sample ω).1) =
      fun ω ↦ {i | i < n ∧ ω i = true}.ncard := by
    funext ω
    simp [sample_sumDraws_draw, ncard_successes]
  change (Measure.infinitePi fun _ : ℕ ↦ bernoulliMeasure true false p).map
    (fun ω ↦ ((sumDraws (SampleM.draw (bernoulliMeasure true false p)) n).sample ω).1) = _
  rw [hs]
  change (Measure.infinitePi fun _ : ℕ ↦ bernoulliMeasure true false p).map
    (Set.ncard ∘ fun ω ↦ {i | i < n ∧ ω i = true}) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), law_successes]
  rfl

/-- Sum `n` independent Bernoulli draws using the general measure-to-sampler constructor. -/
noncomputable def sumBernoulli (p : unitInterval) (n : ℕ) : SampleM unitInterval volume ℕ :=
  sumDraws (SampleM.ofMeasure (bernoulliMeasure true false p)) n

theorem law_sumBernoulli_eq_measure (p : unitInterval) (n : ℕ) :
    (sumBernoulli p n).law = sumDraws (m := Measure) (bernoulliMeasure true false p) n := by
  rw [sumBernoulli, law_sumDraws, SampleM.law_ofMeasure]

theorem law_sumBernoulli (p : unitInterval) (n : ℕ) :
    (sumBernoulli p n).law = binomial n p := by
  rw [sumBernoulli, law_sumDraws_congr _ (SampleM.draw (bernoulliMeasure true false p)) (by simp),
    law_sumDraws_draw]

end Test.SampleM
