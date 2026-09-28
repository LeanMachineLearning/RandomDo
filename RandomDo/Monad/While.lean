/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Monad.Instances
public import RandomDo.Tactic.IsMarkov.Defs
import RandomDo.Monad.Notation
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# `while` loops

`while c rdo body` is a loop over `Lean.Loop`, which runs `body` for as long as `c` holds. Each step
of the loop returns a `ForInStep`: `yield b` to carry on from the state `b`, `done b` to stop there.
Such a loop need not terminate, so its meaning depends on the monad, which provides it through the
class `MeasurableSpaceMonadWhile`.

## Main definitions

* `MeasurableSpaceMonadWhile`: a measurable space monad with an unbounded loop. Its instances:
  - at a core monad, core's loop over `Lean.Loop`;
  - at `Measure`, the least fixed point of "one step, then stop or run the loop again": the sum
    over `n` of the runs that stop at the `n + 1`-th step. The runs that never stop carry no mass.
* `MeasurableSpaceMonad.loopExit f n b`: the runs of the loop whose step is `f` that, from `b`, stop
  at the `n + 1`-th step, in any measurable space monad with a zero.
* `MeasurableSpaceMonad.loopRun f n b`: the runs of that loop that, from `b`, are still going after
  `n` steps.
* The instance of `MeasurableSpaceForIn m Lean.Loop Unit`, for any `MeasurableSpaceMonadWhile m`:
  `while … rdo` runs the loop of the monad.

## Main results

* `MeasurableSpaceMonadWhile.measure_loop_univ_le_one`: at `Measure`, a loop whose step has mass at
  most `1` has mass at most `1`.
* `MeasurableSpaceMonadWhile.isProbabilityMeasure_loop_iff`: at `Measure`, a loop whose step is a
  Markov kernel is a probability measure exactly when the mass of its runs still going after `n`
  steps tends to `0`.

## Implementation notes

The while loop could instead be a field of `MeasurableSpaceMonad` itself. Every program over an
arbitrary measurable space monad could then use `while` with no further hypothesis, as it uses
`for`, at the price of asking every measurable space monad for its own implementation of the loop.

The loop at `Measure` is not defined by `partial_fixpoint`, which also gives the least fixed point,
because it needs the step to be monotone in the loop, over every family `β → Measure β`: this fails
for `Measure.bind`, which is `0` as soon as its continuation is not measurable.

## References

* Dexter Kozen, *Semantics of probabilistic programs*, 1981.
-/

@[expose] public section

universe u v

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

/-- A measurable space monad with an unbounded loop, the one behind `while … rdo`. -/
class MeasurableSpaceMonadWhile (m : (α : Type u) → [MeasurableSpace α] → Type v) where
  /-- Run the step `f` from `b`, then from each state it carries on with, until it stops. -/
  loop {β : Type u} [MeasurableSpace β] (f : β → m (ForInStep β)) (b : β) : m β

/-- At a core monad, the loop is core's loop over `Lean.Loop`. -/
instance {m : Type u → Type v} [Monad m] :
    MeasurableSpaceMonadWhile (Monad.toMeasurableSpaceMonad m) where
  loop f b := ForIn.forIn (m := m) Lean.Loop.mk b fun _ ↦ f

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {β : Type u} [MeasurableSpace β] [Zero (m β)]

/-- The runs of the loop whose step is `f` that, from `b`, stop at the `n + 1`-th step. A run that
does not stop there contributes `0`. -/
def MeasurableSpaceMonad.loopExit (f : β → m (ForInStep β)) : ℕ → β → m β
  -- One step from `b`: keep the runs that stop there, drop the ones that carry on.
  | 0, b => f b >>=ₘ fun s ↦ ForInStep.casesOn (motive := fun _ ↦ m β) s mPure fun _ ↦ 0
  -- One step from `b`: drop the runs that stop there, keep those that stop `n + 1` steps later.
  | n + 1, b => f b >>=ₘ fun s ↦
      ForInStep.casesOn (motive := fun _ ↦ m β) s (fun _ ↦ 0) (loopExit f n)

/-- The runs of the loop whose step is `f` that, from `b`, have not stopped after `n` steps, at the
state they are in. A run that has stopped contributes `0`. -/
def MeasurableSpaceMonad.loopRun (f : β → m (ForInStep β)) : ℕ → β → m β
  -- No step yet: the run is at `b`.
  | 0, b => mPure b
  -- One step from `b`: drop the runs that stop there, keep those still going `n` steps later.
  | n + 1, b => f b >>=ₘ fun s ↦
      ForInStep.casesOn (motive := fun _ ↦ m β) s (fun _ ↦ 0) (loopRun f n)

/-- At `Measure`, the loop is the least fixed point of "one step, then stop or run the loop again":
the sum over `n` of the runs that stop at the `n + 1`-th step. -/
noncomputable instance : MeasurableSpaceMonadWhile Measure where
  loop f b := Measure.sum fun n ↦ MeasurableSpaceMonad.loopExit f n b

/-- The unbounded loop behind `while … rdo` is the loop of the monad. -/
instance [MeasurableSpaceMonadWhile m] : MeasurableSpaceForIn m Lean.Loop Unit where
  forIn _ b f := MeasurableSpaceMonadWhile.loop (f ()) b

section Measure

open scoped ENNReal Topology
open Filter

variable {σ : Type u} [MeasurableSpace σ]

private lemma loopExit_zero (f : σ → Measure (ForInStep σ)) (b : σ) :
    MeasurableSpaceMonad.loopExit f 0 b =
      (f b).bind fun t ↦ ForInStep.casesOn (motive := fun _ ↦ Measure σ) t Measure.dirac
        fun _ ↦ 0 := rfl

private lemma loopExit_succ (f : σ → Measure (ForInStep σ)) (n : ℕ) (b : σ) :
    MeasurableSpaceMonad.loopExit f (n + 1) b =
      (f b).bind fun t ↦ ForInStep.casesOn (motive := fun _ ↦ Measure σ) t (fun _ ↦ 0)
        (MeasurableSpaceMonad.loopExit f n) := rfl

/-- A `while` loop is a sub-probability measure: the runs that stop at the different steps are
disjoint, so their masses add up to at most `1`. -/
lemma MeasurableSpaceMonadWhile.measure_loop_univ_le_one {f : σ → Measure (ForInStep σ)}
    (hf : ∀ s, f s Set.univ ≤ 1) (b : σ) :
    MeasurableSpaceMonadWhile.loop f b Set.univ ≤ 1 := by
  /- The runs that stop at the steps `2, …, n + 1` are one step, followed by the runs that stop at
  the steps `1, …, n`. -/
  have tail : ∀ n b, ∑ k ∈ Finset.range n, MeasurableSpaceMonad.loopExit f (k + 1) b Set.univ ≤
      ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun _ ↦ 0)
        (fun b' ↦ ∑ k ∈ Finset.range n, MeasurableSpaceMonad.loopExit f k b' Set.univ) ∂f b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro b
      rw [Finset.sum_range_succ, loopExit_succ]
      -- Bound each of the two terms by an integral against the first step.
      refine (add_le_add (ih b) (Measure.bind_apply_le _ MeasurableSet.univ)).trans ?_
      -- Merge the two integrals.
      refine (le_lintegral_add _ _).trans (le_of_eq ?_)
      -- The merged integrand is the one of the statement.
      refine lintegral_congr fun t ↦ ?_
      cases t <;> simp [Finset.sum_range_succ]
  -- The runs that stop within `n` steps have mass at most `1`.
  have partialSum : ∀ n b, ∑ k ∈ Finset.range n,
      MeasurableSpaceMonad.loopExit f k b Set.univ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro b
      rw [Finset.sum_range_succ', loopExit_zero]
      -- Bound each of the two terms by an integral against the first step.
      refine (add_le_add (tail n b) (Measure.bind_apply_le _ MeasurableSet.univ)).trans ?_
      -- Merge the two integrals.
      refine (le_lintegral_add _ _).trans ?_
      -- The integral of `1` against the first step is its mass, at most `1`.
      refine le_trans ?_ (lintegral_one.trans_le (hf b))
      -- The merged integrand is at most `1`.
      refine lintegral_mono fun t ↦ ?_
      cases t <;> simp [ih]
  change Measure.sum (fun n ↦ MeasurableSpaceMonad.loopExit f n b) Set.univ ≤ 1
  rw [Measure.sum_apply _ MeasurableSet.univ, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun n ↦ partialSum n b

private lemma loopRun_zero (f : σ → Measure (ForInStep σ)) (b : σ) :
    MeasurableSpaceMonad.loopRun f 0 b = Measure.dirac b := rfl

private lemma loopRun_succ (f : σ → Measure (ForInStep σ)) (n : ℕ) (b : σ) :
    MeasurableSpaceMonad.loopRun f (n + 1) b =
      (f b).bind fun t ↦ ForInStep.casesOn (motive := fun _ ↦ Measure σ) t (fun _ ↦ 0)
        (MeasurableSpaceMonad.loopRun f n) := rfl

private lemma measurable_casesOn {γ : Type*} [MeasurableSpace γ] {d y : σ → γ}
    (hd : Measurable d) (hy : Measurable y) :
    Measurable fun t : ForInStep σ ↦ ForInStep.casesOn (motive := fun _ ↦ γ) t d y :=
  fun _ hs ↦ ⟨hy hs, hd hs⟩

/-- Binding a case analysis on the outcome of a step, evaluated on the whole space. -/
private lemma bind_casesOn_apply_univ (μ : Measure (ForInStep σ)) {d y : σ → Measure σ}
    (hd : Measurable d) (hy : Measurable y) :
    μ.bind (fun t ↦ ForInStep.casesOn (motive := fun _ ↦ Measure σ) t d y) Set.univ =
      ∫⁻ t, ForInStep.casesOn (motive := fun _ ↦ ℝ≥0∞) t (fun s ↦ d s Set.univ)
        (fun s ↦ y s Set.univ) ∂μ := by
  rw [Measure.bind_apply MeasurableSet.univ (measurable_casesOn hd hy).aemeasurable]
  exact lintegral_congr fun t ↦ by cases t <;> rfl

private lemma measurable_loopExit {f : σ → Measure (ForInStep σ)} (hf : Measurable f) :
    ∀ n, Measurable (MeasurableSpaceMonad.loopExit f n)
  | 0 => (Measure.measurable_bind'
      (measurable_casesOn Measure.measurable_dirac measurable_const)).comp hf
  | n + 1 => (Measure.measurable_bind'
      (measurable_casesOn measurable_const (measurable_loopExit hf n))).comp hf

private lemma measurable_loopRun {f : σ → Measure (ForInStep σ)} (hf : Measurable f) :
    ∀ n, Measurable (MeasurableSpaceMonad.loopRun f n)
  | 0 => Measure.measurable_dirac
  | n + 1 => (Measure.measurable_bind'
      (measurable_casesOn measurable_const (measurable_loopRun hf n))).comp hf

/-- The runs still going after `n` steps are those that stop at the next step, and those still going
after it. -/
private lemma loopRun_apply_univ (f : σ → Measure (ForInStep σ)) [hf : IsMarkov f] (n : ℕ)
    (b : σ) :
    MeasurableSpaceMonad.loopRun f n b Set.univ =
      MeasurableSpaceMonad.loopExit f n b Set.univ +
        MeasurableSpaceMonad.loopRun f (n + 1) b Set.univ := by
  induction n generalizing b with
  | zero =>
    have := hf.isProbabilityMeasure b
    rw [loopExit_zero, loopRun_succ,
      bind_casesOn_apply_univ _ Measure.measurable_dirac measurable_const,
      bind_casesOn_apply_univ _ measurable_const (measurable_loopRun hf.measurable 0)]
    simp only [loopRun_zero, measure_univ, Measure.coe_zero, Pi.zero_apply]
    -- Merge the two integrals: the integrand is `1` whether the step stops or not.
    rw [← lintegral_add_left (measurable_casesOn measurable_const measurable_const)]
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂f b := by simp
      _ = _ := lintegral_congr fun t ↦ by cases t <;> simp
  | succ n ih =>
    have hExit : Measurable fun s ↦ MeasurableSpaceMonad.loopExit f n s Set.univ :=
      (Measure.measurable_coe MeasurableSet.univ).comp (measurable_loopExit hf.measurable n)
    rw [loopRun_succ f n b, loopExit_succ, loopRun_succ f (n + 1) b,
      bind_casesOn_apply_univ _ measurable_const (measurable_loopRun hf.measurable n),
      bind_casesOn_apply_univ _ measurable_const (measurable_loopExit hf.measurable n),
      bind_casesOn_apply_univ _ measurable_const (measurable_loopRun hf.measurable (n + 1))]
    simp only [Measure.coe_zero, Pi.zero_apply]
    -- Merge the two integrals, and use the statement for `n` from the state the step carries on.
    rw [← lintegral_add_left (measurable_casesOn measurable_const hExit)]
    exact lintegral_congr fun t ↦ by cases t <;> simp [ih]

/-- The runs that stop within `n` steps and the runs still going after `n` steps have a total mass
of `1`. -/
private lemma sum_loopExit_add_loopRun (f : σ → Measure (ForInStep σ)) [IsMarkov f] (n : ℕ)
    (b : σ) :
    ∑ k ∈ Finset.range n, MeasurableSpaceMonad.loopExit f k b Set.univ +
      MeasurableSpaceMonad.loopRun f n b Set.univ = 1 := by
  induction n with
  | zero => simp [loopRun_zero]
  | succ n ih => rw [Finset.sum_range_succ, add_assoc, ← loopRun_apply_univ, ih]

/-- A `while` loop whose step is a Markov kernel is a probability measure exactly when it stops
almost surely: when the runs still going after `n` steps have a mass that tends to `0`. -/
theorem MeasurableSpaceMonadWhile.isProbabilityMeasure_loop_iff (f : σ → Measure (ForInStep σ))
    [hf : IsMarkov f] (b : σ) :
    IsProbabilityMeasure (MeasurableSpaceMonadWhile.loop f b) ↔
      Tendsto (fun n ↦ MeasurableSpaceMonad.loopRun f n b Set.univ) atTop (𝓝 0) := by
  -- The runs that stop within `n` steps have a mass that tends to the mass of the loop.
  have hExit : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, MeasurableSpaceMonad.loopExit f k b Set.univ)
      atTop (𝓝 (MeasurableSpaceMonadWhile.loop f b Set.univ)) := by
    change Tendsto _ _ (𝓝 (Measure.sum (fun n ↦ MeasurableSpaceMonad.loopExit f n b) Set.univ))
    rw [Measure.sum_apply _ MeasurableSet.univ]
    exact ENNReal.tendsto_nat_tsum _
  -- So the runs still going after `n` steps have a mass that tends to `1` minus it.
  have hRun : Tendsto (fun n ↦ MeasurableSpaceMonad.loopRun f n b Set.univ) atTop
      (𝓝 (1 - MeasurableSpaceMonadWhile.loop f b Set.univ)) := by
    have h n : MeasurableSpaceMonad.loopRun f n b Set.univ =
        1 - ∑ k ∈ Finset.range n, MeasurableSpaceMonad.loopExit f k b Set.univ := by
      have hsum := sum_loopExit_add_loopRun f n b
      refine ENNReal.eq_sub_of_add_eq ?_ ((add_comm _ _).trans hsum)
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_self_add)
    simp_rw [h]
    exact ENNReal.Tendsto.sub tendsto_const_nhds hExit (Or.inl ENNReal.one_ne_top)
  rw [isProbabilityMeasure_iff]
  constructor
  · intro h
    simpa [h] using hRun
  · intro h
    refine le_antisymm ?_ (tsub_eq_zero_iff_le.1 (tendsto_nhds_unique hRun h))
    refine measure_loop_univ_le_one (fun s ↦ ?_) b
    have := hf.isProbabilityMeasure s
    simp

end Measure
