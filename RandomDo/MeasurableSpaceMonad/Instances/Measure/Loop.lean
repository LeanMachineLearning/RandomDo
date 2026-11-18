/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.Instances.Measure
public import RandomDo.MeasurableSpaceMonad.ForIn

/-!
# Unbounded loops of measures

A loop is the sum of the measures of runs exiting at each finite step. Runs which never exit
contribute no mass. For a measurable, probability-preserving body, the result has mass one
exactly when the probability of still running after `n` steps tends to zero.

## Main definitions

* `Measure.loop`: the measure of finite exits, supplying the unbounded-loop instance for `Measure`.
* `Measure.Terminates`: the mass of unfinished runs tends to zero.

## Main theorems

* `Measure.loop_eq`: the one-step loop equation.
* `Measure.measurable_loop`: a measurable body gives a loop measurable in its initial state.
* `Measure.loop_le_of_prefixed`: the loop is below every measurable pre-fixed point.
* `Measure.isProbabilityMeasure_loop_iff`: probability-preserving steps give a probability
  measure exactly when the loop terminates almost surely.

No normalization is performed. In particular, a loop which exits with probability one half
returns a measure of mass one half, and a loop which never exits returns zero.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

-- No core analogue: core does not enumerate probabilistic exit times. These two recursions
-- are adapted from Gaëtan's `loopExit` and `loopRun` in `RandomDo/Monad/While.lean`
-- on `origin/loops` (c0f8f5b). They are specialized to measures, where zero represents discarded
-- runs.
/-- The measure of runs exiting at step `n + 1`. -/
noncomputable def loopExit (f : α → Measure (ForInStep α)) : ℕ → α → Measure α
  | 0 => fun b => (f b).bind fun
      | .done b' => dirac b'
      | .yield _ => 0
  | n + 1 => fun b => (f b).bind fun
      | .done _ => 0
      | .yield b' => loopExit f n b'

/-- The measure of states reached by runs which have not exited after `n` steps. -/
noncomputable def loopRun (f : α → Measure (ForInStep α)) : ℕ → α → Measure α
  | 0 => fun b => dirac b
  | n + 1 => fun b => (f b).bind fun
      | .done _ => 0
      | .yield b' => loopRun f n b'

-- Adapted from Gaëtan's measure loop instance in the same file. The related core operation
-- is `Lean.Loop.forIn`, but its arbitrary fixed-point selection is not used here.
#check Lean.Loop.forIn

/-- Run a measure-valued loop, summing the contributions of all finite exit times. -/
noncomputable def loop (f : α → Measure (ForInStep α)) (b : α) : Measure α :=
  sum fun n => loopExit f n b

-- No separate core analogues for the measurability lemmas below. They adapt Gaëtan's proofs
-- to the existing `ForInStep` measurability API, with all spaces retained explicitly.
@[fun_prop] theorem measurable_loopExit {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (n : ℕ) : Measurable (loopExit f n) := by
  induction n with
  | zero => exact (measurable_bind'
      (measurable_fun_forInStep measurable_dirac measurable_const)).comp hf
  | succ n ih => exact (measurable_bind'
      (measurable_fun_forInStep measurable_const ih)).comp hf

@[fun_prop] theorem measurable_loopRun {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (n : ℕ) : Measurable (loopRun f n) := by
  induction n with
  | zero => exact measurable_dirac
  | succ n ih => exact (measurable_bind'
      (measurable_fun_forInStep measurable_const ih)).comp hf

@[fun_prop] theorem measurable_loop {f : α → Measure (ForInStep α)} (hf : Measurable f) :
    Measurable (loop f) := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp only [loop, sum_apply _ hs]
  exact Measurable.tsum fun n => (measurable_coe hs).comp (measurable_loopExit hf n)

-- No core analogues: these evaluate finite-exit measures. The integral calculations also
-- appear in `Verification/While.lean` at 6e9f206, over Gaëtan's loop implementation.
theorem lintegral_loopExit_zero (f : α → Measure (ForInStep α)) (b : α)
    {Q : α → ℝ≥0∞} (hQ : Measurable Q) :
    ∫⁻ a, Q a ∂loopExit f 0 b = ∫⁻ t, (match t with
      | .done a => Q a | .yield _ => 0) ∂f b := by
  rw [loopExit, lintegral_bind
    (measurable_fun_forInStep (by fun_prop) (by fun_prop)).aemeasurable hQ.aemeasurable]
  exact lintegral_congr fun t => by cases t <;> simp [lintegral_dirac' _ hQ]

theorem lintegral_loopExit_succ {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (n : ℕ) (b : α) {Q : α → ℝ≥0∞} (hQ : Measurable Q) :
    ∫⁻ a, Q a ∂loopExit f (n + 1) b = ∫⁻ t, (match t with
      | .done _ => 0 | .yield a => ∫⁻ x, Q x ∂loopExit f n a) ∂f b := by
  rw [loopExit, lintegral_bind
    (measurable_fun_forInStep (by fun_prop) (by fun_prop)).aemeasurable hQ.aemeasurable]
  exact lintegral_congr fun t => by cases t <;> simp

-- The related core equation is proved from `MonadTail`; here countable additivity and
-- measurability justify exchanging the sum over exit times and the integral of one step.
#check Lean.Loop.forIn_eq_of_monadTail

theorem lintegral_loop {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (b : α) {Q : α → ℝ≥0∞} (hQ : Measurable Q) :
    ∫⁻ a, Q a ∂loop f b = ∫⁻ t, (match t with
      | .done a => Q a | .yield a => ∫⁻ x, Q x ∂loop f a) ∂f b := by
  rw [loop, lintegral_sum_measure, tsum_eq_zero_add' ENNReal.summable]
  simp only [lintegral_loopExit_zero _ _ hQ, lintegral_loopExit_succ hf _ _ hQ]
  have htail (n : ℕ) : Measurable (fun t : ForInStep α => match t with
      | .done _ => (0 : ℝ≥0∞) | .yield a => ∫⁻ x, Q x ∂loopExit f n a) := by fun_prop
  rw [← lintegral_tsum (fun n => (htail n).aemeasurable),
    ← lintegral_add_left (measurable_fun_forInStep (by fun_prop) (by fun_prop))]
  apply lintegral_congr
  intro t
  cases t <;> simp [loop, lintegral_sum_measure]

#check Lean.Loop.forIn_eq_of_monadTail

theorem loop_eq {f : α → Measure (ForInStep α)} (hf : Measurable f) (b : α) :
    loop f b = (f b).bind (fun
      | .done a => dirac a
      | .yield a => loop f a) := by
  ext s hs
  rw [← lintegral_indicator_one hs, lintegral_loop hf b (measurable_one.indicator hs),
    bind_apply hs (measurable_fun_forInStep (by fun_prop) (by fun_prop)).aemeasurable]
  apply lintegral_congr
  intro t
  cases t <;> simp [dirac_apply' _ hs, lintegral_indicator_one hs]

-- No core analogue: core selects an arbitrary fixed point. These finite-horizon bounds
-- prove that the measure interpretation is the least measurable solution of its equation.
theorem lintegral_sum_loopExit_succ {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (n : ℕ) (b : α) {Q : α → ℝ≥0∞} (hQ : Measurable Q) :
    ∑ k ∈ Finset.range (n + 1), ∫⁻ a, Q a ∂loopExit f k b =
      ∫⁻ t, (match t with
        | .done a => Q a
        | .yield a => ∑ k ∈ Finset.range n, ∫⁻ x, Q x ∂loopExit f k a) ∂f b := by
  rw [Finset.sum_range_succ']
  simp only [lintegral_loopExit_succ hf _ _ hQ, lintegral_loopExit_zero _ _ hQ]
  rw [← lintegral_finsetSum _ (fun i _ => by fun_prop)]
  rw [← lintegral_add_left (by fun_prop)]
  apply lintegral_congr
  intro t
  cases t <;> simp

/-- The finite-exit loop is below every measurable pre-fixed point of its one-step equation. -/
theorem loop_le_of_prefixed {f : α → Measure (ForInStep α)} (hf : Measurable f)
    {g : α → Measure α} (hg : Measurable g)
    (h : ∀ b, (f b).bind (fun t => match t with
      | .done a => dirac a | .yield a => g a) ≤ g b) (b : α) : loop f b ≤ g b := by
  refine le_iff.mpr fun s hs => ?_
  rw [← lintegral_indicator_one hs, loop, lintegral_sum_measure, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [lintegral_sum_loopExit_succ hf n b (measurable_one.indicator hs)]
    calc
      _ ≤ ∫⁻ t, (match t with | .done a => dirac a | .yield a => g a) s ∂f b := by
        apply lintegral_mono
        intro t
        cases t with
        | done a => simp [dirac_apply' _ hs]
        | yield a => exact ih a
      _ = ((f b).bind (fun t => match t with
          | .done a => dirac a | .yield a => g a)) s :=
        (bind_apply hs (measurable_fun_forInStep measurable_dirac hg).aemeasurable).symm
      _ ≤ g b s := h b s

-- Same `ForIn` interface as core, with Gaëtan's finite-exit interpretation as its operation.
#check Lean.instForInLoopUnitOfMonad

noncomputable instance : MeasurableSpaceForIn Measure Lean.Loop Unit where
  mForIn _ b f := loop (f ()) b

#check Lean.Loop.forIn_eq_of_monadTail

instance : LawfulMeasurableSpaceLoop Measure where
  mForIn_eq _ _ _ hf := loop_eq hf _

-- No core analogue: the remaining results describe probability mass and almost-sure
-- termination. The conservation argument is adapted from Gaëtan's proofs in
-- `RandomDo/Monad/While.lean` on `origin/loops` (c0f8f5b). Explicit measurability and mass
-- hypotheses replace the old `IsMarkov` tactic-facing class.
@[simp] theorem loopRun_zero_apply_univ (f : α → Measure (ForInStep α)) (b : α) :
    loopRun f 0 b Set.univ = 1 := by simp [loopRun]

theorem loopRun_succ_apply_univ {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (n : ℕ) (b : α) :
    loopRun f (n + 1) b Set.univ = ∫⁻ t, (match t with
      | .done _ => 0 | .yield a => loopRun f n a Set.univ) ∂f b := by
  rw [loopRun, bind_apply MeasurableSet.univ
        (measurable_fun_forInStep (by fun_prop) (by fun_prop)).aemeasurable]
  exact lintegral_congr fun t => by cases t <;> simp

theorem loopRun_apply_univ {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (hprob : ∀ a, f a Set.univ = 1) (n : ℕ) (b : α) :
    loopRun f n b Set.univ = loopExit f n b Set.univ + loopRun f (n + 1) b Set.univ := by
  induction n generalizing b with
  | zero =>
    rw [loopRun_zero_apply_univ, loopExit, loopRun,
      bind_apply MeasurableSet.univ
        (measurable_fun_forInStep (by fun_prop) (by fun_prop)).aemeasurable,
      bind_apply MeasurableSet.univ
        (measurable_fun_forInStep (by fun_prop) (by fun_prop)).aemeasurable,
      ← lintegral_add_left (by
        apply measurable_fun_forInStep
        · simp
        · exact measurable_const)]
    calc
      (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂f b := by simp [hprob]
      _ = _ := lintegral_congr fun t => by cases t <;> simp [loopRun]
  | succ n ih =>
    rw [loopRun_succ_apply_univ hf, loopExit,
      bind_apply MeasurableSet.univ
        (measurable_fun_forInStep (by fun_prop) (by fun_prop)).aemeasurable,
      loopRun_succ_apply_univ hf,
      ← lintegral_add_left (measurable_fun_forInStep measurable_const
        ((measurable_coe MeasurableSet.univ).comp (measurable_loopExit hf n)))]
    exact lintegral_congr fun t => by cases t <;> simp [ih]

theorem sum_loopExit_add_loopRun {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (hprob : ∀ a, f a Set.univ = 1) (n : ℕ) (b : α) :
    ∑ k ∈ Finset.range n, loopExit f k b Set.univ + loopRun f n b Set.univ = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc, ← loopRun_apply_univ hf hprob, ih]

theorem loop_apply_univ_le_one {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (hprob : ∀ a, f a Set.univ = 1) (b : α) : loop f b Set.univ ≤ 1 := by
  rw [loop, sum_apply _ MeasurableSet.univ, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun n => (le_self_add.trans_eq (sum_loopExit_add_loopRun hf hprob n b))

theorem antitone_loopRun_apply_univ {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (hprob : ∀ a, f a Set.univ = 1) (b : α) :
    Antitone fun n => loopRun f n b Set.univ :=
  antitone_nat_of_succ_le fun n => (loopRun_apply_univ hf hprob n b).symm ▸ le_add_self

/-- The mass of runs still going after `n` steps tends to zero.
For a measurable, probability-preserving body, this is almost-sure termination. -/
def Terminates (f : α → Measure (ForInStep α)) (b : α) : Prop :=
  Tendsto (fun n => loopRun f n b Set.univ) atTop (𝓝 0)

theorem terminates_done {g : α → α} (hg : Measurable g) (b : α) :
    Terminates (fun a => dirac (.done (g a))) b := by
  unfold Terminates
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp (disch := (apply measurable_fun_forInStep <;> fun_prop)) [loopRun, dirac_bind]

theorem tendsto_loopRun_apply_univ {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (hprob : ∀ a, f a Set.univ = 1) (b : α) :
    Tendsto (fun n => loopRun f n b Set.univ) atTop (𝓝 (1 - loop f b Set.univ)) := by
  have hExit : Tendsto (fun n => ∑ k ∈ Finset.range n, loopExit f k b Set.univ) atTop
      (𝓝 (loop f b Set.univ)) := by
    rw [loop, sum_apply _ MeasurableSet.univ]
    exact ENNReal.tendsto_nat_tsum _
  have h n : loopRun f n b Set.univ = 1 - ∑ k ∈ Finset.range n, loopExit f k b Set.univ := by
    have hsum := sum_loopExit_add_loopRun hf hprob n b
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_self_add.trans_eq hsum)) ((add_comm _ _).trans hsum)
  simp_rw [h]
  exact ENNReal.Tendsto.sub tendsto_const_nhds hExit (Or.inl ENNReal.one_ne_top)

theorem isProbabilityMeasure_loop_iff {f : α → Measure (ForInStep α)} (hf : Measurable f)
    (hprob : ∀ a, f a Set.univ = 1) (b : α) :
    IsProbabilityMeasure (loop f b) ↔ Terminates f b := by
  have hRun := tendsto_loopRun_apply_univ hf hprob b
  rw [isProbabilityMeasure_iff, Terminates]
  constructor
  · intro h
    simpa [h] using hRun
  · intro h
    exact le_antisymm (loop_apply_univ_le_one hf hprob b)
      (tsub_eq_zero_iff_le.1 (tendsto_nhds_unique hRun h))

end MeasureTheory.Measure
