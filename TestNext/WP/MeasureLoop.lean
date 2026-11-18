/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

import RandomDo.WP.Measure.Loop
import RandomDo.RDo.Loop
import Lean.Elab.Tactic.VCGen

/-!
# Quantitative loop regressions

Fair-coin repetition has mass one; a never-exiting loop has mass zero; a loop with an absorbing
nonterminating branch retains only the mass of finite exits. Stock `vcgen` verifies both a
quantitative almost-sure-termination rule and a loop over a continuous state space.
A countdown also verifies termination using `decreasing` with quantitative assertions.
-/

set_option linter.privateModule false

open MeasureTheory Measure Std.WP Filter
open scoped ENNReal NNReal Topology
set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace TestNext.WP.MeasureLoop

noncomputable def fairStep (_ : Unit) : Measure (ForInStep Unit) :=
  (2 : ℝ≥0∞)⁻¹ • dirac (.done ()) + (2 : ℝ≥0∞)⁻¹ • dirac (.yield ())

lemma half_add_half : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

lemma fairStep_measurable : Measurable fairStep := measurable_const

lemma fairStep_prob (a : Unit) : fairStep a Set.univ = 1 := by
  simp [fairStep, half_add_half]

lemma fairStep_run (n : Nat) (a : Unit) :
    loopRun fairStep n a Set.univ = (2 : ℝ≥0∞)⁻¹ ^ n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [loopRun_succ_apply_univ fairStep_measurable]
    simp only [fairStep, lintegral_add_measure, lintegral_smul_measure]
    rw [lintegral_dirac' _ (measurable_fun_forInStep measurable_const
      ((measurable_coe MeasurableSet.univ).comp (measurable_loopRun fairStep_measurable n))),
      lintegral_dirac' _ (measurable_fun_forInStep measurable_const
        ((measurable_coe MeasurableSet.univ).comp (measurable_loopRun fairStep_measurable n)))]
    simp [ih, pow_succ, mul_comm]

lemma fairStep_terminates (a : Unit) : Terminates fairStep a := by
  unfold Terminates
  simp_rw [fairStep_run]
  exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)

example : IsProbabilityMeasure (loop fairStep ()) :=
  (isProbabilityMeasure_loop_iff fairStep_measurable fairStep_prob ()).mpr
    (fairStep_terminates ())

@[spec] theorem fairStep_spec (a : Unit) (Q : ForInStep Unit → ℝ≥0∞) (hQ : Measurable Q) :
    Triple (fairStep a) ((2 : ℝ≥0∞)⁻¹ * Q (.done ()) + 2⁻¹ * Q (.yield ())) Q estack⟨⟩ := by
  constructor
  simp [wp_eq_lintegral, fairStep, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac' _ hQ]

-- The quantitative invariant rule must accept almost-sure termination without a decreasing rank.
example :
    Triple (MeasureTheory.WP.mForInLoopWithInvariant Lean.Loop.mk () (fun _ => fairStep)
      (WhileInvariant.mk fun _ _ => (1 : ℝ≥0∞))) 1 (fun _ => 1) estack⟨⟩ := by
  vcgen [fairStep_spec]
  all_goals first
    | exact fairStep_terminates ()
    | fun_prop
    | exact ⟨1, by simp⟩
    | simp [half_add_half]

-- A loop which never exits has zero result, not an arbitrary normalized completion.
lemma spin_exit (n : Nat) (a : Unit) :
    loopExit (fun a : Unit => dirac (.yield a)) n a = 0 := by
  induction n generalizing a with
  | zero => simp (disch := (apply measurable_fun_forInStep <;> fun_prop)) [loopExit, dirac_bind]
  | succ n ih =>
    simp (disch := (apply measurable_fun_forInStep <;> fun_prop)) [loopExit, dirac_bind, ih]

example : loop (fun a : Unit => dirac (.yield a)) () = 0 := by
  simp [loop, spin_exit]

-- A Bool state chooses exit or an absorbing nonterminating state at the first step.
noncomputable def partialStep (start : Bool) : Measure (ForInStep Bool) :=
  if start then (2 : ℝ≥0∞)⁻¹ • dirac (.done true) + (2 : ℝ≥0∞)⁻¹ • dirac (.yield false)
  else dirac (.yield false)

lemma partialStep_false_exit (n : Nat) : loopExit partialStep n false = 0 := by
  induction n with
  | zero =>
    simp (disch := (apply measurable_fun_forInStep <;> fun_prop))
      [loopExit, partialStep, dirac_bind]
  | succ n ih =>
    simp (disch := (apply measurable_fun_forInStep <;> fun_prop))
      [loopExit, partialStep, dirac_bind, ih]

lemma partialStep_exit (n : Nat) :
    loopExit partialStep n true = if n = 0 then (2 : ℝ≥0∞)⁻¹ • dirac true else 0 := by
  cases n with
  | zero =>
    ext s hs
    rw [loopExit, bind_apply hs (by exact (measurable_fun_forInStep
      measurable_dirac measurable_const).aemeasurable)]
    simp only [partialStep, ↓reduceIte, lintegral_add_measure, lintegral_smul_measure]
    rw [lintegral_dirac' _ (by
      apply measurable_fun_forInStep
      · exact (measurable_coe hs).comp measurable_dirac
      · exact measurable_const), lintegral_dirac' _ (by
      apply measurable_fun_forInStep
      · exact (measurable_coe hs).comp measurable_dirac
      · exact measurable_const)]
    simp
  | succ n =>
    ext s hs
    rw [loopExit, bind_apply hs (by exact (measurable_fun_forInStep
      measurable_const (measurable_loopExit (by fun_prop) n)).aemeasurable)]
    simp only [partialStep, ↓reduceIte, lintegral_add_measure, lintegral_smul_measure]
    rw [lintegral_dirac' _ (by
      apply measurable_fun_forInStep
      · exact measurable_const
      · exact (measurable_coe hs).comp (measurable_loopExit (by fun_prop) n)),
      lintegral_dirac' _ (by
      apply measurable_fun_forInStep
      · exact measurable_const
      · exact (measurable_coe hs).comp (measurable_loopExit (by fun_prop) n))]
    simp [partialStep_false_exit]

example : loop partialStep true = (2 : ℝ≥0∞)⁻¹ • dirac true := by
  ext s hs
  simp only [loop, sum_apply _ hs, partialStep_exit]
  have h (n : Nat) : (if n = 0 then (2 : ℝ≥0∞)⁻¹ • dirac true else 0) s =
      if n = 0 then ((2 : ℝ≥0∞)⁻¹ • dirac true) s else 0 := by split_ifs <;> rfl
  simp_rw [h]
  simp

-- An annotated real-state loop exercises stock vcgen with quantitative assertions.
noncomputable def realLoop (x : ℝ) : Measure ℝ := rdo
  let mut y := x
  while true
    invariant _ => (1 : ℝ≥0∞)
  rdo
    y := y + 1
    break
  return y

example (x : ℝ) : Triple (realLoop x) 1 (fun _ => 1) estack⟨⟩ := by
  simp only [realLoop, mBind_mPure]
  vcgen
  all_goals first
    | fun_prop
    | exact ⟨1, by simp⟩
    | simp
  simpa using Measure.terminates_done (g := fun a : ℝ => a + 1) (by fun_prop) x

-- A well-founded variant works with the quantitative Measure interpretation.
noncomputable def countdown (n : ℕ) : Measure ℕ := rdo
  let mut remaining := n
  while remaining > 0
    invariant _ => (1 : ℝ≥0∞)
    decreasing remaining
  rdo
    remaining := remaining - 1
  return remaining

example (n : ℕ) : Triple (countdown n) 1 (fun _ => 1) estack⟨⟩ := by
  simp only [countdown, mBind_mPure]
  vcgen
  all_goals try fun_prop
  all_goals try (solve | simp_all)
  all_goals try exact measurable_fun_forInStep measurable_from_nat measurable_from_nat
  rename_i remaining bound h
  by_cases heq : remaining = bound
  · subst bound
    simp_all [Nat.sub_lt h Nat.zero_lt_one]
  · simp [heq]

end TestNext.WP.MeasureLoop
