module

public import Test.Common

set_option linter.style.header false

/-!
# The `is_markov` tactic on `rdo` programs

`is_markov` walks an `rdo` program as a tree of constructs, applying a propagation lemma at each
node. There is one test here per construct it recognises.
-/

open scoped ENNReal
open MeasureTheory ProbabilityTheory MeasurableSpacePure MeasurableSpaceMonadWhile

@[expose] public section

namespace Test.IsMarkov

/-! ## `return` -/

noncomputable def shiftBy (c : ℝ) : Measure ℝ := rdo
  return c + 1

example : IsMarkov shiftBy := by is_markov

/-! ## `let x ← _` -/

noncomputable def sumTwo : Measure ℝ := rdo
  let x ← gaussianReal 0 1
  let y ← gaussianReal 0 1
  return x + y

example : IsProbabilityMeasure sumTwo := by is_markov

/-- A distribution whose parameter is read off the argument. -/
noncomputable def centred (c : ℝ) : Measure ℝ := rdo
  let x ← gaussianReal c 1
  return x

example : IsMarkov centred := by is_markov

/-! ## Reparametrisation -/

example {κ : ℝ → Measure ℝ} [IsMarkov κ] : IsMarkov fun c ↦ κ (c + 1) := by is_markov

/-! ## A constant family -/

example (μ : Measure ℝ) [IsProbabilityMeasure μ] : IsMarkov fun _ : ℝ ↦ μ := by is_markov

/-! ## `if … then … else` between two families -/

noncomputable def branchOn (c : ℝ) : Measure ℝ := rdo
  if 0 < c then
    let x ← gaussianReal c 1
    return x
  else
    let x ← gaussianReal 0 1
    return x

example : IsMarkov branchOn := by is_markov

/-! ## `for` over a fixed collection -/

noncomputable def sumLoop : Measure ℝ := rdo
  let mut s : ℝ := 0
  for _ in List.range 3 rdo
    let x ← gaussianReal 0 1
    s := s + x
  return s

example : IsProbabilityMeasure sumLoop := by is_markov

/-! ## `for` with an early `return`, which goes through `Break.runK` -/

noncomputable def firstPositive : Measure ℝ := rdo
  for _ in List.range 3 rdo
    let x ← gaussianReal 0 1
    if 0 < x then
      return x
  return 0

example : IsProbabilityMeasure firstPositive := by is_markov

/-! ## `for` over a collection read off the argument -/

noncomputable def overList (xs : List ℝ) : Measure ℝ := rdo
  let mut s : ℝ := 0
  for x in xs rdo
    let z ← gaussianReal (s + x) 1
    s := z
  return s

example : IsMarkov overList := by is_markov

/-! ## `while`, whose termination is handed back

`is_markov` proves that a `while` loop is Markovian up to its termination, which it hands back as a
goal `Terminates`. Each test closes it with a proof rule of the literature, from
`RandomDo.Tactic.IsMarkov.Termination`. -/

noncomputable def untilHeads : Measure ℕ := rdo
  let mut n := 0
  while true rdo
    let heads ← fairCoin
    n := n + 1
    if heads then
      break
  return n

/-- The variant rule of McIver and Morgan, as stated by Majumdar and Sathiyanarayana: the variant is
`1` while the loop runs, `0` once it has stopped. -/
example : IsProbabilityMeasure untilHeads := by
  is_markov
  refine fun _ ↦ .majumdarSathiyanarayana_variantRule (fun _ ↦ True)
    (fun t ↦ if t.isDone then 0 else 1) 0 2 (1 / 4) (by norm_num) trivial
    (fun _ _ ↦ Filter.Eventually.of_forall fun _ ↦ trivial) (fun t _ ↦ by split_ifs <;> simp)
    (fun _ _ ↦ by simp) fun n _ ↦ ?_
  norm_num [fairCoin]

/-- The Lyapunov ranking function of Bournez and Garnier, `2` while the loop runs: the loop also
takes at most `2` steps in expectation. -/
example : IsProbabilityMeasure untilHeads := by
  is_markov
  exact fun _ ↦ (bournezGarnier (fun t ↦ if t.isDone then 0 else 2) 1 one_pos fun n ↦ by
    norm_num [fairCoin, ENNReal.ofReal_div_of_pos, ENNReal.inv_mul_cancel]).1

/-- A `while` loop whose condition reads the parameter. -/
noncomputable def climbFrom (k : ℕ) : Measure ℕ := rdo
  let mut n := k
  while n < k + 3 rdo
    let heads ← fairCoin
    if heads then
      n := n + 1
  return n

/-- The variant rule of McIver and Morgan, as stated by Majumdar and Sathiyanarayana: below the
invariant bound `k + 3`, the variant is `k + 4 - n` while the loop runs. -/
example : IsMarkov climbFrom := by
  is_markov
  refine fun k ↦ .majumdarSathiyanarayana_variantRule (fun t ↦ t.run ≤ k + 3)
    (fun t ↦ if t.isDone then 0 else (k : ℤ) + 4 - t.run) 0 (k + 5) (1 / 4) (by norm_num)
    (by simp) (fun n (hn : n ≤ k + 3) ↦ ?_) (fun t ht ↦ by split_ifs <;> omega)
    (fun _ _ ↦ by simp) (fun n (hn : n ≤ k + 3) ↦ ?_)
  · rw [ae_iff]
    by_cases h : n < k + 3 <;> simp [h, hn.not_gt, fairCoin]
  · by_cases h : n < k + 3 <;> norm_num [h, fairCoin, show (n : ℤ) < k + 4 by omega]

/-- A deterministic countdown, whose counter is bounded only by its initial value. -/
noncomputable def countdown (k : ℕ) : Measure ℕ := rdo
  let mut i := k
  while 0 < i rdo
    i := i - 1
  return i

/-- The variant rule of McIver and Morgan, as stated by Majumdar and Sathiyanarayana: below the
invariant bound `k`, the variant is the counter plus one while the loop runs. -/
example : IsMarkov countdown := by
  is_markov
  refine fun k ↦ .majumdarSathiyanarayana_variantRule (fun t ↦ t.run ≤ k)
    (fun t ↦ if t.isDone then 0 else (t.run : ℤ) + 1) 0 (k + 2) (1 / 2) (by norm_num) le_rfl
    (fun i (hi : i ≤ k) ↦ ?_) (fun t ht ↦ by split_ifs <;> omega) (fun _ _ ↦ by simp)
    (fun i _ ↦ by by_cases h : 0 < i <;> norm_num [h])
  rw [ae_iff]
  by_cases h : 0 < i <;> simp [h, hi.not_gt, show ¬k < i - 1 by omega]

/-- A `while` loop over two mutable variables: the flips until two heads. -/
noncomputable def untilTwoHeads : Measure ℕ := rdo
  let mut heads := 0
  let mut flips := 0
  while heads < 2 rdo
    let b ← fairCoin
    flips := flips + 1
    if b then
      heads := heads + 1
  return flips

/-- The variant rule of McIver and Morgan, as stated by Majumdar and Sathiyanarayana: below the
invariant bound `2` on the heads, the variant is `3 - heads` while the loop runs. -/
example : IsProbabilityMeasure untilTwoHeads := by
  is_markov
  refine fun _ ↦ .majumdarSathiyanarayana_variantRule (fun t ↦ t.run.1 ≤ 2)
    (fun t ↦ if t.isDone then 0 else 3 - (t.run.1 : ℤ)) 0 4 (1 / 4) (by norm_num) (by simp)
    (fun p (hp : p.1 ≤ 2) ↦ ?_) (fun t ht ↦ by split_ifs <;> omega) (fun _ _ ↦ by simp)
    (fun p (hp : p.1 ≤ 2) ↦ ?_)
  · rw [ae_iff]
    by_cases h : p.1 < 2 <;> simp [h, hp.not_gt, fairCoin]
  · by_cases h : p.1 < 2 <;> norm_num [h, fairCoin, show p.1 < 3 by omega]

/-- The symmetric random walk on the integers, stopped at `0`: it stops almost surely, but after an
infinite expected number of steps, and no bounded variant proves it. -/
noncomputable def randomWalk (x : ℤ) : Measure ℤ := rdo
  let mut y := x
  while y ≠ 0 rdo
    let b ← fairCoin
    if b then
      y := y + 1
    else
      y := y - 1
  return y

/-- The martingale rule of Majumdar and Sathiyanarayana, with `|y| + 1` as both the supermartingale
and the variant. -/
example : IsMarkov randomWalk := by
  is_markov
  refine fun _ ↦ .majumdarSathiyanarayana_martingaleRule (fun _ ↦ True)
    (fun t ↦ if t.isDone then 0 else (t.run.natAbs : ℝ) + 1)
    (fun t ↦ if t.isDone then 0 else t.run.natAbs + 1) trivial
    (fun _ _ ↦ Filter.Eventually.of_forall fun _ ↦ trivial) (fun _ _ ↦ by simp)
    (fun _ _ ↦ by simp only [ForInStep.isDone_yield, Bool.false_eq_true, ↓reduceIte]; positivity)
    (fun y _ ↦ ?_) (fun _ _ ↦ by simp)
    (fun r ↦ ⟨⌈r⌉₊, fun t _ ht ↦ ?_⟩) (fun r ↦ ⟨1 / 4, by norm_num, fun y _ _ ↦ ?_⟩)
  · -- `|y| + 1` is a martingale away from `0`: `|y + 1| + |y - 1| = 2 |y|`.
    by_cases hy : y = 0
    · simp [hy]
    have habs : |(y : ℝ) + 1| + |(y : ℝ) - 1| = 2 * |(y : ℝ)| := by
      rcases lt_or_gt_of_ne hy with h | h
      · have : (y : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
        rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
        ring
      · have : (1 : ℝ) ≤ y := by exact_mod_cast h
        rw [abs_of_pos (by linarith), abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
        ring
    have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    simp only [ne_eq, hy, not_false_eq_true, ↓reduceIte, fairCoin, one_div, mPure_def, mBind_def,
      bernoulliMeasure_bind, Nat.ofNat_pos, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat,
      Bool.false_eq_true, Nat.cast_natAbs, Int.cast_abs, lintegral_add_measure,
      lintegral_smul_measure, lintegral_dirac, ForInStep.isDone_yield, ForInStep.run_yield,
      Int.cast_add, Int.cast_one, smul_eq_mul, Int.cast_sub]
    rw [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, h2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · cases t with
    | done _ => simp
    | yield y =>
      simp only [ForInStep.isDone_yield, Bool.false_eq_true, ite_false, ForInStep.run_yield] at ht ⊢
      exact_mod_cast (show ((y.natAbs + 1 : ℕ) : ℝ) ≤ r by exact_mod_cast ht).trans (Nat.le_ceil r)
  · -- The step towards `0` has probability `1 / 2`.
    by_cases hy : y = 0
    · norm_num [hy]
    rcases lt_or_gt_of_ne hy with h | h
    · have h1 : (y + 1).natAbs < y.natAbs := by omega
      have h2 : ¬(y - 1).natAbs < y.natAbs := by omega
      norm_num [hy, fairCoin, h1, h2]
    · have h1 : ¬(y + 1).natAbs < y.natAbs := by omega
      have h2 : (y - 1).natAbs < y.natAbs := by omega
      norm_num [hy, fairCoin, h1, h2]

/-! ## Looking through definitions, and the `fuel` argument -/

noncomputable def layerOne : Measure ℝ := sumTwo

noncomputable def layerTwo : Measure ℝ := layerOne

example : IsProbabilityMeasure layerTwo := by is_markov

example : IsProbabilityMeasure layerTwo := by is_markov (fuel := 3)

/-! ## The resulting instance is a `Kernel` -/

instance : IsMarkov centred := by is_markov

noncomputable example : Kernel ℝ ℝ := IsMarkov.toKernel centred

example : IsMarkovKernel (IsMarkov.toKernel centred) := inferInstance

end Test.IsMarkov

end
