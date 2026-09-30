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

/-- The variant rule of McIver and Morgan (Lemma 2.7.1) on the loop `while n < k + 3 do body`: the
states where the loop runs are finitely many, so the variant `k + 3 - n` needs no bounds. -/
example : IsMarkov climbFrom := by
  is_markov
  intro k
  convert Terminates.mcIverMorgan_variantRule_of_finite (G := (· < k + 3)) (Inv := (k ≤ ·))
    (body := fun n ↦ fairCoin >>=ₘ fun heads ↦ if heads then mPure (n + 1) else mPure n)
    (fun n ↦ (k : ℤ) + 3 - n) (1 / 2) (by norm_num) (by norm_num)
    (fun h ↦ absurd ((Set.finite_Ico k (k + 3)).subset fun s hs ↦ ⟨hs.2, hs.1⟩) h)
    (fun s _ hs ↦ ?_) (fun N s _ _ hN ↦ ?_) le_rfl using 1
  · funext n
    by_cases h : n < k + 3 <;> simp [whileStep, h, fairCoin, Measure.map_add, Measure.map_smul,
      ForInStep.measurable_yield]
  · norm_num [fairCoin, hs, show k ≤ s + 1 by omega]
  · subst hN
    norm_num [fairCoin]

/-- A deterministic countdown, whose counter is bounded only by its initial value. -/
noncomputable def countdown (k : ℕ) : Measure ℕ := rdo
  let mut i := k
  while 0 < i rdo
    i := i - 1
  return i

/-- The variant rule of McIver and Morgan with a variant that cannot increase (p. 56): the counter
itself. -/
example : IsMarkov countdown := by
  is_markov
  intro k
  convert Terminates.mcIverMorgan_variantRule_of_antitone (b := k) (G := fun i : ℕ ↦ 0 < i)
    (Inv := fun _ ↦ True) (body := fun i ↦ (mPure (i - 1) : Measure ℕ)) (fun i ↦ (i : ℤ)) 0 1
    one_pos (fun _ _ _ ↦ by positivity) (fun _ _ _ ↦ by simp) (fun N i hi _ hN ↦ ?_)
    (fun N i hi _ hN ↦ ?_) trivial using 1
  · funext i
    by_cases h : 0 < i <;> simp [whileStep, h, ForInStep.measurable_yield]
  · subst hN
    simp [hi]
  · subst hN
    simp

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

/-- The variant rule of McIver and Morgan (Lemma 7.5.1), with the variant `2 - heads` between `1`
and `3`. -/
example : IsProbabilityMeasure untilTwoHeads := by
  is_markov
  intro _
  convert Terminates.mcIverMorgan_variantRule (b := (0, 0)) (G := fun p : ℕ × ℕ ↦ p.1 < 2)
    (Inv := fun _ ↦ True) (body := fun p ↦ fairCoin >>=ₘ fun b ↦
      if b then mPure (p.1 + 1, p.2 + 1) else mPure (p.1, p.2 + 1))
    (fun p ↦ 2 - (p.1 : ℤ)) 1 3 (1 / 2) (by norm_num) (fun p hp _ ↦ by omega)
    (fun _ _ _ ↦ by norm_num [fairCoin]) (fun N p hp _ hN ↦ ?_) trivial using 1
  · funext p
    by_cases h : p.1 < 2 <;> simp [whileStep, h, fairCoin, Measure.map_add, Measure.map_smul,
      ForInStep.measurable_yield]
  · subst hN
    norm_num [fairCoin]

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
      bernoulliMeasure_bind', Nat.ofNat_pos, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat,
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

/-- The new variant rule of McIver, Morgan, Kaminski and Katoen, with the super-martingale `|y|`,
which decreases by `1` with probability `1 / 2`. -/
example : IsMarkov randomWalk := by
  is_markov
  intro x
  -- Away from `0`, one of `y + 1` and `y - 1` is one closer to `0`, the other one further.
  have habs : ∀ y : ℤ, y ≠ 0 →
      (|(y : ℝ) + 1| = |(y : ℝ)| + 1 ∧ |(y : ℝ) - 1| = |(y : ℝ)| - 1) ∨
      (|(y : ℝ) + 1| = |(y : ℝ)| - 1 ∧ |(y : ℝ) - 1| = |(y : ℝ)| + 1) := by
    intro y hy
    rcases lt_or_gt_of_ne hy with h | h
    · have : (y : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
      right
      rw [abs_of_nonpos (show (y : ℝ) + 1 ≤ 0 by linarith),
        abs_of_neg (show (y : ℝ) - 1 < 0 by linarith), abs_of_neg (show (y : ℝ) < 0 by linarith)]
      constructor <;> ring
    · have : (1 : ℝ) ≤ y := by exact_mod_cast h
      left
      rw [abs_of_pos (show (0 : ℝ) < y + 1 by linarith),
        abs_of_nonneg (show (0 : ℝ) ≤ y - 1 by linarith), abs_of_pos (show (0 : ℝ) < y by linarith)]
      constructor <;> ring
  -- `max (a, 0)` is at most the mean of `max (a - 1, 0)` and `max (a + 1, 0)`.
  have hconv : ∀ a : ℝ, ENNReal.ofReal a ≤
      ENNReal.ofReal (1 / 2) * ENNReal.ofReal (a - 1) +
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (a + 1) := by
    intro a
    rcases le_or_gt a 1 with h | h
    · calc ENNReal.ofReal a ≤ ENNReal.ofReal (1 / 2 * (a + 1)) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (a + 1) := ENNReal.ofReal_mul (by norm_num)
        _ ≤ _ := le_add_self
    · rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  convert Terminates.mcIverMorganKaminskiKatoen (b := x) (G := fun y : ℤ ↦ y ≠ 0)
    (I := fun _ ↦ True) (body := fun y ↦ fairCoin >>=ₘ fun b ↦
      if b then mPure (y + 1) else mPure (y - 1))
    (fun y ↦ |(y : ℝ)|) (fun _ ↦ abs_nonneg _) (fun _ ↦ 1 / 2) (fun _ ↦ 1)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ one_pos) antitoneOn_const antitoneOn_const
    (fun _ _ _ ↦ by norm_num [fairCoin]) (fun y hy _ ↦ by positivity)
    (fun R _ y hy _ hR ↦ ?_) (fun H _ y hy _ ↦ ?_) trivial using 1
  · funext y
    by_cases h : y = 0 <;> simp [whileStep, h, fairCoin, Measure.map_add, Measure.map_smul,
      ForInStep.measurable_yield]
  · -- The step towards `0` has probability `1 / 2`.
    subst hR
    have : ¬|(y : ℝ)| + 1 ≤ |(y : ℝ)| - 1 := by linarith
    rcases habs y hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> norm_num [fairCoin, h1, h2, this]
  · -- `H ⊖ |y|` is a submartingale away from `0`.
    norm_num [fairCoin]
    rcases habs y hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      simpa [sub_sub, sub_add] using hconv (H - |(y : ℝ)|)
    · rw [h1, h2, add_comm]
      simpa [sub_sub, sub_add] using hconv (H - |(y : ℝ)|)

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
