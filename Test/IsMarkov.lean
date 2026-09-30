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
`RandomDo.Tactic.IsMarkov.While.Termination`. -/

noncomputable def untilHeads : Measure ℕ := rdo
  let mut n := 0
  while true rdo
    let heads ← fairCoin
    n := n + 1
    if heads then
      break
  return n

/-- The variant rule of McIver and Morgan, as stated by Majumdar and Sathiyanarayana: with the
invariant that always holds, the variant is `1` while the loop runs, `0` once it has stopped. -/
example : IsProbabilityMeasure untilHeads := by
  is_markov
  refine fun _ ↦ .majumdarSathiyanarayana_variantRule ⊤ (fun t ↦ if t.isDone then 0 else 1) 0 2
    (1 / 4) (by norm_num) trivial (fun t _ ↦ by split_ifs <;> simp)
    fun n _ ↦ ?_
  norm_num [fairCoin]

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
  refine fun k ↦ .majumdarSathiyanarayana_variantRule
    { running := (· ≤ k + 3), step := fun n (hn : n ≤ k + 3) ↦ ?_ }
    (fun t ↦ if t.isDone then 0 else (k : ℤ) + 4 - t.run) 0 (k + 5) (1 / 4) (by norm_num)
    (Nat.le_add_right k 3) (fun t ht ↦ by cases t <;> simp at ht ⊢ <;> omega)
    (fun n (hn : n ≤ k + 3) ↦ ?_)
  · rw [ae_iff]
    by_cases h : n < k + 3 <;> simp [h, hn.not_gt, fairCoin]
    omega
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
  refine fun k ↦ .majumdarSathiyanarayana_variantRule
    { running := (· ≤ k), step := fun i (hi : i ≤ k) ↦ ?_ }
    (fun t ↦ if t.isDone then 0 else (t.run : ℤ) + 1) 0 (k + 2) (1 / 2) (by norm_num) le_rfl
    (fun t ht ↦ by cases t <;> simp at ht ⊢ <;> omega)
    (fun i _ ↦ by by_cases h : 0 < i <;> norm_num [h])
  rw [ae_iff]
  by_cases h : 0 < i <;> simp [h]
  omega

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
  refine fun _ ↦ .majumdarSathiyanarayana_variantRule
    { running := fun p ↦ p.1 ≤ 2, step := fun p (hp : p.1 ≤ 2) ↦ ?_ }
    (fun t ↦ if t.isDone then 0 else 3 - (t.run.1 : ℤ)) 0 4 (1 / 4) (by norm_num) (by simp)
    (fun t ht ↦ by cases t <;> simp at ht ⊢; omega)
    (fun p (hp : p.1 ≤ 2) ↦ ?_)
  · rw [ae_iff]
    by_cases h : p.1 < 2 <;> simp [h, hp.not_gt, fairCoin]
  · by_cases h : p.1 < 2 <;> norm_num [h, fairCoin, show p.1 < 3 by omega]

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
