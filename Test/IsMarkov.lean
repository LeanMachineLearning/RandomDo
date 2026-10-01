module

public import Test.Common

set_option linter.style.header false

/-!
# The `is_markov` tactic on `rdo` programs

`is_markov` walks an `rdo` program as a tree of constructs, applying a propagation lemma at each
node. There is one test here per construct it recognises.
-/

open scoped ENNReal
open MeasureTheory ProbabilityTheory MeasurableSpacePure

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
goal `Terminates`. Each test closes it with `terminates`, which applies a proof rule of the
literature from `RandomDo.Tactic.IsMarkov.While.Termination`. -/

noncomputable def untilHeads : Measure ℕ := rdo
  let mut n := 0
  while true rdo
    let heads ← fairCoin
    n := n + 1
    if heads then
      break
  return n

/-- Immediate escape: every step stops with probability `1 / 2`. -/
example : IsProbabilityMeasure untilHeads := by
  is_markov
  terminates (prob := 1 / 2) [fairCoin]

/-- A `while` loop whose condition reads the parameter. -/
noncomputable def climbFrom (k : ℕ) : Measure ℕ := rdo
  let mut n := k
  while n < k + 3 rdo
    let heads ← fairCoin
    if heads then
      n := n + 1
  return n

/-- The variant rule: below the invariant bound `k + 3`, the variant `k + 3 - n` decreases with
probability `1 / 2`. -/
example : IsMarkov climbFrom := by
  is_markov
  intro k
  terminates (invariant := (· ≤ k + 3)) (variant := (k + 3 - ·)) (bound := k + 3) (prob := 1 / 2)
    [fairCoin]

/-- A deterministic countdown, whose counter is bounded only by its initial value. -/
noncomputable def countdown (k : ℕ) : Measure ℕ := rdo
  let mut i := k
  while 0 < i rdo
    i := i - 1
  return i

/-- The variant rule: below the invariant bound `k`, the counter decreases at every step. -/
example : IsMarkov countdown := by
  is_markov
  intro k
  terminates (invariant := (· ≤ k)) (variant := id) (bound := k) (prob := 1)

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

/-- The variant rule, on the pairs `(heads, flips)`: below the invariant bound `2` on the heads, the
variant `2 - heads` decreases with probability `1 / 2`. -/
example : IsProbabilityMeasure untilTwoHeads := by
  is_markov
  terminates (invariant := fun p ↦ p.1 ≤ 2) (variant := fun p ↦ 2 - p.1) (bound := 2)
    (prob := 1 / 2) [fairCoin]

/-- The flips of a coin of bias `p` until heads. -/
noncomputable def geometric (p : unitInterval) : Measure ℕ := rdo
  let mut n := 0
  while true rdo
    let b ← bernoulliMeasure true false p
    n := n + 1
    if b then
      break
  return n

/-- Immediate escape, with a symbolic probability. -/
example (p : unitInterval) (hp : 0 < (p : ℝ)) : IsProbabilityMeasure (geometric p) := by
  is_markov
  terminates (prob := p)

/-- The gambler's ruin: a fair random walk stopped at `0` and at `N`. -/
noncomputable def ruin (N x : ℕ) : Measure ℕ := rdo
  let mut y := x
  while 0 < y ∧ y < N rdo
    let b ← fairCoin
    if b then
      y := y + 1
    else
      y := y - 1
  return y

/-- The variant rule, with the distance to the nearest barrier as the variant. -/
example (N : ℕ) : IsMarkov (ruin N) := by
  is_markov
  terminates (variant := fun y ↦ min y (N - y)) (bound := N) (prob := 1 / 2) [fairCoin]

/-- A die by rejection: three flips give a number below `8`, kept if it is below `6`. -/
noncomputable def die : Measure ℕ := rdo
  let mut r := 6
  while 6 ≤ r rdo
    let a ← fairCoin
    let b ← fairCoin
    let c ← fairCoin
    r := (if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0)
  return r

/-- The variant rule, with the variant `1` on the rejected numbers: a step keeps the number it draws
with probability `3 / 4`. -/
example : IsProbabilityMeasure die := by
  is_markov
  terminates (variant := fun r ↦ if 6 ≤ r then 1 else 0) (bound := 1) (prob := 3 / 4) [fairCoin]

/-- A Gaussian random walk, stopped once it leaves `(-1, 1)`. -/
noncomputable def gaussianWalk (x : ℝ) : Measure ℝ := rdo
  let mut y := x
  while |y| < 1 rdo
    let z ← gaussianReal 0 1
    y := y + z
  return y

/-- The variant rule, with the variant `1` inside `(-1, 1)`: a step leaves it with probability at
least `P(Z ≥ 2)`. The goals left are about the Gaussian distribution only. -/
example : IsMarkov gaussianWalk := by
  is_markov
  intro x
  terminates (variant := fun y ↦ if |y| < 1 then 1 else 0) (bound := 1)
    (prob := (gaussianReal 0 1 (Set.Ici 2)).toReal)
  · -- From `|s| < 1`, a step of at least `2` leaves `(-1, 1)`.
    rename_i h
    refine measure_mono fun a (ha : 2 ≤ a) ↦ ?_
    have := (abs_lt.1 h).1
    simp [show ¬|s + a| < 1 from fun h' ↦ by linarith [(abs_lt.1 h').2]]
  · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp [prob_le_one])
  · refine ENNReal.toReal_pos (fun h ↦ ?_) (measure_ne_top _ _)
    simpa using gaussianReal_absolutelyContinuous' 0 one_ne_zero h
  · exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const
      measurable_const

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
