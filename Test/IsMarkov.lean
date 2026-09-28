module

public import Test.Common

set_option linter.style.header false

/-!
# The `is_markov` tactic on `rdo` programs

`is_markov` walks an `rdo` program as a tree of constructs, applying a propagation lemma at each
node. There is one test here per construct it recognises.
-/

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

`is_markov` proves the measurability of a `while` loop, and hands back its termination: the loop is
a probability measure exactly when the mass of its runs still going after `n` steps tends to `0`.
Each test takes that as a hypothesis, which closes the only goal left. -/

noncomputable def untilHeads : Measure ℕ := rdo
  let mut n := 0
  while true rdo
    let heads ← fairCoin
    n := n + 1
    if heads then
      break
  return n

example (h : ∀ _ : Unit, Filter.Tendsto (fun k ↦ MeasurableSpaceMonad.loopRun (m := Measure)
    (fun n : ℕ ↦ fairCoin >>=ₘ fun heads ↦
      if heads then mPure (ForInStep.done (n + 1)) else mPure (ForInStep.yield (n + 1)))
    k 0 Set.univ) Filter.atTop (nhds 0)) :
    IsProbabilityMeasure untilHeads := by
  is_markov
  exact h

/-- A `while` loop whose condition reads the parameter. -/
noncomputable def climbFrom (k : ℕ) : Measure ℕ := rdo
  let mut n := k
  while n < k + 3 rdo
    let heads ← fairCoin
    if heads then
      n := n + 1
  return n

example (h : ∀ k, Filter.Tendsto (fun j ↦ MeasurableSpaceMonad.loopRun (m := Measure)
    (fun n : ℕ ↦ if n < k + 3 then
        fairCoin >>=ₘ fun heads ↦
          if heads then mPure (ForInStep.yield (n + 1)) else mPure (ForInStep.yield n)
      else mPure (ForInStep.done n)) j k Set.univ) Filter.atTop (nhds 0)) :
    IsMarkov climbFrom := by
  is_markov
  exact h

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
