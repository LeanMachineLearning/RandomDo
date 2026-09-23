module

public import Test.IsMarkov
public meta import RandomDo
import Batteries.Data.Float.Basic

set_option linter.style.header false

/-!
# Polymorphic `rdo` programs

The programs of `Test.Computable`, written once over an arbitrary `MeasurableSpaceMonad` `m` and
drawing through `HasGaussian` and `HasBernoulli`. Read at `m := Measure`, each one is a probability
measure, checked by `is_markov`, and is the program of `Test.IsMarkov` when there is one. Run at
`m := RandM`, it samples.
-/

@[expose] public section

namespace Test.Polymorphic

open Test.IsMarkov NumLean Lean.Elab.Command MeasureTheory ProbabilityTheory

universe v

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {R V : Type} [Scalar R] [Scalar V]

def logPolymorphic {α : Type} [MeasurableSpace α] [Lean.ToMessageData α] (prog : RandM α) :
    CommandElabM Unit := do
  let x ← (IO.runRandPCG prog : IO α)
  let y ← (IO.runRandPCGWith 42 prog : IO α)
  Lean.logInfo m!"x = {x}"
  Lean.logInfo m!"y (seed 42) = {y}"

def sumTwo [HasGaussian m R V R] : m R := rdo
  let x ← HasGaussian.gaussian (m := m) (0 : R) (1 : V)
  let y ← HasGaussian.gaussian (m := m) (0 : R) (1 : V)
  return x + y

example : sumTwo (m := Measure) (R := ℝ) (V := NNReal) = Test.IsMarkov.sumTwo := rfl

run_cmd logPolymorphic (sumTwo (m := RandM) (R := Float) (V := Float))

def unfoldSumTwo [HasGaussian m R V R] : m R := rdo
  let y ← sumTwo (m := m) (V := V)
  let x ← HasGaussian.gaussian (m := m) (0 : R) (1 : V)
  return x + y

example : IsProbabilityMeasure (unfoldSumTwo (m := Measure) (R := ℝ) (V := NNReal)) := by
  is_markov

run_cmd logPolymorphic (unfoldSumTwo (m := RandM) (R := Float) (V := Float))

def centred [HasGaussian m R V R] (c : R) : m R := rdo
  let x ← HasGaussian.gaussian (m := m) c (1 : V)
  return x

example : centred (m := Measure) (R := ℝ) (V := NNReal) = Test.IsMarkov.centred := rfl

run_cmd logPolymorphic (centred (m := RandM) (R := Float) (V := Float) 20)

def branchOn [LT R] [DecidableLT R] [HasGaussian m R V R] (c : R) : m R := rdo
  if 0 < c then
    let x ← HasGaussian.gaussian (m := m) c (1 : V)
    return x
  else
    let x ← HasGaussian.gaussian (m := m) (0 : R) (1 : V)
    return x

example : branchOn (m := Measure) (R := ℝ) (V := NNReal) = Test.IsMarkov.branchOn := rfl

run_cmd logPolymorphic (branchOn (m := RandM) (R := Float) (V := Float) 20)

run_cmd logPolymorphic (branchOn (m := RandM) (R := Float) (V := Float) (-1))

def coin [HasBernoulli m R] (p : R) : m Bool := rdo
  let b ← HasBernoulli.bernoulli (m := m) p
  return b

example : IsProbabilityMeasure (coin (m := Measure) (1 / 2 : ℝ)) := by is_markov

run_cmd logPolymorphic (coin (m := RandM) (0.5 : Float))

/--
error: expected 0 ≤ p ≤ 1, got 2.000000
-/
#guard_msgs in
run_cmd logPolymorphic (coin (m := RandM) (2 : Float))

/--
error: expected 0 ≤ p ≤ 1, got -1.000000
-/
#guard_msgs in
run_cmd logPolymorphic (coin (m := RandM) (-1 : Float))

def twoCoins [HasBernoulli m R] (p : R) : m Bool := rdo
  let x ← coin (m := m) p
  let y ← coin (m := m) p
  return x && y

example : IsProbabilityMeasure (twoCoins (m := Measure) (1 / 2 : ℝ)) := by is_markov

run_cmd logPolymorphic (twoCoins (m := RandM) (0.5 : Float))

def ex1 [HasGaussian m R V R] : m R := rdo
  let mut x : R := 0
  for _ in List.range 1000 rdo
    let y ← HasGaussian.gaussian (m := m) (0 : R) (1 : V)
    x := x + y
  return x

example : IsProbabilityMeasure (ex1 (m := Measure) (R := ℝ) (V := NNReal)) := by is_markov

run_cmd logPolymorphic (ex1 (m := RandM) (R := Float) (V := Float))

end Test.Polymorphic

end
