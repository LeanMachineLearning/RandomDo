module

public import Test.IsMarkov
public meta import RandomDo
import Batteries.Data.Float.Basic

set_option linter.style.header false

/-!
# Polymorphic `rdo` programs

The programs of `Test.Computable`, written once over an arbitrary `MeasurableSpaceMonad` `m` and
drawing through `HasGaussian`, `HasUniform` and `HasBernoulli`. Read at `m := Measure`, each one is
a probability measure, checked by `is_markov`, and is the program of `Test.IsMarkov` when there is
one. Run at `m := RandM`, it samples.
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

def uniformDraw [HasUniform m R] (low high : R) : m R := rdo
  let x ← HasUniform.uniform (m := m) low high
  return x

example (low high : ℝ) [Fact (low ≤ high)] :
    IsProbabilityMeasure (uniformDraw (m := Measure) low high) := by is_markov

example : IsProbabilityMeasure (uniformDraw (m := Measure) (0 : ℝ) 1) := by is_markov

-- A proper subinterval has its relative length as probability, even on a non-unit interval.
example : (HasUniform.uniform (m := Measure) (2 : ℝ) 6 (Set.Ico 2 4)).toReal = 1 / 2 := by
  norm_num [HasUniform.uniform, cond_apply measurableSet_Ico, Set.Ico_inter_Ico, Real.volume_Ico]

-- Equal bounds give a point mass, not the zero measure of an empty half-open interval.
example (x : ℝ) : HasUniform.uniform (m := Measure) x x = Measure.dirac x := by
  simp [HasUniform.uniform]

example (low high : ℝ) (h : high < low) :
    HasUniform.uniform (m := Measure) low high = 0 := by
  simp [HasUniform.uniform, ne_of_gt h, Set.Ico_eq_empty_of_le h.le]

run_cmd do
  let x ← (IO.runRandPCGWith 42 (uniformDraw (m := RandM) (-2 : Float) 3) : IO Float)
  unless (-2 : Float) ≤ x ∧ x < 3 do
    throwError "uniform sample outside its bounds: {x}"
  let x ← (IO.runRandPCGWith 42 (uniformDraw (m := RandM) (7 : Float) 7) : IO Float)
  unless x == 7 do
    throwError "uniform sample with equal bounds: expected 7, got {x}"

/--
error: low > high
-/
#guard_msgs in
run_cmd logPolymorphic (uniformDraw (m := RandM) (2 : Float) 1)

def coin [HasBernoulli m R] (p : R) : m Bool := rdo
  let b ← HasBernoulli.bernoulli (m := m) p
  return b

example : IsProbabilityMeasure (coin (m := Measure) (1 / 2 : ℝ)) := by is_markov

run_cmd logPolymorphic (coin (m := RandM) (0.5 : Float))

example : HasBernoulli.bernoulli (m := Measure) (-1 : ℝ) = Measure.dirac false := by
  norm_num [HasBernoulli.bernoulli, Set.projIcc]

example : HasBernoulli.bernoulli (m := Measure) (2 : ℝ) = Measure.dirac true := by
  norm_num [HasBernoulli.bernoulli, Set.projIcc]

-- The polymorphic sampler clamps to the endpoints, including infinite inputs.
run_cmd do
  for (p, expected) in ([(-1, false), (0, false), (1, true), (2, true),
      (-(1 / 0), false), (1 / 0, true)] : List (Float × Bool)) do
    let actual ← (IO.runRandPCGWith 42 (coin (m := RandM) p) : IO Bool)
    unless actual == expected do
      throwError "clamped Bernoulli with p = {p}: expected {expected}, got {actual}"

-- Valid probabilities preserve the NumLean sampler's seeded sequence.
run_cmd do
  for p in ([0, 0.2, 0.5, 0.8, 1] : List Float) do
    let actual ← (IO.runRandPCGWith 42
      ((List.range 20).mapM fun _ => coin (m := RandM) p) : IO (List Bool))
    let expected ← (IO.runRandPCGWith 42
      ((List.range 20).mapM fun _ => NumLean.bernoulli p) : IO (List Nat))
    unless actual == expected.map (· == 1) do
      throwError "Bernoulli sequence changed for p = {p}"

/--
error: expected 0 ≤ p ≤ 1, got NaN
-/
#guard_msgs in
run_cmd logPolymorphic (coin (m := RandM) (0 / 0 : Float))

-- The underlying NumLean sampler retains NumPy's strict validation.
/--
error: expected 0 ≤ p ≤ 1, got 2.000000
-/
#guard_msgs in
run_cmd logPolymorphic (NumLean.bernoulli 2)

/--
error: expected 0 ≤ p ≤ 1, got -1.000000
-/
#guard_msgs in
run_cmd logPolymorphic (NumLean.bernoulli (-1))

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
