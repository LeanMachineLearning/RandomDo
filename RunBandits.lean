/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Bandits.Defs

/-!
# Running the Gaussian bandit

`lake exe bandits [rounds] [seeds]` runs explore-then-commit, UCB and ε-greedy on a three-armed
Gaussian bandit, through the programs `banditStep` and `banditStepRand` of `Bandits.Defs` read at
`RandM` and `Float`, for many seeds, and writes the cumulative pseudo-regret in `bandit_output/`:

* `<algorithm>.csv`: for each round, the mean regret over the seeds, its standard error, and its
  10% and 90% quantiles;
* `<algorithm>_paths.csv`: the regret of the first few seeds, round by round, as the hexadecimal
  bits of each `Float`, for `scripts/bandit_plot.py` to replay them with numpy;
* `config.csv`: the parameters, for the same purpose.

It also checks that the one-shot program, `banditRun n` or `banditRunRand n`, lands on the state the
round-by-round run reaches after `n` rounds.
-/

open RDoBandit NumLean

/-- The number of arms. -/
def numArms : ℕ := 3

instance : NeZero numArms := ⟨by decide⟩

/-- The mean reward of each arm. -/
def means (a : Fin numArms) : Float := #[1.0, 0.5, 0.0][a.val]!

/-- The gap of each arm: how much is lost, in expectation, by pulling it rather than arm `0`. -/
def gap (a : Fin numArms) : Float := 1.0 - means a

/-- The variance of the rewards. -/
def variance : Float := 1.0

/-- A bandit algorithm to run. -/
structure Algo where
  /-- Its name, which names its files. -/
  name : String
  /-- One round, at `RandM` and `Float`. -/
  step : ℕ → State numArms Float → RandPCG IO (State numArms Float)
  /-- The one-shot program: `n` rounds from the initial state. -/
  oneShot : ℕ → RandPCG IO (State numArms Float)

/-- An algorithm choosing its arm deterministically from the state, run by `banditStep`. -/
def Algo.det (name : String) (arm : ℕ → State numArms Float → Fin numArms) : Algo where
  name := name
  step n s := (banditStep (m := RandM) (R := Float) (V := Float) arm means variance n s : RandM _)
  oneShot n := (banditRun (m := RandM) (R := Float) (V := Float) arm means variance n : RandM _)

/-- An algorithm drawing its arm, run by `banditStepRand`. -/
def Algo.rand (name : String) (arm : ℕ → State numArms Float → RandM (Fin numArms)) : Algo where
  name := name
  step n s :=
    (banditStepRand (m := RandM) (R := Float) (V := Float) arm means variance n s : RandM _)
  oneShot n :=
    (banditRunRand (m := RandM) (R := Float) (V := Float) arm means variance n : RandM _)

/-- `T` rounds, recording the cumulative pseudo-regret after each. -/
def Algo.run (alg : Algo) (T : ℕ) : RandPCG IO (Array Float × State numArms Float) := do
  let mut s := State.init
  let mut regret := 0.0
  let mut curve := Array.mkEmpty T
  for n in [0:T] do
    s ← alg.step n s
    regret := regret + gap s.2.2
    curve := curve.push regret
  return (curve, s)

/-- The bits of a `Float`, in hexadecimal: they are read back exactly. -/
def hexBits (x : Float) : String := String.ofList (Nat.toDigits 16 x.toBits.toNat)

/-- The `q`-quantile of a sorted array, by the nearest-rank method. -/
def quantile (xs : Array Float) (q : Float) : Float :=
  xs[(q * (xs.size - 1).toFloat).round.toUInt64.toNat]!

/-- Whether two states are the same, bit for bit. -/
def sameState (s t : State numArms Float) : Bool :=
  (List.finRange numArms).all fun a ↦
    s.1[a] == t.1[a] && s.2.1[a].toBits == t.2.1[a].toBits && s.2.2 == t.2.2

/-- Run `alg` for `T` rounds on each of `reps` seeds, write its files, and check the one-shot
program on the first seed. -/
def Algo.go (alg : Algo) (T reps : ℕ) (maxPaths : ℕ := 5) : IO Bool := do
  let paths := min maxPaths reps
  let mut curves : Array (Array Float) := #[]
  for r in [0:reps] do
    let (c, _) ← (IO.runRandPCGWith (r + 1) (alg.run T) : IO _)
    curves := curves.push c
  IO.FS.withFile s!"bandit_output/{alg.name}.csv" .write fun h ↦ do
    h.putStrLn "round,mean,se,q10,q90"
    for n in [0:T] do
      let xs := (curves.map (·[n]!)).qsort (· < ·)
      let mean := xs.foldl (· + ·) 0 / reps.toFloat
      let var := xs.foldl (fun acc x ↦ acc + (x - mean) * (x - mean)) 0 / (reps - 1).toFloat
      h.putStrLn s!"{n + 1},{mean},{(var / reps.toFloat).sqrt},{quantile xs 0.1},{quantile xs 0.9}"
  IO.FS.withFile s!"bandit_output/{alg.name}_paths.csv" .write fun h ↦ do
    h.putStrLn ("round," ++ ",".intercalate ((List.range paths).map (s!"seed{· + 1}")))
    for n in [0:T] do
      h.putStrLn (s!"{n + 1}," ++ ",".intercalate
        ((List.range paths).map fun r ↦ hexBits (curves[r]!)[n]!))
  -- The one-shot program, on the first seed: the same draws, in the same order.
  let nCheck := min 500 T
  let (_, sDriver) ← (IO.runRandPCGWith 1 (alg.run nCheck) : IO _)
  let sOneShot ← (IO.runRandPCGWith 1 (alg.oneShot nCheck) : IO (State numArms Float))
  let ok := sameState sDriver sOneShot
  let final := curves.map (·.back!)
  IO.println s!"{alg.name}: {reps} seeds × {T} rounds, mean final regret \
    {final.foldl (· + ·) 0 / reps.toFloat}; one-shot {nCheck} = {nCheck} steps: {ok}"
  return ok

/-- `lake exe bandits [rounds] [seeds]`, by default 5000 rounds and 300 seeds. -/
def main (args : List String) : IO UInt32 := do
  IO.FS.createDirAll "bandit_output"
  let T := (args[0]?.bind String.toNat?).getD 5000
  let reps := (args[1]?.bind String.toNat?).getD 300
  let algos : List (Algo × String) := [
    (.det "etc_m10" (etcArm 10), "etc,10"),
    (.det "etc_m50" (etcArm 50), "etc,50"),
    (.det "ucb_c3" (ucbArm 3), "ucb,3"),
    (.rand "epsgreedy_0.1" (epsGreedyArm (m := RandM) 0.1), "epsgreedy,0.1")]
  IO.FS.withFile "bandit_output/config.csv" .write fun h ↦ do
    h.putStrLn "name,algorithm,parameter,rounds,seeds,means,variance"
    for (alg, desc) in algos do
      h.putStrLn s!"{alg.name},{desc},{T},{reps},1.0;0.5;0.0,{variance}"
  let mut ok := true
  for (alg, _) in algos do
    ok := (← alg.go T reps) && ok
  IO.println (if ok then "all checks passed" else "SOME CHECKS FAILED")
  return if ok then 0 else 1
