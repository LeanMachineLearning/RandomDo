/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import MetropolisHastings.Targets

/-!
# Running random-walk Metropolis–Hastings

`lake exe mh` runs the chain on the targets of `MetropolisHastings.Targets`, through both routes
from the theory to a sampler: the program `@[computable]` wrote, and the polymorphic program run at
`RandM`. Seeded alike, the two draw the same numbers in the same order, so they must produce the
same trajectory, bit for bit; the executable checks it, and that the one-shot chains
`mhChainComputable` and `mhChainPoly` land on the last state of that trajectory.

It writes, in `mh_output/`:
* `<run>.csv`: the trajectory of each run, each state as the hexadecimal bits of its `Float`, one
  column per route;
* `runs.csv`: the parameters of each run, for `scripts/mh_plot.py` to replay them with numpy;
* `acceptance.csv`: the acceptance rate against the proposal standard deviation, for both targets.
-/

open MetropolisHastings NumLean

/-- A run of the chain. -/
structure Run where
  /-- The name of the run, which names its file. -/
  name : String
  /-- The name of the target. -/
  target : String
  /-- The log-density, as `@[computable]` translated it. -/
  logπA : Float → Float
  /-- The log-density, polymorphic, read at `Float`. -/
  logπB : Float → Float
  /-- The proposal variance. -/
  var : Float
  /-- The number of steps. -/
  steps : Nat
  /-- The initial state. -/
  x₀ : Float := 0
  /-- The seed of the generator. -/
  seed : Nat := 42

/-- One step of the chain, through the `@[computable]` route. -/
def Run.stepA (r : Run) (x : Float) : RandPCG IO Float := mhStepComputable r.logπA r.var x

/-- One step of the chain, through the polymorphic route. -/
def Run.stepB (r : Run) (x : Float) : RandPCG IO Float :=
  (mhStepPoly (m := RandM) (R := Float) (V := Float) r.logπB r.var x : RandM Float)

/-- The whole trajectory of `n` steps of a chain from `x₀`, one state per step. -/
def trajectory (step : Float → RandPCG IO Float) (n : Nat) (x₀ : Float) :
    RandPCG IO (Array Float) := do
  let mut x := x₀
  let mut xs := #[x₀]
  for _ in [0:n] do
    x ← step x
    xs := xs.push x
  return xs

/-- The fraction of steps that moved: a proposal is almost surely not the current state, so this is
the fraction of accepted proposals. -/
def acceptanceRate (xs : Array Float) : Float := Id.run do
  let mut moves := 0
  for i in [1:xs.size] do
    if xs[i]!.toBits != xs[i - 1]!.toBits then moves := moves + 1
  return moves.toFloat / (xs.size - 1).toFloat

/-- The bits of a `Float`, in hexadecimal: they are read back exactly. -/
def hexBits (x : Float) : String := String.ofList (Nat.toDigits 16 x.toBits.toNat)

/-- The sample mean of the states after `burnIn`. -/
def mean (xs : Array Float) (burnIn : Nat) : Float :=
  let ys := xs.extract burnIn xs.size
  ys.foldl (· + ·) 0 / ys.size.toFloat

/-- Run `r` through both routes, check that they agree, and write its trajectory. Returns whether
the checks passed. -/
def Run.go (r : Run) : IO Bool := do
  let a ← (IO.runRandPCGWith r.seed (trajectory r.stepA r.steps r.x₀) : IO (Array Float))
  let b ← (IO.runRandPCGWith r.seed (trajectory r.stepB r.steps r.x₀) : IO (Array Float))
  let chainA ← (IO.runRandPCGWith r.seed (mhChainComputable r.logπA r.var r.steps r.x₀) : IO Float)
  let chainB ← (IO.runRandPCGWith r.seed
    (mhChainPoly (m := RandM) (R := Float) (V := Float) r.logπB r.var r.steps r.x₀ : RandM Float) :
      IO Float)
  let sameTrajectory := a.map (·.toBits) == b.map (·.toBits)
  let last := a.back!.toBits
  let sameChain := chainA.toBits == last && chainB.toBits == last
  IO.FS.withFile s!"mh_output/{r.name}.csv" .write fun h ↦ do
    h.putStrLn "step,computable,polymorphic"
    for i in [0:a.size] do
      h.putStrLn s!"{i},{hexBits a[i]!},{hexBits b[i]!}"
  IO.println s!"{r.name}: {r.steps} steps, proposal std {r.var.sqrt}, \
    acceptance {acceptanceRate a}, mean after burn-in {mean a (r.steps / 10)}"
  IO.println s!"  computable = polymorphic, all {a.size} states: {sameTrajectory}; \
    one-shot chains land on the last state: {sameChain}"
  return sameTrajectory && sameChain

/-- The acceptance rate of `steps` steps of the chain, through both routes, for each proposal
standard deviation in `stds`. -/
def sweep (target : String) (logπA logπB : Float → Float) (stds : List Float) (steps : Nat) :
    IO (List String × Bool) := do
  let mut lines := []
  let mut ok := true
  for std in stds do
    let r : Run := { name := "", target, logπA, logπB, var := std * std, steps, seed := 7 }
    let a ← (IO.runRandPCGWith r.seed (trajectory r.stepA r.steps r.x₀) : IO (Array Float))
    let b ← (IO.runRandPCGWith r.seed (trajectory r.stepB r.steps r.x₀) : IO (Array Float))
    ok := ok && a.map (·.toBits) == b.map (·.toBits)
    lines := lines ++ [s!"{target},{std},{acceptanceRate a},{acceptanceRate b}"]
  return (lines, ok)

def main : IO UInt32 := do
  IO.FS.createDirAll "mh_output"
  let runs : List Run := [
    { name := "stdnormal", target := "stdNormal", logπA := stdNormalComputable,
      logπB := stdNormalPoly, var := 2.4 * 2.4, steps := 50000 },
    { name := "bimodal_small", target := "bimodal", logπA := bimodalComputable,
      logπB := bimodalPoly, var := 0.25 * 0.25, steps := 50000 },
    { name := "bimodal_good", target := "bimodal", logπA := bimodalComputable,
      logπB := bimodalPoly, var := 3 * 3, steps := 50000 },
    { name := "bimodal_large", target := "bimodal", logπA := bimodalComputable,
      logπB := bimodalPoly, var := 30 * 30, steps := 50000 }]
  let mut ok := true
  for r in runs do
    ok := (← r.go) && ok
  IO.FS.withFile "mh_output/runs.csv" .write fun h ↦ do
    h.putStrLn "name,target,var,steps,x0,seed"
    for r in runs do
      h.putStrLn s!"{r.name},{r.target},{hexBits r.var},{r.steps},{hexBits r.x₀},{r.seed}"
  let stds := (List.range 25).map fun k ↦ 0.05 * Float.pow 1000 (k.toFloat / 24)
  let (normalLines, okNormal) ← sweep "stdNormal" stdNormalComputable stdNormalPoly stds 5000
  let (bimodalLines, okBimodal) ← sweep "bimodal" bimodalComputable bimodalPoly stds 5000
  IO.FS.withFile "mh_output/acceptance.csv" .write fun h ↦ do
    h.putStrLn "target,std,computable,polymorphic"
    for l in normalLines ++ bimodalLines do h.putStrLn l
  IO.println s!"acceptance sweep over {stds.length} proposal stds: \
    computable = polymorphic: {okNormal && okBimodal}"
  ok := ok && okNormal && okBimodal
  IO.println (if ok then "all checks passed" else "SOME CHECKS FAILED")
  return if ok then 0 else 1
