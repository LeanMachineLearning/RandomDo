module

public import RandomDo

set_option linter.style.header false

open NumLean IO Lean

run_cmd do
  let x ← rand 0 1000
  logInfo m!"Random number between 0 and 1000: {x}"

run_cmd do
  let x ← (runRandPCG <| randInt 1000 : IO Int)
  logInfo m!"Random number between 0 and 1000 (PCG): {x}"

run_cmd do
  let x ← (runRandPCG <| normal 10 2 : IO Float)
  logInfo m!"{x}"

run_cmd do
  let x ← (runRandPCG <| exponential 10 : IO Float)
  logInfo m!"{x}"

run_cmd do
  let x ← (runRandPCG <| binomial 10 0.5 : IO Nat)
  logInfo m!"{x}"

run_cmd do
  let x ← (runRandPCG <| bernoulli 0.5 : IO Nat)
  logInfo m!"{x}"
