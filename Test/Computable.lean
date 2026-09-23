module

public import Test.IsMarkov
public import Test.Bind
public meta import RandomDo
import Batteries.Data.Float.Basic

set_option linter.style.header false

set_option trace.computable true

namespace Test.Computable

open Test.IsMarkov NumLean Lean.Elab.Command MeasureTheory ProbabilityTheory

def logComputable {α : Type} [Lean.ToMessageData α] (prog : RandPCG IO α) : CommandElabM Unit := do
  let x ← (IO.runRandPCG prog : IO α)
  let y ← (IO.runRandPCGWith 42 prog : IO α)
  Lean.logInfo m!"x = {x}"
  Lean.logInfo m!"y (seed 42) = {y}"

attribute [computable] sumTwo

run_cmd logComputable sumTwoComputable

@[computable]
noncomputable
def unfoldSumTwo : Measure ℝ := rdo
  let y ← sumTwo
  let x ← gaussianReal 0 1
  return x + y

attribute [computable] centred

run_cmd logComputable (centredComputable 20)

attribute [computable] branchOn

run_cmd do logComputable (branchOnComputable 20)

run_cmd logComputable (branchOnComputable (-1))

attribute [computable] fairCoin

run_cmd logComputable (fairCoinComputable)

attribute [computable] Bind.twoCoins

run_cmd logComputable (Bind.twoCoinsComputable)

@[computable]
noncomputable
def ex1 : Measure ℝ := rdo
  let mut x := 0
  for _ in List.range 1000 rdo
    let y ← gaussianReal 0 1
    x := x + y
  return x

run_cmd logComputable (ex1Computable)

end Test.Computable
