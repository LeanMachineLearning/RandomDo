module

public import Test.IsMarkov
import Batteries.Data.Float.Basic
/- A `run_cmd` runs at elaboration time, so what it calls has to be imported as `meta` too: the
sampler it draws with, and `Float.toStringFull` it prints with. -/
meta import RandomDo.NumLean.Distributions
meta import Batteries.Data.Float.Basic

set_option linter.style.header false

set_option trace.computable true

namespace Test.Computable

open Test.IsMarkov NumLean Lean.Elab.Command

def logComputable (prog : RandPCG IO Float) : CommandElabM Unit := do
  let x ← (IO.runRandPCG prog : IO Float)
  let y ← (IO.runRandPCGWith 42 prog : IO Float)
  Lean.logInfo m!"x = {x.toStringFull}"
  Lean.logInfo m!"y (seed 42) = {y.toStringFull}"

--attribute [computable] sumTwo

--run_cmd do logComputable sumTwoComputable

@[computable]
noncomputable
def test : MeasureTheory.Measure ℝ := rdo
  let y ← sumTwo
  let x ← ProbabilityTheory.gaussianReal 0 1
  return x + y

attribute [computable] centred

run_cmd do logComputable (centredComputable 20)

attribute [computable] branchOn

run_cmd do logComputable (branchOnComputable 20)

run_cmd do logComputable (branchOnComputable (-1))

end Test.Computable
