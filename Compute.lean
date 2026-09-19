import RandomDo

open MeasureTheory ProbabilityTheory NumLean

@[computable]
noncomputable def ex1 : Measure ℝ := rdo
  let mut x := 0
  for _ in List.range 1000000 rdo
    let y ← gaussianReal 0 1
    x := x + y
  return x

def main : IO Unit := do
  let x ← (IO.runRandPCGWith 42 ex1Computable : IO Float)
  IO.println s!"x = {x}"
