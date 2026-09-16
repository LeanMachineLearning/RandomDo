import RandomDo

open MeasureTheory ProbabilityTheory NumLean

universe v

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
variable {α β : Type*}
-- We could define a typeclass for type that have "classical" behavior, inheriting from `Add`, etc.
variable {R : Type} [MeasurableSpace R] [Add R] [OfNat R 0] [OfNat α 0] [OfNat β 1]

def ex1 [HasGaussian m α β R] : m R := rdo
  let mut x : R := 0
  for _ in List.range 1000000 rdo
    let y ← HasGaussian.gaussian (m := m) (α := α) (β := β) 0 1
    x := x + y
  return x

def main : IO Unit := do
  let x ← (IO.runRandPCGWith 42
    (ex1 (m := RandM) (α := Float) (β := Float) (R := Float)) : IO Float)
  IO.println s!"x = {x}"
