import numpy as np
from common import compare

print("Checking uniform distribution over integers...")

LEAN = """import RandomDo
import Batteries.Data.Float.Basic
def main (args : List String) : IO Unit := do
  for s in args do
    IO.FS.withFile (System.FilePath.mk s!"@DIR@/pcg64-{s}.txt") .write fun h ↦
      IO.runRandPCGWith s.toNat! do
        for _ in List.range @N@ do h.putStrLn <| toString (← NumLean.randInt 1000000)
"""

distrib = lambda seed, N: np.random.default_rng(seed).integers(1000000, size=N)

compare(LEAN, distrib)