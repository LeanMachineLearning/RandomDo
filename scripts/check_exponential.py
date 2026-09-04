import numpy as np
from common import compare

print("Checking exponential distribution...")

LEAN = """import RandomDo
import Batteries.Data.Float.Basic
def main (args : List String) : IO Unit := do
  for s in args do
    IO.FS.withFile (System.FilePath.mk s!"@DIR@/pcg64-{s}.txt") .write fun h ↦
      IO.runRandPCGWith s.toNat! do
        for _ in List.range @N@ do h.putStrLn (← NumLean.exponential).toStringFull
"""

distrib = lambda seed, N: np.random.default_rng(seed).exponential(size=N)

compare(LEAN, distrib)