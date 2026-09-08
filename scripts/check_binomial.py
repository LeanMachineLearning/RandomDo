import numpy as np
from common import compare

print("Checking binomial distribution...")

# One pair per branch of numpy's `random_binomial`: inversion and BTPE, each on both sides of
# `p = 1/2`, on both sides of the `n * p = 30` threshold, and the three degenerate cases.
PARAMS = [(10, 0.3), (60, 0.5), (100, 0.31), (1000, 0.5), (1000, 0.9), (5, 0.99),
          (0, 0.5), (10, 0.0), (10, 1.0)]

LEAN = """import RandomDo
def params : List (Nat × Float) :=
  [%s]
def main (args : List String) : IO Unit := do
  for s in args do
    IO.FS.withFile (System.FilePath.mk s!"@DIR@/pcg64-{s}.txt") .write fun h ↦
      IO.runRandPCGWith s.toNat! do
        for _ in List.range (@N@ / %d) do
          for (n, p) in params do
            h.putStrLn (toString (← NumLean.binomial n p))
""" % (",\n   ".join(f"({n}, {p})" for n, p in PARAMS), len(PARAMS))

def distrib(seed, N):
    g = np.random.default_rng(seed)
    return [g.binomial(n, p) for _ in range(N // len(PARAMS)) for n, p in PARAMS]

compare(LEAN, distrib)
