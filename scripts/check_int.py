import os, shutil, subprocess, sys
from decimal import Decimal
import numpy as np

N, SEEDS, DIR = 1_000_000, np.random.randint(1_000_000_000, size=5), "test_data"

LEAN = """import RandomDo
import Batteries.Data.Float.Basic
def main (args : List String) : IO Unit := do
  for s in args do
    IO.FS.withFile (System.FilePath.mk s!"@DIR@/pcg64-{s}.txt") .write fun h ↦
      IO.runRandPCGWith s.toNat! do
        for _ in List.range @N@ do h.putStrLn <| toString (← NumLean.randInt 1000000)
"""

shutil.rmtree(DIR, ignore_errors=True)
os.makedirs(DIR)
open(f"{DIR}/dump.lean", "w").write(LEAN.replace("@DIR@", DIR).replace("@N@", str(N)))
subprocess.run(
    ["lake", "build"], check=True
)
subprocess.run(
    ["lake", "env", "lean", "--run", f"{DIR}/dump.lean", *map(str, SEEDS)], check=True
)


def check_distrib(path, xs):
    with open(path) as f:
        for i, (line, x) in enumerate(zip(f, xs)):
            if line.rstrip("\n") != format(Decimal(float(x)), "f"):
                return i
    return None


ok = True
for seed in SEEDS:
    xs = np.random.default_rng(seed).integers(1000000, size=N)
    bad_line = check_distrib(f"{DIR}/pcg64-{seed}.txt", xs)
    if bad_line is None:
        print(f"seed {seed} {N} identical draws")
    else:
        print(f"seed {seed} DIVERGENCE at line {bad_line}")
    ok = ok and bad_line is None

sys.exit(0 if ok else 1)
