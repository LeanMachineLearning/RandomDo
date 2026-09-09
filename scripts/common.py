import os, shutil, subprocess, sys
from decimal import Decimal
import numpy as np

N, SEEDS, DIR = 1_000_000, np.random.randint(1_000_000_000, size=5), "test_data"

def check_distrib(path, xs):
    with open(path) as f:
        for i, (line, x) in enumerate(zip(f, xs)):
            if line.rstrip("\n") != format(Decimal(float(x)), "f"):
                return i
    return None

def compare(lean_code, distrib): 
  shutil.rmtree(DIR, ignore_errors=True)
  os.makedirs(DIR)
  open(f"{DIR}/Dump.lean", "w").write(lean_code.replace("@DIR@", DIR).replace("@N@", str(N)))
  subprocess.run(["lake", "exe", "dump", *map(str, SEEDS)], check=True)

  ok = True
  for seed in SEEDS:
      xs = distrib(seed, N)
      bad_line = check_distrib(f"{DIR}/pcg64-{seed}.txt", xs)
      if bad_line is None:
          print(f"seed {seed} {N} identical draws")
      else:
          print(f"seed {seed} DIVERGENCE at line {bad_line}")
      ok = ok and bad_line is None

  sys.exit(0 if ok else 1)
