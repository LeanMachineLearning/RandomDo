/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module  -- shake: keep-all --deprecated_module: ignore

public import Bandits.Defs
public import Bandits.Theory

/-!
# A Gaussian bandit, written in `rdo`, proved and run

* `Bandits.Defs`: one round of interaction, and `n` rounds, as `rdo` programs polymorphic in the
  monad and the scalars; explore-then-commit and UCB as the algorithms choosing the arm.
* `Bandits.Theory`: read at `Measure`, the programs have the law of LeanMachineLearning's
  interaction, so its regret bounds hold for them.

To run them and draw the regret against the bounds, from the root of the repository:

```
lake exe bandits                  # 300 seeds × 5000 rounds; writes bandit_output/
python3 scripts/bandit_plot.py    # checks them against numpy, draws bandit_output/*.png
```
-/
