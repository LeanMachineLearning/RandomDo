/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module  -- shake: keep-all --deprecated_module: ignore

public import MetropolisHastings.Computable
public import MetropolisHastings.Defs
public import MetropolisHastings.Polymorphic
public import MetropolisHastings.Targets
public import MetropolisHastings.Theory

/-!
# Random-walk Metropolis–Hastings, written in `rdo`, proved and run

* `MetropolisHastings.Defs`: the algorithm, as `rdo` programs over the Giry monad.
* `MetropolisHastings.Theory`: they are Markov kernels, satisfy detailed balance with respect to the
  target, and leave it invariant after any number of steps.
* `MetropolisHastings.Computable`: the samplers `@[computable]` writes from them.
* `MetropolisHastings.Polymorphic`: the same algorithm, polymorphic in the monad; at `Measure` it
  is the one of `Defs`, so the theorems carry over, and at `RandM` it samples.
* `MetropolisHastings.Targets`: two targets to run the chain on, for both routes.

To run it and draw the plots, from the root of the repository:

```
lake exe mh                     # runs both samplers, checks they agree, writes mh_output/
python3 scripts/mh_plot.py      # checks them against numpy, draws mh_output/*.png
```
-/
