/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import MetropolisHastings.Defs
public meta import MetropolisHastings.Defs

/-!
# Random-walk Metropolis–Hastings, translated into a sampler

The `@[computable]` attribute reads the programs of `MetropolisHastings.Defs`, written over the
Giry monad, and writes the programs that sample from them:

* `mhStepComputable : (Float → Float) → Float → Float → RandPCG IO Float`,
* `mhChainComputable : (Float → Float) → Float → ℕ → Float → RandPCG IO Float`.

The Gaussian proposal becomes `NumLean.normal'`, the Bernoulli draw `bernoulliChoice`, `ℝ` and `ℝ≥0`
become `Float`, and the log-density becomes a function on `Float`. The theorems of
`MetropolisHastings.Theory` are about the programs read here; what is to be trusted is the
translation.
-/

@[expose] public section

namespace MetropolisHastings

attribute [computable] mhStep mhChain

end MetropolisHastings
