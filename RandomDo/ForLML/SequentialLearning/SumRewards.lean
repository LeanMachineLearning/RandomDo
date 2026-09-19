/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards

/-!
# The sum of the rewards of an action, one round later

## Main results

* `sumRewards'_snoc`: the sum of the rewards of an action in a history extended by one round.
-/

@[expose] public section

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} [DecidableEq 𝓐] [AddCommGroup 𝓨]

lemma sumRewards'_snoc (n : ℕ) (h : Hist 𝓞 𝓐 𝓨 n) (o : 𝓞) (a b : 𝓐) (y : 𝓨) :
    sumRewards' (n + 1) (Fin.snoc h (o, a, y)) b = sumRewards' n h b + if a = b then y else 0 := by
  rw [sumRewards', sumRewards', Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

end Learning
