/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# The number of pulls of an action, one round later

## Main results

* `pullCount'_snoc`: the number of pulls of an action in a history extended by one round.
-/

@[expose] public section

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} [DecidableEq 𝓐]

lemma pullCount'_snoc (n : ℕ) (h : Hist 𝓞 𝓐 𝓨 n) (o : 𝓞) (a b : 𝓐) (y : 𝓨) :
    pullCount' (n + 1) (Fin.snoc h (o, a, y)) b = pullCount' n h b + if a = b then 1 else 0 := by
  rw [pullCount'_eq_sum, pullCount'_eq_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

end Learning
