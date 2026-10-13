/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Examples.VonNeumann

/-!
# Concrete checks of the von Neumann specification
-/

@[expose] public section

open MeasureTheory Std.Internal.Do Examples.VonNeumann
open scoped ENNReal unitInterval

set_option mvcgen.warning false

namespace Test.VonNeumann

noncomputable def half : I := ⟨1 / 2, by norm_num⟩

private theorem toNNReal_half : unitInterval.toNNReal half = 1 / 2 := by
  apply NNReal.eq
  norm_num [half]

private theorem symm_half : unitInterval.symm half = half := by
  ext
  norm_num [half]

private theorem successProb_half_three : successProb half 3 = 7 / 16 := by
  apply NNReal.eq
  rw [successProb, NNReal.coe_div, NNReal.coe_sub (failureProb_le_one half 3)]
  norm_num [failureProb, rejectProb, symm_half, toNNReal_half]

example (p : I) : sample p 0 = Measure.dirac none := by simp

example (n : ℕ) : sample 0 n = Measure.dirac none := by simp

example (n : ℕ) : sample 1 n = Measure.dirac none := by simp

example : sample half 3 {none} = 1 / 8 := by
  norm_num [failureProb, rejectProb, symm_half, toNNReal_half]

example (b : Bool) : sample half 3 {some b} = 7 / 16 := by
  norm_num [successProb_half_three]

-- The exported specification is reusable without unfolding the sampler or repeating its proof.
example : Triple (sample half 3) (7 / 16) (fun x ↦ if x = some true then 1 else 0) ⟨⟩ := by
  vcgen
  norm_num [invariant, successProb_half_three, failureProb, rejectProb, symm_half,
    toNNReal_half, show (none : Option Bool) ≠ some true from by decide]

end Test.VonNeumann
