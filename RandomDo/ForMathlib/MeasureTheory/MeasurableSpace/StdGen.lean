/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# The measurable space on `StdGen`

`StdGen` is countable and carries the discrete measurable space.
-/

@[expose] public section

namespace StdGen

instance : Countable StdGen :=
  Function.Injective.countable (f := fun g : StdGen => (g.s1, g.s2)) (by
    rintro ⟨a, b⟩ ⟨c, d⟩
    simp)

instance instMeasurableSpace : MeasurableSpace StdGen := ⊤

instance : MeasurableSingletonClass StdGen := ⟨fun _ => trivial⟩

end StdGen
