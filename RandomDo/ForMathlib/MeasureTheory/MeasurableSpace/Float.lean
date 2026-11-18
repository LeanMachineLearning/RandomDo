/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# The measurable space on `Float`

Floating-point scalars carry the discrete measurable space.
-/

@[expose] public section

namespace Float

instance instMeasurableSpace : MeasurableSpace Float := ⊤

instance : MeasurableSingletonClass Float := ⟨fun _ => trivial⟩

end Float
