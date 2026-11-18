/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Measurable spaces on unsigned machine integers

The finite types `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `USize` carry the discrete
measurable space.
-/

@[expose] public section

namespace UInt8

instance instMeasurableSpace : MeasurableSpace UInt8 := ⊤

instance : MeasurableSingletonClass UInt8 := ⟨fun _ => trivial⟩

end UInt8

namespace UInt16

instance instMeasurableSpace : MeasurableSpace UInt16 := ⊤

instance : MeasurableSingletonClass UInt16 := ⟨fun _ => trivial⟩

end UInt16

namespace UInt32

instance instMeasurableSpace : MeasurableSpace UInt32 := ⊤

instance : MeasurableSingletonClass UInt32 := ⟨fun _ => trivial⟩

end UInt32

namespace UInt64

instance instMeasurableSpace : MeasurableSpace UInt64 := ⊤

instance : MeasurableSingletonClass UInt64 := ⟨fun _ => trivial⟩

end UInt64

namespace USize

instance instMeasurableSpace : MeasurableSpace USize := ⊤

instance : MeasurableSingletonClass USize := ⟨fun _ => trivial⟩

end USize
