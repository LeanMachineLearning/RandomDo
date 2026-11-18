/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.NumLean.PCG64
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# The measurable space on `PCG64`

The generator state, including its buffered 32-bit output, is countable and carries the discrete
measurable space. These instances allow its pure state monad to inherit the measurable monad laws.
-/

@[expose] public section

namespace NumLean.PCG64

instance : Countable PCG64 :=
  Function.Injective.countable (f := fun g : PCG64 =>
    (g.stateHi.toNat, g.stateLo.toNat, g.incHi.toNat, g.incLo.toNat,
      g.hasUInt32, g.uinteger.toNat)) (by
    rintro ⟨a, b, c, d, e, f⟩ ⟨a', b', c', d', e', f'⟩ h
    simpa [UInt64.toNat_inj, UInt32.toNat_inj] using h)

instance instMeasurableSpace : MeasurableSpace PCG64 := ⊤

instance : MeasurableSingletonClass PCG64 := ⟨fun _ => trivial⟩

end NumLean.PCG64
