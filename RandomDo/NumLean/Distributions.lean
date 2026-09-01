/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.NumLean.PCG64
public meta import RandomDo.NumLean.PCG64

/-!
# Sample from specific distributions using the PCG-64 generator.

This files provides samplers for specific distributions using the PCG-64 generator.

## Main definitions
* `randUInt64`: sample a `UInt64`.
* `random`: sample a `Float` in `[0, 1)`.
-/

@[expose] public section

namespace NumLean

/-- Sample a `UInt64` from a PCG-64 generator. -/
def randUInt64 : RandPCG IO UInt64 := do
  let (x, g) := (← get).down.nextUInt64
  set (ULift.up g)
  return x

/-- Sample a `Float` in `[0, 1)` from a PCG-64 generator. -/
def random : RandPCG IO Float := do
  let x ← randUInt64
  return (x >>> 11).toFloat * (Float.ofBits <| 0x3CA <<< (52 : UInt64))

end NumLean
