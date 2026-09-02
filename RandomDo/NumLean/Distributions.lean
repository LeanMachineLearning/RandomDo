/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.NumLean.PCG64
public meta import RandomDo.NumLean.PCG64
public import Batteries.Data.Float.Basic

/-!
# Sample from specific distributions using the PCG-64 generator.

This file provides samplers for specific distributions using the PCG-64 generator. Each one draws
exactly what its numpy counterpart draws, so that a `RandPCG` program and a numpy `Generator`
seeded alike produce the same values.

## Main definitions
* `randUInt64` / `randUInt32`: sample a `UInt64`, or a `UInt32` as numpy's `next_uint32` does.
* `random`: sample a `Float` in `[0, 1)`.
* `randInt`: sample an integer in `[low, high)` or `[low, high]`, as numpy's `Generator.integers`.
-/

@[expose] public section

namespace NumLean

/-- Sample a `UInt64` from a PCG-64 generator. -/
def randUInt64 : RandPCG IO UInt64 := do
  let (x, g) := (← get).down.nextUInt64
  set (ULift.up g)
  return x

/-- Sample a `UInt32` from a PCG-64 generator, as numpy's `next_uint32` does for `PCG64`: the two
halves of each 64-bit output are handed out in turn, see `PCG64.nextUInt32`. -/
def randUInt32 : RandPCG IO UInt32 := do
  let (x, g) := (← get).down.nextUInt32
  set (ULift.up g)
  return x

/-- Sample a `UInt32` uniformly in `[0, rng]` by Lemire's nearly divisionless rejection method, as
numpy's `buffered_bounded_lemire_uint32`. -/
def randLemireUInt32 (rng : UInt32) : RandPCG IO UInt32 := do
  let rngExcl := rng + 1
  let mut m := (← randUInt32).toUInt64 * rngExcl.toUInt64
  if m.toUInt32 < rngExcl then
    let threshold := (0xFFFFFFFF - rng) % rngExcl
    while m.toUInt32 < threshold do
      m := (← randUInt32).toUInt64 * rngExcl.toUInt64
  return (m >>> 32).toUInt32

/-- Sample a `UInt64` uniformly in `[0, rng]` by Lemire's method, as numpy's
`bounded_lemire_uint64`. -/
def randLemireUInt64 (rng : UInt64) : RandPCG IO UInt64 := do
  let rngExcl := rng + 1
  let mut x ← randUInt64
  let mut leftover := x * rngExcl
  if leftover < rngExcl then
    let threshold := (0xFFFFFFFFFFFFFFFF - rng) % rngExcl
    while leftover < threshold do
      x ← randUInt64
      leftover := x * rngExcl
  return PCG64.mulHi x rngExcl

/-- Sample a `UInt64` uniformly in `[0, rng]`, as numpy's `random_bounded_uint64` with Lemire's
rejection. -/
def randBoundedUInt64 (rng : UInt64) : RandPCG IO UInt64 := do
  if rng == 0 then return 0
  else if rng == 0xFFFFFFFF then return (← randUInt32).toUInt64
  else if rng < 0xFFFFFFFF then return (← randLemireUInt32 rng.toUInt32).toUInt64
  else if rng == 0xFFFFFFFFFFFFFFFF then randUInt64
  else randLemireUInt64 rng

/-- Sample an integer uniformly in `[low, high)`, or in `[low, high]` when `endpoint` is set, as
numpy's `Generator.integers`. -/
def randInt₀ (low high : Int) (endpoint : Bool := false) : RandPCG IO Int := do
  let high := if endpoint then high else high - 1
  if low < Int64.minValue.toInt then throw <| IO.userError "low is out of bounds for int64"
  if high > Int64.maxValue.toInt then throw <| IO.userError "high is out of bounds for int64"
  if low > high then throw <| IO.userError (if endpoint then "low > high" else "low >= high")
  let x ← randBoundedUInt64 (high - low).toNat.toUInt64
  return low + x.toNat

/-- Sample an integer uniformly in `[0, high)`, or in `[0, high]` when `endpoint` is set. -/
def randInt (high : Int) (endpoint : Bool := false) : RandPCG IO Int := randInt₀ 0 high endpoint

/-- Sample an integer uniformly in `[low, high)`, or in `[low, high]` when `endpoint` is set. -/
def randBoundedInt (low high : Int) (endpoint : Bool := false) : RandPCG IO Int :=
    randInt₀ low high endpoint

/-- Sample a `Float` in `[0, 1)` from a PCG-64 generator. -/
def random : RandPCG IO Float := do
  let x ← randUInt64
  return (x >>> 11).toFloat * (Float.ofBits <| 0x3CA <<< (52 : UInt64))

/-- `x * y + z`, rounded once, as the C `fma`: the product and the sum are computed exactly, as
integers scaled by a power of two, and only the final value is rounded to a `Float`. -/
def fma (x y z : Float) : Float :=
  match x.toRatParts, y.toRatParts, z.toRatParts with
  | some (vx, ex), some (vy, ey), some (vz, ez) =>
    -- the product is `vx * vy * 2 ^ (ex + ey)`, so the sum is exact over the common exponent `e`
    let ep := ex + ey
    let e := min ep ez
    let n := vx * vy * 2 ^ (ep - e).toNat + vz * 2 ^ (ez - e).toNat
    if e ≥ 0 then Int.divFloat (n * 2 ^ e.toNat) 1 else Int.divFloat n (2 ^ (-e).toNat)
  | _, _, _ => x * y + z

/-- Sample a `Float` uniformly in `[low, high)`. -/
def uniform (low high : Float) : RandPCG IO Float := do
  if low > high then throw <| IO.userError "low > high"
  let x ← random
  return fma x (high - low) low

end NumLean
