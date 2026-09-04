/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.NumLean.PCG64
public meta import RandomDo.NumLean.PCG64
public import FFI.Float
public import RandomDo.NumLean.Ziggurat

/-!
# Sample from specific distributions using the PCG-64 generator.

This file provides samplers for specific distributions using the PCG-64 generator. Each one draws
exactly what its numpy counterpart draws, so that a `RandPCG` program and a numpy `Generator`
seeded alike produce the same values.

## Main definitions
* `randUInt64` / `randUInt32`: sample a `UInt64`, or a `UInt32` as numpy's `next_uint32` does.
* `random`: sample a `Float` in `[0, 1)`.
* `randInt`: sample an integer in `[low, high)` or `[low, high]`, as numpy's `Generator.integers`.
* `uniform`: sample a `Float` in `[low, high)`, as numpy's `Generator.uniform`.
* `standardNormal` / `normal`: sample a normal deviate, as numpy's `Generator.normal`.
* `standardExponential` / `exponential`: sample an exponential deviate, as numpy's
  `Generator.exponential`.
* `ziggurat`: the sampler shape both of those share.
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

/-- Sample a `Float` uniformly in `[low, high)`. -/
def uniform (low high : Float) : RandPCG IO Float := do
  if low > high then throw <| IO.userError "low > high"
  let x ← random
  return Float.fma x (high - low) low

/-- The rejection test on a strip that sticks out of the curve: the point drawn at height `u`
between the density at the strip's two edges lies under the curve. -/
@[inline] def zigguratWedge (f : Array Float) (idx : Nat) (u density : Float) : Bool :=
  Float.fma (f[idx - 1]! - f[idx]!) u f[idx]! < density

/-- The sampler shape shared by numpy's `random_standard_normal` and
`random_standard_exponential`, the ziggurat of Marsaglia and Tsang: the density is covered by 256
strips of equal area, and one 64-bit output supplies at once the strip `idx` and the integer `ri`
that `w` scales to an abscissa, `split` saying how those bits are laid out and whether the deviate
comes out negated.

The draw is returned as it stands when `ri` falls below `k[idx]`, which is where about 99% of the
draws end. Otherwise the strip either is the base one, whose unbounded part `tail` samples from the
integer drawn, or sticks out of the curve, and then the point is tested against `density` and the
whole draw is started over on rejection. -/
@[specialize] partial def ziggurat (k : Array UInt64) (w f : Array Float)
    (split : UInt64 → Nat × UInt64 × Bool) (density : Float → Float)
    (tail : UInt64 → RandPCG IO Float) : RandPCG IO Float := do
  let (idx, ri, negate) := split (← randUInt64)
  let x := ri.toFloat * w[idx]!
  let x := if negate then -x else x
  if ri < k[idx]! then return x
  if idx == 0 then tail ri
  else if zigguratWedge f idx (← random) (density x) then return x
  else ziggurat k w f split density tail

/-- Sample the tail of the standard normal beyond `Ziggurat.norR`, as the `idx == 0` branch of
numpy's `random_standard_normal`: draw from an exponential tail until the pair of draws falls under
the normal's, which is Marsaglia's method for the tail. `negate` carries the sign numpy reads off
the integer already drawn, which the loop does not redraw. -/
partial def normalTail (negate : Bool) : RandPCG IO Float := do
  let xx := -Ziggurat.norInvR * Float.log1p (-(← random))
  let yy := -Float.log1p (-(← random))
  if yy + yy > xx * xx then
    return if negate then -(Ziggurat.norR + xx) else Ziggurat.norR + xx
  normalTail negate

/-- Sample from the standard normal, as numpy's `random_standard_normal`. The 64-bit output gives
the strip in its low byte, then the sign, then a 52-bit abscissa; the tail takes its sign from a
further bit of that same abscissa, as numpy does. -/
def standardNormal : RandPCG IO Float :=
  ziggurat Ziggurat.ki Ziggurat.wi Ziggurat.fi
    (fun r =>
      let idx := (r &&& 0xFF).toNat
      let r := r >>> 8
      (idx, (r >>> 1) &&& 0x000FFFFFFFFFFFFF, (r &&& 1) == 1))
    (fun x => Float.exp ((-0.5) * x * x))
    (fun rabs => normalTail (((rabs >>> 8) &&& 1) == 1))

/-- Sample from the standard exponential, as numpy's `random_standard_exponential`. The 64-bit
output is first shifted by three, then gives the strip in its low byte and a 53-bit abscissa; the
tail is the exponential's own, memoryless, so one draw beyond `Ziggurat.expR` suffices. -/
def standardExponential : RandPCG IO Float :=
  ziggurat Ziggurat.ke Ziggurat.we Ziggurat.fe
    (fun r =>
      let r := r >>> 3
      ((r &&& 0xFF).toNat, r >>> 8, false))
    (fun x => Float.exp (-x))
    (fun _ => do return Ziggurat.expR - Float.log1p (-(← random)))

/-- Draw random samples from a normal (Gaussian) distribution. -/
def normal (loc : Float := 0) (scale : Float := 1) : RandPCG IO Float := do
  if scale < 0 then throw <| IO.userError "scale < 0"
  return Float.fma scale (← standardNormal) loc

/-- Draw samples from an exponential distribution. -/
def exponential (scale : Float := 1) : RandPCG IO Float := do
  if scale < 0 then throw <| IO.userError "scale < 0"
  return scale * (← standardExponential)

end NumLean
