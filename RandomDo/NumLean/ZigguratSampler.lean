/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.NumLean.PCG64
public import FFI.Float

/-!
# The ziggurat sampler

The sampler shape numpy's `random_standard_normal` and `random_standard_exponential` share, the
ziggurat of Marsaglia and Tsang. The density is covered by 256 strips of equal area; a draw picks a
strip and a point in it, and is accepted at once when the point falls in the strip's rectangular
part, which is where about 99% of the draws end.

The tables the two samplers read live in `RandomDo.NumLean.Ziggurat`, and the samplers themselves
in `RandomDo.NumLean.Distributions`; this file holds only the shape they share, which is generic in
the tables `k`, `w` and `f` and in the three functions that say how a 64-bit output is cut up, what
the density is, and how the base strip's tail is sampled.

## Main definitions

* `ziggurat`: the sampler, whose fast path is inlined into its caller
* `zigguratSlow`: the branches the remaining ~1% of the draws take
* `zigguratWedge`: the rejection test on a strip that sticks out of the curve

## References

* G. Marsaglia and W. W. Tsang, *The Ziggurat Method for Generating Random Variables*, Journal of
  Statistical Software, 2000.
* numpy's samplers: `numpy/random/src/distributions/distributions.c`
-/

@[expose] public section

namespace NumLean

/-- The rejection test on a strip that sticks out of the curve: the point drawn at height `u`
between the density at the strip's two edges lies under the curve. -/
@[inline] def zigguratWedge (f : Array Float) (idx : Nat) (u density : Float) : Bool :=
  Float.fma (f[idx - 1]! - f[idx]!) u f[idx]! < density

/-- The rare branches of `ziggurat`, reached by about 1% of the draws: the strip either is the base
one, whose unbounded part `tail` samples from the integer drawn, or sticks out of the curve, and
then the point is tested against `density` and the whole draw is started over on rejection.

`idx`, `ri` and `x` are the strip, the integer and the abscissa `ziggurat` has already drawn and
found not to land in the rectangular part of its strip. Each redraw retries the fast path here
rather than returning to `ziggurat`, so the two together run exactly the loop of numpy's samplers.

This is kept apart from `ziggurat` so that the fast path can be inlined into its caller: a
recursive function cannot be, and behind a call boundary every draw would have to box the generator
state and its result, which costs several times the draw itself. -/
@[specialize] partial def zigguratSlow (k : Array UInt64) (w f : Array Float)
    (split : UInt64 → Nat × UInt64 × Bool) (density : Float → Float)
    (tail : UInt64 → RandPCG IO Float) (idx : Nat) (ri : UInt64) (x : Float) :
    RandPCG IO Float := do
  if idx == 0 then tail ri
  else if zigguratWedge f idx (← random) (density x) then return x
  else
    let (idx, ri, negate) := split (← randUInt64)
    let x := ri.toFloat * w[idx]!
    let x := if negate then -x else x
    if ri < k[idx]! then return x
    else zigguratSlow k w f split density tail idx ri x

/-- The sampler shape shared by numpy's `random_standard_normal` and
`random_standard_exponential`, the ziggurat of Marsaglia and Tsang: the density is covered by 256
strips of equal area, and one 64-bit output supplies at once the strip `idx` and the integer `ri`
that `w` scales to an abscissa, `split` saying how those bits are laid out and whether the deviate
comes out negated.

The draw is returned as it stands when `ri` falls below `k[idx]`, which is where about 99% of the
draws end; `zigguratSlow` takes over the remaining ones. -/
@[inline] def ziggurat (k : Array UInt64) (w f : Array Float)
    (split : UInt64 → Nat × UInt64 × Bool) (density : Float → Float)
    (tail : UInt64 → RandPCG IO Float) : RandPCG IO Float := do
  let (idx, ri, negate) := split (← randUInt64)
  let x := ri.toFloat * w[idx]!
  let x := if negate then -x else x
  if ri < k[idx]! then return x
  else zigguratSlow k w f split density tail idx ri x

end NumLean
