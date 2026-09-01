/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Control.Random
public import RandomDo.NumLean.SeedSequence

/-!
# The PCG-64 pseudo-random number generator

This file provides `PCG64`, a drop-in replacement for `StdGen` implementing the
`PCG-XSL-RR 128/64` variant of the permuted congruential generator family of O'Neill, i.e. the
generator known as `pcg64` in the reference C implementation and as `numpy.random.PCG64` in numpy.

The generator is a linear congruential generator on 128 bits,
`state ← state * multiplier + increment`, whose state is scrambled down to 64 bits by the
`XSL-RR` output permutation (xor the two halves together, then rotate by the top 6 bits of the
state). The 128-bit arithmetic is emulated with pairs of `UInt64`, so every operation compiles to
native machine arithmetic.

## Main definitions

* `PCG64`: the generator state, and its `RandomGen` instance
* `PCG64.seedWords` / `PCG64.seed` / `mkPCG64`: seeding, following the reference
  `pcg_setseq_128_srandom_r`

## References

* M. E. O'Neill, *PCG: A Family of Simple Fast Space-Efficient Statistically Good Algorithms for
  Random Number Generation*, 2014. <https://www.pcg-random.org/paper.html>
* The reference implementation: <https://github.com/imneme/pcg-c>
* numpy's vendored copy: `numpy/random/src/pcg64/pcg64.h`
-/

@[expose] public section

namespace NumLean

/-- The state of a PCG-64 generator: a 128-bit LCG state and a 128-bit increment (which selects the
stream and must be odd), each stored as a pair of 64-bit words. -/
structure PCG64 where
  /-- High 64 bits of the LCG state. -/
  stateHi : UInt64
  /-- Low 64 bits of the LCG state. -/
  stateLo : UInt64
  /-- High 64 bits of the increment. -/
  incHi : UInt64
  /-- Low 64 bits of the increment; it is odd for any generator built through the API below. -/
  incLo : UInt64
  deriving Repr, DecidableEq

namespace PCG64

/-- High 64 bits of the PCG-64 multiplier `0x2360ED051FC65DA44385DF649FCCF645`. -/
def multHi : UInt64 := 0x2360ED051FC65DA4

/-- Low 64 bits of the PCG-64 multiplier `0x2360ED051FC65DA44385DF649FCCF645`. -/
def multLo : UInt64 := 0x4385DF649FCCF645

/-- The default stream, i.e. the reference default increment `0x5851F42D4C957F2D14057B7EF767814F`
divided by two, since `seed` turns a stream `s` into the increment `2 * s + 1`. -/
def defaultStream : Nat := 0x2C28FA16A64ABF968A02BDBF7BB3C0A7

/-- The high 64 bits of the 128-bit product `a * b`, obtained from the four 32-bit limb products. -/
@[inline] def mulHi (a b : UInt64) : UInt64 :=
  let mask : UInt64 := 0xFFFFFFFF
  let a₀ := a &&& mask
  let a₁ := a >>> 32
  let b₀ := b &&& mask
  let b₁ := b >>> 32
  let t := a₁ * b₀ + (a₀ * b₀) >>> 32
  a₁ * b₁ + t >>> 32 + (a₀ * b₁ + (t &&& mask)) >>> 32

/-- Rotate the 64-bit word `x` right by `r` bits. Only the low 6 bits of `r` are used. -/
@[inline] def rotr (x r : UInt64) : UInt64 := (x >>> r) ||| (x <<< (64 - r))

/-- One step of the underlying 128-bit LCG, `state ← state * multiplier + increment`. -/
@[inline] def step (g : PCG64) : PCG64 :=
  let lo := g.stateLo * multLo
  let hi := mulHi g.stateLo multLo + g.stateLo * multHi + g.stateHi * multLo
  let lo' := lo + g.incLo
  -- unsigned addition wraps, so `lo' < lo` exactly when the low half carried
  let carry : UInt64 := if lo' < lo then 1 else 0
  { g with stateHi := hi + g.incHi + carry, stateLo := lo' }

/-- The `XSL-RR` output permutation: fold the 128-bit state onto 64 bits by xoring its two halves,
then rotate the result right by the 6 most significant bits of the state. -/
@[inline] def output (g : PCG64) : UInt64 :=
  rotr (g.stateHi ^^^ g.stateLo) (g.stateHi >>> 58)

/-- The next 64-bit output, together with the advanced generator. As in the reference
implementation, the state is stepped before the output permutation is applied. -/
@[inline] def nextUInt64 (g : PCG64) : UInt64 × PCG64 :=
  let g := g.step
  (g.output, g)

/-- Seed a generator from four 64-bit words, following the reference
`pcg_setseq_128_srandom_r`: `stateHi:stateLo` is the initial state and `seqHi:seqLo` selects the
stream, whose increment is `2 * seq + 1`. -/
def seedWords (stateHi stateLo seqHi seqLo : UInt64) : PCG64 :=
  let g : PCG64 :=
    { stateHi := 0, stateLo := 0,
      incHi := (seqHi <<< 1) ||| (seqLo >>> 63), incLo := (seqLo <<< 1) ||| 1 }
  let g := g.step
  let lo := g.stateLo + stateLo
  let carry : UInt64 := if lo < g.stateLo then 1 else 0
  step { g with stateHi := g.stateHi + stateHi + carry, stateLo := lo }

/-- Seed a generator from a `SeedSequence`, as numpy's `PCG64` constructor does: the first two
words drawn from the mixer give the initial state and the next two the stream. -/
def ofSeedSequence (s : SeedSequence) : PCG64 :=
  let w := s.generateState 4
  seedWords w[0]! w[1]! w[2]! w[3]!

/-- Seed a generator from an initial state. -/
def seed (n : Nat) : PCG64 := ofSeedSequence (SeedSequence.ofNat n)

/-- The `SeedSequence` whose entropy is `n` outputs taken from `g`, split into 32-bit words, the
advanced generator being returned alongside. Used to derive further generators from an existing
one. Two outputs are enough by default: they fill the mixing pool exactly, and no amount of extra
entropy would make it carry more than its `SeedSequence.poolSize` words. -/
def toSeedSequence (g : PCG64) (n : Nat := 2) : SeedSequence × PCG64 :=
  let (words, g) := Id.run do
    let mut g := g
    let mut words := Array.emptyWithCapacity (2 * n)
    for _ in List.range n do
      let (x, g') := g.nextUInt64
      g := g'
      words := (words.push x.toUInt32).push (x >>> 32).toUInt32
    return (words, g)
  (SeedSequence.ofWords words #[], g)

/-- The range of values returned by `PCG64`, namely all of `[0, 2 ^ 64 - 1]`. -/
def range : Nat × Nat := (0, UInt64.size - 1)

/-- Derive `n` generators from one, together with the parent advanced past the outputs used as
entropy. The children are the `SeedSequence.spawn` children of the entropy drawn from the parent,
so they are obtained exactly as any other family of generators in this library. -/
def spawn (g : PCG64) (n : Nat) : Array PCG64 × PCG64 :=
  let (s, g) := g.toSeedSequence
  ((s.spawn n).1.map ofSeedSequence, g)

/-- Derive two generators from one: the first is the current one advanced by two steps, the second
is the first `SeedSequence.spawn` child of those two outputs. Splitting is not part of the PCG
specification and nothing here establishes that the two streams are independent; going through the
mixer only removes the direct algebraic tie between the child's initial state and two consecutive
states of the parent. -/
def split (g : PCG64) : PCG64 × PCG64 :=
  let (s, g) := g.toSeedSequence
  (g, ofSeedSequence (s.spawn 1).1[0]!)

/-- The first `n` outputs of `g`. -/
def take (g : PCG64) (n : Nat) : Array UInt64 := Id.run do
  let mut g := g
  let mut out := Array.emptyWithCapacity n
  for _ in [:n] do
    let (x, g') := g.nextUInt64
    g := g'
    out := out.push x
  return out

end PCG64

/-- Returns a PCG-64 generator seeded with `s`, on the default stream. The analogue of
`mkStdGen`. -/
def mkPCG64 (s : Nat := 0) : PCG64 := PCG64.seed s

instance : Inhabited PCG64 := ⟨mkPCG64⟩

instance : RandomGen PCG64 where
  range _ := PCG64.range
  next g := let (x, g) := g.nextUInt64; (x.toNat, g)
  split := PCG64.split

/-- A monad transformer to generate random objects using the generator type `PCG64`.
`RandPCG m α` should be thought of a random value in `m α`. -/
abbrev RandPCG := RandGT PCG64

end NumLean

namespace IO

open NumLean

/-- A global reference to a PCG-64 generator, seeded from the system's random source. -/
initialize PCG64Ref : Ref PCG64 ←
  let seed := UInt64.toNat (ByteArray.toUInt64LE! (← IO.getRandomBytes 8))
  IO.mkRef (mkPCG64 seed)

variable {m : Type* → Type*} {m₀ : Type → Type}
variable [Monad m] [MonadLiftT (ST RealWorld) m₀] [ULiftable m₀ m]

set_option autoImplicit true

/-- Execute `RandPCG m α` using the global `PCG64Ref` as RNG. -/
def runRandPCG (cmd : RandPCG m α) : m α := do
  let PCG64 ← ULiftable.up (PCG64Ref.get : m₀ _)
  let (res, new) ← StateT.run cmd PCG64
  let _ ← ULiftable.up (PCG64Ref.set new.down : m₀ _)
  pure res

/-- Execute `RandPCG m α` using the global `PCG64Ref` as RNG and the given `seed`. -/
def runRandPCGWith (seed : Nat) (cmd : RandPCG m α) : m α := do
  pure <| (← cmd.run (ULift.up <| mkPCG64 seed)).1

end IO
