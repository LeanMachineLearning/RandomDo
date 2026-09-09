/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

/-!
# Numpy's `SeedSequence` entropy mixer

Numpy instead runs the user's seed through `SeedSequence`, an entropy mixer whose job is to turn a
small, structured seed (`0`, `1`, `2`, ...) into 128 well-distributed bits, so that consecutive
seeds yield unrelated streams. The algorithm is a two-stage avalanche on 32-bit words: a pool of
four words absorbs the entropy, every word is mixed into every other one, then the requested output
words are drawn from the pool through a second hash.

## Main definitions

* `SeedSequence`: the mixer state, built by `SeedSequence.ofNat`;
* `SeedSequence.generateState`: draw 64-bit words from the pool;
* `SeedSequence.spawn`: derive independent child sequences, Numpy's principled alternative to
  `RandomGen.split`;

## References

* Numpy's implementation: `numpy/random/bit_generator.pyx`.
* The design it follows: M. E. O'Neill, *Developing a seed_seq Alternative*, 2015.
  <https://www.pcg-random.org/posts/developing-a-seed_seq-alternative.html>
-/

@[expose] public section

namespace NumLean

/-- Numpy's entropy mixer. `entropy` is the user's seed and `spawnKey` identifies the sequence among
the descendants of the original one; the `pool` is the mixed entropy both are absorbed into. -/
structure SeedSequence where
  /-- The seed, as 32-bit words, least significant first. -/
  entropy : Array UInt32
  /-- The path identifying this sequence among the descendants of the root one. -/
  spawnKey : Array UInt32
  /-- How many children have already been spawned from this sequence. -/
  nChildrenSpawned : Nat
  /-- The mixed entropy, of length `SeedSequence.poolSize`. -/
  pool : Array UInt32
  deriving Repr, Inhabited

namespace SeedSequence

/-- Number of 32-bit words held in the mixing pool. -/
def poolSize : Nat := 4

/-- Amount by which a hashed word is xor-shifted, half of a word's width. -/
def xshift : UInt32 := 16

/-- Initial hash constant of the entropy-absorbing stage. -/
def initA : UInt32 := 0x43B0D7E5

/-- Multiplier of the entropy-absorbing stage. -/
def multA : UInt32 := 0x931E8875

/-- Initial hash constant of the output stage. -/
def initB : UInt32 := 0x8B51F9DD

/-- Multiplier of the output stage. -/
def multB : UInt32 := 0x58F38DED

/-- Left multiplier of the pool mixing function. -/
def mixMultL : UInt32 := 0xCA01F9DD

/-- Right multiplier of the pool mixing function. -/
def mixMultR : UInt32 := 0x4973F715

/-- Hash a word against the running hash constant, returning the hashed word and the advanced
constant. -/
@[inline] def hashmix (value hashConst : UInt32) : UInt32 × UInt32 :=
  let value := value ^^^ hashConst
  let hashConst := hashConst * multA
  let value := value * hashConst
  (value ^^^ (value >>> xshift), hashConst)

/-- Combine two pool words. -/
@[inline] def mix (x y : UInt32) : UInt32 :=
  let r := mixMultL * x - mixMultR * y
  r ^^^ (r >>> xshift)

/-- Auxiliary function for `toWords`, accumulating the 32-bit words of `n`. -/
def toWordsAux (n : Nat) (acc : Array UInt32) : Array UInt32 :=
  if h : n = 0 then acc
  else toWordsAux (n / 4294967296) (acc.push (UInt32.ofNat (n % 4294967296)))
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

/-- Split a natural number into 32-bit words, least significant first. Zero maps to `#[0]`, as in
Numpy's `_int_to_uint32_array`. -/
def toWords (n : Nat) : Array UInt32 := if n = 0 then #[0] else toWordsAux n #[]

/-- Absorb an entropy array into a pool of `poolSize` words: seed the pool, then mix every word
into every other one so that late bits influence early ones, and finally fold in whatever entropy
did not fit in the pool. -/
def mixEntropy (entropy : Array UInt32) : Array UInt32 := Id.run do
  let mut pool : Array UInt32 := Array.replicate poolSize 0
  let mut hashConst := initA
  for i in [:poolSize] do
    let (v, hc) := hashmix (entropy[i]?.getD 0) hashConst
    pool := pool.set! i v
    hashConst := hc
  for src in [:poolSize] do
    for dst in [:poolSize] do
      if src ≠ dst then
        let (h, hc) := hashmix pool[src]! hashConst
        pool := pool.set! dst (mix pool[dst]! h)
        hashConst := hc
  for src in [poolSize:entropy.size] do
    for dst in [:poolSize] do
      let (h, hc) := hashmix entropy[src]! hashConst
      pool := pool.set! dst (mix pool[dst]! h)
      hashConst := hc
  return pool

/-- Build a sequence from an entropy array and a spawn key. When a spawn key is present, the
entropy is padded with zeros up to the pool size, so that a child cannot collide with a root
sequence whose seed happens to look like the concatenation of the two. -/
def ofWords (entropy spawnKey : Array UInt32) : SeedSequence :=
  let entropy' :=
    if spawnKey.isEmpty || poolSize ≤ entropy.size then entropy
    else entropy ++ Array.replicate (poolSize - entropy.size) 0
  { entropy, spawnKey, nChildrenSpawned := 0, pool := mixEntropy (entropy' ++ spawnKey) }

/-- The sequence Numpy builds from an integer seed, i.e. `numpy.random.SeedSequence(n)`. -/
def ofNat (n : Nat) : SeedSequence := ofWords (toWords n) #[]

/-- Draw `n` 64-bit words from the pool. Each is assembled from two consecutive 32-bit outputs,
least significant first, as Numpy does when asked for `dtype=np.uint64`. -/
def generateState (s : SeedSequence) (n : Nat) : Array UInt64 := Id.run do
  let mut words : Array UInt32 := Array.emptyWithCapacity (2 * n)
  let mut hashConst := initB
  for i in [:2 * n] do
    let v := s.pool[i % poolSize]! ^^^ hashConst
    hashConst := hashConst * multB
    let v := v * hashConst
    words := words.push (v ^^^ (v >>> xshift))
  let mut out := Array.emptyWithCapacity n
  for i in [:n] do
    out := out.push (words[2 * i]!.toUInt64 ||| (words[2 * i + 1]!.toUInt64 <<< 32))
  return out

/-- Derive `n` child sequences, together with the parent updated to remember how many children it
has produced. Each child absorbs a distinct spawn key into the mixer, so it is a pure function of
the root entropy and of its key path: it can be rebuilt directly, without replaying any draw, and
does not depend on how much the parent has been used. Their statistical independence rests on the
avalanche quality of the mixer, not on a proof. -/
def spawn (s : SeedSequence) (n : Nat) : Array SeedSequence × SeedSequence := Id.run do
  let mut children := Array.emptyWithCapacity n
  for i in [:n] do
    children := children.push (ofWords s.entropy (s.spawnKey ++ toWords (s.nChildrenSpawned + i)))
  return (children, { s with nChildrenSpawned := s.nChildrenSpawned + n })

end SeedSequence

end NumLean
