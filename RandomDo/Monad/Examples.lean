module

public import RandomDo.Monad.ForInInstances
public import RandomDo.Monad.Instances
public import RandomDo.Measurable
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Probability.Distributions.Bernoulli

set_option linter.style.header false

@[expose] public section

open MeasureTheory ProbabilityTheory Measure

/- # Nonpolymorphic examples -/

universe u v

noncomputable def measureSample : Measure Bool := rdo
  let x ← bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩
  let y ← bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩
  return x + y

def pseudoSample : Rand Bool := do
  let x ← Random.randBool
  let y ← Random.randBool
  return x + y

/- # Polymorphic examples -/

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]

class HasBit (m : (α : Type) → MeasurableSpace α → Type v) where
  bit : m Bool (by infer_instance)

noncomputable instance : HasBit Measure where
  bit := bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩

instance : HasBit PseudoRandomM where
  bit := Random.randBool

def indepAnd [HasBit m] : m Bool := rdo
  let x ← HasBit.bit
  let y ← HasBit.bit
  return x && y

noncomputable def indepAndMeasure : Measure Bool := indepAnd (m := Measure)

def indepAndGen : PseudoRandomM Bool := indepAnd (m := PseudoRandomM)

variable {α : Type*} [MeasurableSpace α]

def sampleBitsArray [HasBit m] (n : ℕ) : m (Array Bool) := rdo
  let mut xs : Array Bool := #[]
  for _ in List.range n rdo
    let b ← HasBit.bit (m := m)
    xs := xs.push b
  return xs

/- # `for` over several collections

A `for` loop over several collections is expanded into a loop over the first one whose body reads
the remaining ones off a `Std.Stream` held in a mutable variable. That body has to stay part of the
surrounding `rdo` block: expanding it into a fresh `rdo` block instead puts the mutable variables
declared before the loop out of scope, and reassigning one of them is then rejected.

The loops below are run in a deterministic monad so that the tests can pin the value the loop
computes, not merely that it elaborates. -/

section MultiCollectionFor

/-- A deterministic `MeasurableSpaceMonad`, so that `rdo` programs reduce to a value. -/
abbrev IdM := Monad.toMeasurableSpaceMonad Id

/-- Read the value out of a deterministic `rdo` program. `IdM α` is definitionally `α`, but it is
not reducibly so, so the tests below go through this to state the value a loop computes. -/
def IdM.run {α : Type u} [MeasurableSpace α] (x : IdM α) : α := x

def zipDot (xs ys : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs, y in ys rdo
    s := s + x * y
  return s

example : IdM.run (zipDot [1, 2, 3] [10, 20, 30]) = 140 := rfl

/-- Iteration stops with the shorter collection, whichever one that is. -/
example : IdM.run (zipDot [1, 2, 3] [10, 20]) = 50 := rfl

example : IdM.run (zipDot [1, 2] [10, 20, 30]) = 50 := rfl

example : IdM.run (zipDot [] [10, 20]) = 0 := rfl

def zipTriple (xs ys zs : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs, y in ys, z in zs rdo
    s := s + x * y * z
  return s

example : IdM.run (zipTriple [1, 2] [3, 4] [5, 6]) = 63 := rfl

/-- `break` in the body of a loop over several collections. -/
def zipUntilZero (xs ys : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs, y in ys rdo
    if x = 0 then
      break
    s := s + y
  return s

example : IdM.run (zipUntilZero [1, 0, 1] [10, 20, 30]) = 10 := rfl

/-- `continue` in the body of a loop over several collections. -/
def zipSkipZero (xs ys : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs, y in ys rdo
    if x = 0 then
      continue
    s := s + y
  return s

example : IdM.run (zipSkipZero [1, 0, 1] [10, 20, 30]) = 40 := rfl

/-- Early `return` out of a loop over several collections. -/
def firstAgreement (xs ys : List ℕ) : IdM (Option ℕ) := rdo
  for x in xs, y in ys rdo
    if x = y then
      return some x
  return none

example : IdM.run (firstAgreement [1, 2, 3] [3, 2, 1]) = some 2 := rfl

example : IdM.run (firstAgreement [1, 2] [3, 4]) = none := rfl

/-- The collections a loop ranges over need not have the same type, nor need an `Array` be the
leading one: the collections past the first are iterated through `Std.toStream`, and an `Array`
streams as a `Subarray`, which is measurable.

The two definitions here are checked by elaborating: without `MeasurableSpace (Subarray _)` they
are rejected. Their value is not pinned the way the loops above are, because `Std.Slice`, which
`Subarray` is built from, does not reduce inside a `module` file. -/
def zipMixed (xs : List ℕ) (ys : Array Bool) : IdM ℕ := rdo
  let mut s := 0
  for x in xs, y in ys rdo
    s := s + (if y then x else 0)
  return s

def zipArrays (xs ys : Array ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs, y in ys rdo
    s := s + x * y
  return s

/-- A `Vector` leading a loop over several collections, where it is consumed by
`MeasurableSpaceForIn'`. -/
def zipVectorFirst (xs : Vector ℕ 3) (ys : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs, y in ys rdo
    s := s + x * y
  return s

example : IdM.run (zipVectorFirst #v[1, 2, 3] [10, 20, 30]) = 140 := rfl

/-- A `Vector` following one, where it streams as a `Subarray` just as an `Array` does. -/
def zipVectorSecond (xs : List ℕ) (ys : Vector ℕ 3) : IdM ℕ := rdo
  let mut s := 0
  for x in xs, y in ys rdo
    s := s + x * y
  return s

/-- The same loop shape, in a genuinely probabilistic monad. -/
noncomputable def zipBernoulli (xs ys : List Bool) : Measure Bool := rdo
  let mut acc := false
  for x in xs, y in ys rdo
    let b ← bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩
    acc := acc || (b && x && y)
  return acc

end MultiCollectionFor

end
