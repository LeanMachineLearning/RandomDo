module

public import Test.Common

set_option linter.style.header false

/-!
# `rdo`: `for` loops over a single collection

`rdo` has its own `for … rdo …` parser, expander and elaborator, mirroring core's but emitting
`MeasurableSpaceForIn.forIn`. Instances exist for `List`, `Array` and `Vector`.

There is no test for a loop nested inside another: `rdoFor` has no registered `ControlInfo`
inference handler, so the outer loop cannot work out what the inner one does to the control flow,
and such a program is rejected before elaboration.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace Test.Loops

/-- A loop over a `List`. -/
def sumList (xs : List ℕ) : MId ℕ := rdo
  let mut s := 0
  for x in xs rdo
    s := s + x
  return s

example : Id.run (sumList [1, 2, 3]) = 6 := rfl

example : Id.run (sumList []) = 0 := rfl

/-- A loop over an `Array`. -/
def sumArray (xs : Array ℕ) : MId ℕ := rdo
  let mut s := 0
  for x in xs rdo
    s := s + x
  return s

example : Id.run (sumArray #[1, 2, 3]) = 6 := rfl

/-- A loop over a `Vector`. -/
def sumVector (xs : Vector ℕ 3) : MId ℕ := rdo
  let mut s := 0
  for x in xs rdo
    s := s + x
  return s

example : Id.run (sumVector #v[1, 2, 3]) = 6 := rfl

/-- `for h : x in xs`, which hands the body a proof that `x` is in the collection. -/
def sumWithProof (xs : List ℕ) : MId ℕ := rdo
  let mut s := 0
  for h : x in xs rdo
    have : x ∈ xs := h
    s := s + x
  return s

example : Id.run (sumWithProof [1, 2, 3]) = 6 := rfl

/-- Several mutable variables carried through one loop. -/
def sumAndCount (xs : List ℕ) : MId (ℕ × ℕ) := rdo
  let mut s := 0
  let mut n := 0
  for x in xs rdo
    s := s + x
    n := n + 1
  return (s, n)

example : Id.run (sumAndCount [1, 2, 3]) = (6, 3) := rfl

/-- `break`. -/
def sumUntilZero (xs : List ℕ) : MId ℕ := rdo
  let mut s := 0
  for x in xs rdo
    if x = 0 then
      break
    s := s + x
  return s

example : Id.run (sumUntilZero [1, 2, 0, 4]) = 3 := rfl

example : Id.run (sumUntilZero [1, 2, 3]) = 6 := rfl

/-- `continue`. -/
def sumSkippingZero (xs : List ℕ) : MId ℕ := rdo
  let mut s := 0
  for x in xs rdo
    if x = 0 then
      continue
    s := s + x
  return s

example : Id.run (sumSkippingZero [1, 0, 3]) = 4 := rfl

/-- An early `return` out of a loop, which elaborates through `Break.runK`. -/
def firstNonzero (xs : List ℕ) : MId (Option ℕ) := rdo
  for x in xs rdo
    if x ≠ 0 then
      return some x
  return none

example : Id.run (firstNonzero [0, 0, 3, 4]) = some 3 := rfl

example : Id.run (firstNonzero [0, 0]) = none := rfl

/-- An early `return` from a loop that also carries mutable state. -/
def runningSumOver (xs : List ℕ) (limit : ℕ) : MId ℕ := rdo
  let mut s := 0
  for x in xs rdo
    s := s + x
    if s > limit then
      return s
  return 0

example : Id.run (runningSumOver [1, 2, 3, 4] 4) = 6 := rfl

example : Id.run (runningSumOver [1, 2] 100) = 0 := rfl

/-- A loop with no mutable state, whose only effect is an early return. -/
def containsZero (xs : List ℕ) : MId Bool := rdo
  for x in xs rdo
    if x = 0 then
      return true
  return false

example : Id.run (containsZero [1, 0]) = true := rfl

example : Id.run (containsZero [1, 2]) = false := rfl

/-- A loop whose body binds monadically, at `Measure`. -/
noncomputable def countHeads (n : ℕ) : Measure ℕ := rdo
  let mut c := 0
  for _ in List.range n rdo
    let b ← fairCoin
    if b then
      c := c + 1
  return c

end Test.Loops

end
