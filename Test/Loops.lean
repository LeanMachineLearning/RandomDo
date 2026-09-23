module

public import Test.Common

set_option linter.style.header false

/-!
# `rdo`: `for` loops over a single collection

`rdo` has its own `for … rdo …` parser, expander and elaborator, mirroring core's but emitting
`MeasurableSpaceForIn.forIn`. Instances exist for `List`, `Array` and `Vector`.

A loop can sit under another construct, including another loop: the enclosing one learns what the
loop does to the control flow from the `ControlInfo` handler of `rdoFor`, which is that of core's
`for` loop with the same body.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace Test.Loops

/-- A loop over a `List`. -/
def sumList (xs : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    s := s + x
  return s

example : IdM.run (sumList [1, 2, 3]) = 6 := rfl

example : IdM.run (sumList []) = 0 := rfl

/-- A loop over an `Array`. -/
def sumArray (xs : Array ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    s := s + x
  return s

example : IdM.run (sumArray #[1, 2, 3]) = 6 := rfl

/-- A loop over a `Vector`. -/
def sumVector (xs : Vector ℕ 3) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    s := s + x
  return s

example : IdM.run (sumVector #v[1, 2, 3]) = 6 := rfl

/-- `for h : x in xs`, which hands the body a proof that `x` is in the collection. -/
def sumWithProof (xs : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for h : x in xs rdo
    have : x ∈ xs := h
    s := s + x
  return s

example : IdM.run (sumWithProof [1, 2, 3]) = 6 := rfl

/-- Several mutable variables carried through one loop. -/
def sumAndCount (xs : List ℕ) : IdM (ℕ × ℕ) := rdo
  let mut s := 0
  let mut n := 0
  for x in xs rdo
    s := s + x
    n := n + 1
  return (s, n)

example : IdM.run (sumAndCount [1, 2, 3]) = (6, 3) := rfl

/-- `break`. -/
def sumUntilZero (xs : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    if x = 0 then
      break
    s := s + x
  return s

example : IdM.run (sumUntilZero [1, 2, 0, 4]) = 3 := rfl

example : IdM.run (sumUntilZero [1, 2, 3]) = 6 := rfl

/-- `continue`. -/
def sumSkippingZero (xs : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    if x = 0 then
      continue
    s := s + x
  return s

example : IdM.run (sumSkippingZero [1, 0, 3]) = 4 := rfl

/-- An early `return` out of a loop, which elaborates through `Break.runK`. -/
def firstNonzero (xs : List ℕ) : IdM (Option ℕ) := rdo
  for x in xs rdo
    if x ≠ 0 then
      return some x
  return none

example : IdM.run (firstNonzero [0, 0, 3, 4]) = some 3 := rfl

example : IdM.run (firstNonzero [0, 0]) = none := rfl

/-- An early `return` from a loop that also carries mutable state. -/
def runningSumOver (xs : List ℕ) (limit : ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    s := s + x
    if s > limit then
      return s
  return 0

example : IdM.run (runningSumOver [1, 2, 3, 4] 4) = 6 := rfl

example : IdM.run (runningSumOver [1, 2] 100) = 0 := rfl

/-- A loop with no mutable state, whose only effect is an early return. -/
def containsZero (xs : List ℕ) : IdM Bool := rdo
  for x in xs rdo
    if x = 0 then
      return true
  return false

example : IdM.run (containsZero [1, 0]) = true := rfl

example : IdM.run (containsZero [1, 2]) = false := rfl

/-- A loop whose body binds monadically, at `Measure`. -/
noncomputable def countHeads (n : ℕ) : Measure ℕ := rdo
  let mut c := 0
  for _ in List.range n rdo
    let b ← fairCoin
    if b then
      c := c + 1
  return c

/-! ## Loops under other constructs -/

/-- A loop nested inside another, reassigning a variable of the enclosing block. -/
def nestedLoops (xs ys : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    for y in ys rdo
      s := s + x * y
  return s

example : IdM.run (nestedLoops [1, 2] [3, 4]) = 21 := rfl

example : IdM.run (nestedLoops [1, 2] []) = 0 := rfl

/-- `break` in the inner loop leaves the inner loop only. -/
def innerBreak (xs ys : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    for y in ys rdo
      if y = 0 then
        break
      s := s + x * y
  return s

example : IdM.run (innerBreak [1, 2] [3, 0, 5]) = 9 := rfl

/-- `continue` in the inner loop skips to the next inner iteration. -/
def innerContinue (xs ys : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    for y in ys rdo
      if y = 0 then
        continue
      s := s + x * y
  return s

example : IdM.run (innerContinue [1, 2] [3, 0, 5]) = 24 := rfl

/-- An early `return` in the inner loop leaves the whole program. -/
def firstProductOver (xs ys : List ℕ) (limit : ℕ) : IdM ℕ := rdo
  for x in xs rdo
    for y in ys rdo
      if x * y > limit then
        return x * y
  return 0

example : IdM.run (firstProductOver [1, 2, 3] [1, 2] 3) = 4 := rfl

example : IdM.run (firstProductOver [1, 2] [1, 2] 10) = 0 := rfl

/-- An inner loop over several collections, which the expander rewrites first. -/
def nestedZip (xs ys zs : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    for y in ys, z in zs rdo
      s := s + x * y * z
  return s

example : IdM.run (nestedZip [1, 2] [1, 2] [3, 4]) = 33 := rfl

/-- A loop in a branch of an `if`. -/
def sumIf (b : Bool) (xs : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  if b then
    for x in xs rdo
      s := s + x
  return s

example : IdM.run (sumIf true [1, 2, 3]) = 6 := rfl

example : IdM.run (sumIf false [1, 2, 3]) = 0 := rfl

/-- A loop in an arm of a `match`. -/
def sumHead (xss : List (List ℕ)) : IdM ℕ := rdo
  let mut s := 0
  match xss with
  | [] => pure ()
  | xs :: _ =>
    for x in xs rdo
      s := s + x
  return s

example : IdM.run (sumHead [[1, 2], [10]]) = 3 := rfl

example : IdM.run (sumHead []) = 0 := rfl

/-- Nested loops whose body binds monadically, at `Measure`. -/
noncomputable def countPairsOfHeads (n : ℕ) : Measure ℕ := rdo
  let mut c := 0
  for _ in List.range n rdo
    for _ in List.range n rdo
      let b ← fairCoin
      if b then
        c := c + 1
  return c

end Test.Loops

end
