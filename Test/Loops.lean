module

public import Test.Common
meta import Test.Common
public import Std.Tactic.Do

set_option linter.style.header false
set_option linter.hashCommand false

/-!
# `rdo`: `for` and `while` loops

`rdo` has its own `for … rdo …` parser, expander and elaborator, mirroring core's but emitting
`MeasurableSpaceForIn.forIn`. Instances exist for `List`, `Array` and `Vector`, and for `Lean.Loop`,
which `while … rdo` loops over, at the core monads.

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

/-! ## `while` loops

`while c rdo body` is a loop over `Lean.Loop`, as in core. At a core monad it is core's loop, which
the kernel cannot unfold, so these programs are checked with `#guard` rather than `rfl`, and proved
through `mvcgen`. There is no instance at `Measure` yet.
-/

/-- A `while` loop, counting down from `n`. -/
def countdown (n : ℕ) : IdM ℕ := rdo
  let mut i := n
  let mut steps := 0
  while 0 < i rdo
    i := i - 1
    steps := steps + 1
  return steps

#guard IdM.run (countdown 5) = 5

#guard IdM.run (countdown 0) = 0

open Std.Do in
set_option mvcgen.warning false in
theorem countdown_eq (n : ℕ) : IdM.run (countdown n) = n := by
  generalize h : IdM.run (countdown n) = r
  apply Id.of_wp_run_eq h
  simp only [countdown, MeasurableSpaceForIn.forIn, MeasurableSpaceBind.mBind,
    MeasurableSpacePure.mPure]
  dsimp only [IdM, Monad.toMeasurableSpaceMonad]
  mvcgen invariants
  · fun st => ⟨st.1⟩
  · ⇓ c => match c with
      | .inl st => ⌜st.1 + st.2 = n⌝
      | .inr st => ⌜st.2 = n⌝
  all_goals simp_all <;> omega

/-- `break` out of a `while` loop. -/
def halveUntilOdd (n : ℕ) : IdM ℕ := rdo
  let mut k := n
  while 0 < k rdo
    if k % 2 = 1 then
      break
    k := k / 2
  return k

#guard IdM.run (halveUntilOdd 24) = 3

#guard IdM.run (halveUntilOdd 0) = 0

/-- An early `return` out of a `while` loop. -/
def firstSquareAbove (n : ℕ) : IdM ℕ := rdo
  let mut k := 0
  while true rdo
    if k * k > n then
      return k
    k := k + 1
  return 0

#guard IdM.run (firstSquareAbove 10) = 4

/-- `while let`, consuming a list one element at a time. -/
def sumByPopping (xs : List ℕ) : IdM ℕ := rdo
  let mut rest := xs
  let mut s := 0
  while let x :: xs' := rest rdo
    s := s + x
    rest := xs'
  return s

#guard IdM.run (sumByPopping [1, 2, 3]) = 6

/-- `while h : c`, which hands the body a proof of the condition. -/
def countdownWithProof (n : ℕ) : IdM ℕ := rdo
  let mut i := n
  let mut steps := 0
  while h : 0 < i rdo
    have : i - 1 < i := Nat.sub_lt h Nat.one_pos
    i := i - 1
    steps := steps + 1
  return steps

#guard IdM.run (countdownWithProof 4) = 4

/-- A `while` loop nested inside a `for` loop. -/
def sumOfLogs (xs : List ℕ) : IdM ℕ := rdo
  let mut s := 0
  for x in xs rdo
    let mut k := x
    while 1 < k rdo
      k := k / 2
      s := s + 1
  return s

#guard IdM.run (sumOfLogs [1, 2, 8]) = 4

end Test.Loops

end
