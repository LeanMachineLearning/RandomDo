module

public import Test.Common

set_option linter.style.header false

/-!
# `rdo`: branching

Every branching `do` element goes through core's elaborators, which build the block out of the
`DoOps` that `rdo` supplies. Each shape is checked here to make sure the substituted `mPure` and
`mBind` reach it.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace Test.Control

/-- `if … then … else`, branching the whole rest of the block. -/
def branch (n : ℕ) : IdM ℕ := rdo
  if n = 0 then
    return 100
  else
    return n

example : IdM.run (branch 0) = 100 := rfl

example : IdM.run (branch 5) = 5 := rfl

/-- `if` with no `else`: the block carries on afterwards. -/
def clampZero (n : ℕ) : IdM ℕ := rdo
  let mut s := n
  if n = 0 then
    s := 100
  return s

example : IdM.run (clampZero 0) = 100 := rfl

example : IdM.run (clampZero 5) = 5 := rfl

/-- Nested branches. -/
def nestedIf (a b : ℕ) : IdM ℕ := rdo
  if a = 0 then
    if b = 0 then
      return 0
    else
      return 1
  else
    return 2

example : IdM.run (nestedIf 0 0) = 0 := rfl

example : IdM.run (nestedIf 0 1) = 1 := rfl

example : IdM.run (nestedIf 1 0) = 2 := rfl

/-- A dependent `if`, whose branch uses the proof it introduces. -/
def headOr (xs : List ℕ) : IdM ℕ := rdo
  if h : 0 < xs.length then
    return xs[0]'h
  else
    return 0

example : IdM.run (headOr [7, 8]) = 7 := rfl

example : IdM.run (headOr []) = 0 := rfl

/-- A `match` on a value bound by `←`. -/
def matchArrow (o : Option ℕ) : IdM ℕ := rdo
  match ← (o : IdM (Option ℕ)) with
  | none => return 0
  | some n => return n + 1

example : IdM.run (matchArrow (some 4)) = 5 := rfl

example : IdM.run (matchArrow none) = 0 := rfl

/-- A pure `match` inside the block. -/
def matchPure (o : Option ℕ) : IdM ℕ := rdo
  let v ← (o : IdM (Option ℕ))
  match v with
  | none => return 0
  | some n => return n + 1

example : IdM.run (matchPure (some 4)) = 5 := rfl

/-- `if let`. -/
def ifLet (o : Option ℕ) : IdM ℕ := rdo
  let v ← (o : IdM (Option ℕ))
  if let some n := v then
    return n + 1
  else
    return 0

example : IdM.run (ifLet (some 4)) = 5 := rfl

example : IdM.run (ifLet none) = 0 := rfl

/-- `unless`. -/
def unlessFlag (b : Bool) : IdM ℕ := rdo
  let mut s := 0
  unless b do
    s := 1
  return s

example : IdM.run (unlessFlag true) = 0 := rfl

example : IdM.run (unlessFlag false) = 1 := rfl

/-- Branching on a value drawn from a genuine distribution. -/
noncomputable def fairCoinBranch : Measure ℕ := rdo
  let b ← fairCoin
  if b then
    return 1
  else
    return 0

end Test.Control

end
