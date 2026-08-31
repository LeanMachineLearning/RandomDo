module

public import Test.Common

set_option linter.style.header false

/-!
# `rdo`: the monad instances, and programs polymorphic over them

The point of `MeasurableSpaceMonad` is that one `rdo` program can be read both as a distribution
and as a sampler. These tests write a program once and interpret it at each instance the library
provides.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace Test.Instances

universe u

/-! ## What `rdo` elaborates to at `Measure` -/

example {α : Type} [MeasurableSpace α] (a : α) :
    (MeasurableSpacePure.mPure a : Measure α) = Measure.dirac a := rfl

example {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → Measure β) : μ >>=ₘ f = μ.bind f := rfl

/-- An `rdo` program is the explicit `bind`/`dirac` term one would write by hand. -/
noncomputable def flip : Measure Bool := rdo
  let x ← fairCoin
  return !x

example : flip = fairCoin.bind (fun x ↦ Measure.dirac (!x)) := rfl

/-! ## One program, several interpretations -/

variable {m : (α : Type) → [MeasurableSpace α] → Type u} [MeasurableSpaceMonad m]

/-- A program that draws twice from the same source and adds the results. -/
def twice (x : m ℕ) : m ℕ := rdo
  let a ← x
  let b ← x
  return a + b

/-- At `IdM` it computes. -/
example : IdM.run (twice ((3 : ℕ) : IdM ℕ)) = 6 := rfl

/-- At `Measure` it denotes a distribution. -/
noncomputable def twiceCoin : Measure ℕ := twice (m := Measure) (rdo
  let b ← fairCoin
  return (if b then 1 else 0))

/-- At `PseudoRandomM` it is an executable sampler. -/
def twiceRandom : PseudoRandomM ℕ := twice (m := PseudoRandomM) (rdo
  let b ← Random.randBool
  return (if b then 1 else 0))

/-- A polymorphic program containing a loop. -/
def sumOver (xs : List ℕ) (f : ℕ → m ℕ) : m ℕ := rdo
  let mut s := 0
  for x in xs rdo
    let y ← f x
    s := s + y
  return s

example : IdM.run (sumOver [1, 2, 3] (fun x ↦ ((x * 2 : ℕ) : IdM ℕ))) = 12 := rfl

noncomputable def sumOverMeasure : Measure ℕ :=
  sumOver (m := Measure) [1, 2, 3] (fun x ↦ rdo
    let b ← fairCoin
    return (if b then x else 0))

def sumOverRandom : PseudoRandomM ℕ :=
  sumOver (m := PseudoRandomM) [1, 2, 3] (fun x ↦ rdo
    let b ← Random.randBool
    return (if b then x else 0))

end Test.Instances

end
