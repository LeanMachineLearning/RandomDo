module

public import Test.Common

set_option linter.style.header false

/-!
# `rdo`: binding, sequencing and `return`

`rdo` elaborates to `MeasurableSpacePure.mPure` and `MeasurableSpaceBind.mBind` rather than to
`pure` and `bind`, so every shape a `do` block can take has to be re-checked here.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace Test.Bind

/-- A single bind. -/
def one (xs : List ℕ) : IdM ℕ := rdo
  let x ← (xs.headD 0 : IdM ℕ)
  return x + 1

example : IdM.run (one [4, 5]) = 5 := rfl

/-- A chain of binds. -/
def chain (a b : ℕ) : IdM ℕ := rdo
  let x ← (a : IdM ℕ)
  let y ← (b : IdM ℕ)
  return x * y

example : IdM.run (chain 6 7) = 42 := rfl

/-- `←` nested inside a larger expression is lifted out of it. -/
def nested (a b : ℕ) : IdM ℕ := rdo
  return (← (a : IdM ℕ)) + (← (b : IdM ℕ)) * 2

example : IdM.run (nested 3 4) = 11 := rfl

/-- A pure `let`, and a `have`, alongside the monadic ones. -/
def mixedLets (a : ℕ) : IdM ℕ := rdo
  let x ← (a : IdM ℕ)
  let y := x + 1
  have : 0 < y + 1 := Nat.succ_pos y
  return y * 2

example : IdM.run (mixedLets 5) = 12 := rfl

/-- Destructuring a bound pair. -/
def destructure (p : ℕ × ℕ) : IdM ℕ := rdo
  let (a, b) ← (p : IdM (ℕ × ℕ))
  return a + b

example : IdM.run (destructure (3, 4)) = 7 := rfl

/-- A statement in the middle of a block is sequenced, not dropped. -/
def sequenced (a : ℕ) : IdM ℕ := rdo
  let mut s := 0
  (pure () : IdM PUnit)
  s := s + a
  return s

example : IdM.run (sequenced 9) = 9 := rfl

/-- `return` in straight-line code drops the rest of the block. -/
def earlyReturn (a : ℕ) : IdM ℕ := rdo
  if a = 0 then
    return 100
  return a

example : IdM.run (earlyReturn 0) = 100 := rfl

example : IdM.run (earlyReturn 7) = 7 := rfl

/-- The same shapes at `Measure`, where the binds are genuine integrals. -/
noncomputable def twoCoins : Measure Bool := rdo
  let x ← fairCoin
  let y ← fairCoin
  return x && y

end Test.Bind

end
