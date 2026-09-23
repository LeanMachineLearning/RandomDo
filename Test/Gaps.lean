module

public import Test.Common

set_option linter.style.header false

/-!
# `rdo`: known gaps, with their current behaviour pinned

Each test below is a program `rdo` does *not* handle. The message it currently produces is pinned
with `#guard_msgs`, so that closing a gap makes the corresponding test fail and forces this file to
be revisited, rather than letting a gap close unnoticed.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace Test.Gaps

/-! ## Unbounded and conditional iteration

`while … rdo` is a loop over `Lean.Loop`, which has an instance at the core monads only.
TODO: at `Measure`, a denotation for an iteration that need not terminate: the least fixed point of
its unfolding, where the runs that never stop carry no mass. And `repeat` and `repeat … until`,
which still expand to core's `for _ in Loop.mk do …`, need `rdo` counterparts.
-/

/--
error: failed to synthesize instance of type class
  MeasurableSpaceForIn Measure Lean.Loop ?α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable def whileAtMeasure : Measure ℕ := rdo
  let mut n := 0
  let mut go := true
  while go rdo
    let b ← fairCoin
    n := n + 1
    if b then
      go := false
  return n

/--
error: failed to synthesize instance of type class
  ForIn IdM Lean.Loop ?α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def repeatLoop : IdM ℕ := rdo
  let mut i := 0
  repeat
    i := i + 1
    if 3 ≤ i then
      break
  return i

/-! ## Exceptions

TODO: needs a `MeasurableSpaceMonadExcept` class; `try`/`catch` elaborates against `MonadExcept`.
-/

/--
error: failed to synthesize instance of type class
  MeasurableSpace (Except Bool Bool)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable def tryCatch : Measure Bool := rdo
  try
    let x ← fairCoin
    return x
  catch _ =>
    return false

/-! ## Collections with no `MeasurableSpaceForIn` instance

TODO: instances exist for `List`, `Array` and `Vector` only. A range is the one most missed, since
`for i in [0:n]` has to be written `for i in List.range n` today.
-/

/--
error: failed to synthesize instance of type class
  MeasurableSpaceForIn IdM Std.Legacy.Range ?α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def overRange : IdM ℕ := rdo
  let mut s := 0
  for _ in [0:3] rdo
    s := s + 1
  return s

/--
error: failed to synthesize instance of type class
  MeasurableSpaceForIn IdM (Finset ℕ) ?α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def overFinset : IdM ℕ := rdo
  let mut s := 0
  for _ in Finset.range 3 rdo
    s := s + 1
  return s

/-! ## No `Functor`, `Applicative` or `Monad` structure

A measurable-space monad is not a monad on `Type`, which is the whole reason `rdo` exists. The
consequence inside a block is that core's operators — `<$>`, `<*>`, `<|>` — are unavailable; only
`<$>ₘ` and `>>=ₘ` are. TODO: an `mMap`-aware notation could recover `<$>`.

This one is not pinned: `Measure` does not even have the arity `Functor` expects, so the message
is an application type mismatch carrying universe metavariable numbers, which would churn on every
toolchain bump for no benefit.
-/

end Test.Gaps

end
