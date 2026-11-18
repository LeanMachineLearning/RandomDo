/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.RDo.Loop
public import RandomDo.MeasurableSpaceMonad.Instances.Id
public import RandomDo.Sampling.PCG64
public import RandomDo.Sampling.StdGen
public import RandomDo.WP.ForIn

/-!
# Loop interpretation and control-flow regressions

A genuinely polymorphic sampler specializes to core's loop, including through the named RNG
wrappers. The equalities check the logical definitions; the guards check values and final state.
The control-flow and post-test examples also serve as generated-C comparisons against core.
The break-free example is only elaborated and proved equal, never executed.
-/

set_option linter.hashCommand false
set_option experimental.intrinsic true

@[expose] public section

open MeasureTheory

namespace TestNext.RDo.While
universe v

def untilHeads {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] [MeasurableSpaceForIn m Lean.Loop Unit] (coin : m Bool) : m Nat := rdo
  let mut draws := 0
  repeat rdo
    let b ← coin
    draws := draws + 1
    if b then break
  return draws

def untilHeadsDo {m : Type → Type v} [Monad m] (coin : m Bool) : m Nat := do
  let mut draws := 0
  repeat
    let b ← coin
    draws := draws + 1
    if b then break
  return draws

example {m : Type → Type v} [Monad m] (coin : m Bool) :
    untilHeads (m := Monad.toMeasurableSpaceMonad m) coin = untilHeadsDo coin := rfl

def everyThird : PseudoRand Nat Bool := fun s => (decide (s.down % 3 = 2), ⟨s.down + 1⟩)
def sampledRDo (seed : Nat) : Nat × Nat :=
  let (n, s) := (untilHeads (m := PseudoRand Nat) everyThird).run ⟨seed⟩
  (n, s.down)
def sampledDo (seed : Nat) : Nat × Nat :=
  let (n, s) := (untilHeadsDo (m := RandGT Nat Id) everyThird).run ⟨seed⟩
  (n, s.down)
example : sampledRDo = sampledDo := rfl
#guard sampledRDo 0 == (3, 3)
#guard sampledRDo 4 == (2, 6)

-- `continue` must jump to the test of the next iteration; early return must escape the loop.
def controlRDo (fuel : Nat) : MId Nat := rdo
  let mut i := fuel
  while i > 0 rdo
    i := i - 1
    if i = 3 then continue
    if i = 1 then return 17
  return i

def controlDo (fuel : Nat) : Id Nat := do
  let mut i := fuel
  while i > 0 do
    i := i - 1
    if i = 3 then continue
    if i = 1 then return 17
  return i
example : controlRDo = controlDo := rfl
#guard (controlRDo 5).run == 17
#guard (controlRDo 1).run == 0

def postTestRDo (fuel : Nat) : MId Nat := rdo
  let mut i := fuel
  repeat rdo
    i := i - 1
  until i = 0
  return i

def postTestDo (fuel : Nat) : Id Nat := do
  let mut i := fuel
  repeat
    i := i - 1
  until i = 0
  return i
example : postTestRDo = postTestDo := rfl
#guard (postTestRDo 5).run == 0

-- An annotation must not cause core's repeat parser to consume the enclosing continuation.
def annotatedRepeatRDo (x : Nat) : MId Nat := rdo
  let mut y := x
  repeat rdo
    invariant _ => True
    do
      y := y + 1
      break
  return y

def annotatedRepeatDo (x : Nat) : Id Nat := do
  let mut y := x
  repeat
    invariant _ => True
    do
      y := y + 1
      break
  return y

example : annotatedRepeatRDo = annotatedRepeatDo := rfl
#guard (annotatedRepeatRDo 4).run == 5

-- The same polymorphic program reaches core's implementation through the named sampling tag.
example (coin : PCG64M Bool) :
    untilHeads coin = untilHeadsDo (m := RandGT NumLean.PCG64 Id) coin := rfl

example (coin : StdGenM Bool) :
    untilHeads coin = untilHeadsDo (m := RandGT StdGen Id) coin := rfl

-- This checks elaboration of a non-Unit, break-free loop without executing it.
def spin {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] [MeasurableSpaceForIn m Lean.Loop Unit] : m Nat := rdo
  repeat rdo
    mPure ()

def spinDo {m : Type → Type v} [Monad m] : m Nat := do
  repeat
    pure ()

example {m : Type → Type v} [Monad m] :
    spin (m := Monad.toMeasurableSpaceMonad m) = spinDo (m := m) := rfl

end TestNext.RDo.While
