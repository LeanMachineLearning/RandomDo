/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import TestNext.Examples
meta import TestNext.Examples

/-!
# Regression checks for sampling interpretations

These checks exercise instance isolation, preservation and resumption of generator state,
Bernoulli boundaries, and the unit-interval conversion. All interpretations are imported together.
They test the interface and execution contracts, not statistical quality of the generators.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open MeasureTheory HasBernoulli HasUniform

namespace TestNext.Sampling

-- Both named interpretations inherit the generic measurable monad laws.
example : LawfulMeasurableSpaceMonad PCG64M := inferInstance
example : LawfulMeasurableSpaceMonad StdGenM := inferInstance

-- The surrounding block determines the primitive's monad, including for a genuine bind.
example {m : (α : Type) → [MeasurableSpace α] → Type*} [MeasurableSpaceMonad m]
    {P : Type} [HasBernoulli m P] (p : P) :
    (rdo
      let b ← bernoulli p
      return !b : m Bool) =
    MeasurableSpaceBind.mBind (bernoulli (m := m) p) (fun b => mPure (!b)) := rfl

-- Parameter-dependent sampling remains available to measurability automation.
example : Measurable (fun p : ℝ => (rdo
    let b ← bernoulli p
    return !b : Measure Bool)) := by
  fun_prop

-- A fresh tag inherits the monad infrastructure, but not another tag's sampling choices.
private inductive OtherPCG64M.Tag

private abbrev OtherPCG64M := WithSampling OtherPCG64M.Tag (PseudoRand NumLean.PCG64)

example : LawfulMeasurableSpaceMonad OtherPCG64M := inferInstance

example : True := by
  fail_if_success
    have : HasUniform OtherPCG64M Float := inferInstance
  fail_if_success
    have : HasBernoulli OtherPCG64M Float := inferInstance
  trivial

-- A deliberately constant test action makes accidental instance sharing observable.
instance : HasUniform OtherPCG64M Float := ⟨mPure 0.0⟩
instance : HasBernoulli OtherPCG64M Float := ⟨bernoulliOfUniform⟩

#guard ((bernoulli 0.5 : OtherPCG64M Bool) ⟨NumLean.mkPCG64 42⟩).1
#guard (PCG64M.runWithSeed 42 uniform).toBits ==
  ((NumLean.random (m := Id)).run ⟨NumLean.mkPCG64 42⟩).1.toBits

private def twoUniforms {m : (α : Type) → [MeasurableSpace α] → Type}
    [MeasurableSpaceMonad m] [HasUniform m Float] : m (Float × Float) := rdo
  let x ← uniform
  let y ← uniform
  return (x, y)

-- Resuming from the returned state agrees with sequencing both draws in one program.
#guard Id.run do
  let g := NumLean.mkPCG64 42
  let (x, g') := PCG64M.run uniform g
  let (y, g'') := PCG64M.run uniform g'
  let ((a, b), final) := PCG64M.run twoUniforms g
  return x.toBits == a.toBits && y.toBits == b.toBits && g'' == final && g' != g

#guard Id.run do
  let g := mkStdGen 42
  let (x, g') := StdGenM.run uniform g
  let (y, g'') := StdGenM.run uniform g'
  let ((a, b), final) := StdGenM.run twoUniforms g
  return x.toBits == a.toBits && y.toBits == b.toBits &&
    g''.s1 == final.s1 && g''.s2 == final.s2 && (g'.s1 != g.s1 || g'.s2 != g.s2)

-- Even a certain/impossible Bernoulli consumes one draw. This fixes stream alignment explicitly.
#guard Id.run do
  let g := NumLean.mkPCG64 42
  let (_, next) := PCG64M.run uniform g
  return ([-1.0, 0.0, 1.0, 2.0, Float.nan] : List Float).all fun p =>
    let (b, final) := PCG64M.run (bernoulli p) g
    b == Float.le 1.0 p && final == next

#guard Id.run do
  let g := mkStdGen 42
  let (_, next) := StdGenM.run uniform g
  return ([-1.0, 0.0, 1.0, 2.0, Float.nan] : List Float).all fun p =>
    let (b, final) := StdGenM.run (bernoulli p) g
    b == Float.le 1.0 p && final.s1 == next.s1 && final.s2 == next.s2

-- The conversion must never round up to one or produce a nonfinite value.
#guard (List.range 100).all fun seed =>
  let x := PCG64M.runWithSeed seed uniform
  let y := StdGenM.runWithSeed seed uniform
  Float.le 0.0 x && Float.lt x 1.0 && Float.le 0.0 y && Float.lt y 1.0

-- The polymorphic loop uses the selected Bernoulli instance at both probability boundaries.
#guard PCG64M.runWithSeed 42 (Examples.binomial 10 (0.0 : Float)) == 0 &&
  PCG64M.runWithSeed 42 (Examples.binomial 10 (1.0 : Float)) == 10
#guard StdGenM.runWithSeed 42 (Examples.binomial 10 (0.0 : Float)) == 0 &&
  StdGenM.runWithSeed 42 (Examples.binomial 10 (1.0 : Float)) == 10

end TestNext.Sampling
