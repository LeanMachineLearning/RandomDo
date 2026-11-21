/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

import RandomDo.RDo

/-!
# Isolation of the polymorphic foundation

The new notation import must not pull in the original monad classes, concrete measure
semantics, or random-number implementations. These checks also catch transitive imports.
-/

assert_not_exists MeasurableSpaceMonad MeasureTheory.Measure PseudoRandomM
  MeasureTheory.PseudoRandT MeasureTheory.PseudoRand NumLean.RandPCG

-- The notation import does not require annotation wrappers or a measurable WP interpretation.
assert_not_exists MeasureTheory.WP.mForInPureWithInvariant MeasureTheory.WPMeasurableSpaceMonad

open MeasureTheory

/-- error: a loop annotation elaborates to a `vcgen` gadget;
add `import RandomDo.WP.ForIn` to use it. -/
#guard_msgs (whitespace := lax) in
set_option experimental.intrinsic true in
example {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m] : m Unit := rdo
  for _ in [1]
    invariant _ _ => True
  rdo
    mPure ()
