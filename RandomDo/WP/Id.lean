/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.Instances.Id
public import RandomDo.WP.MeasurableSpaceMonad
public import Std.WP.Monad.Instances

/-!
# Weakest preconditions of pure computations

`MId` uses core's `Id` interpretation: a computation satisfies a postcondition exactly when
its result does. This also supplies the base interpretation for `PseudoRand`.
-/

@[expose] public section

open MeasureTheory Lean.Order

namespace Std.WP

#check Std.WP.Id.instWPMonad

instance : WPMeasurableSpaceMonad MId Prop EStack⟨⟩ where
  toWP _ := inferInstanceAs (WP (Id _) _ Prop EStack⟨⟩)
  measurable_wp hpost _ := hpost
  mPure_le_wp_mPure _ _ _ _ := PartialOrder.rel_refl
  mBind_le_wp_mBind _ _ _ _ _ _ := PartialOrder.rel_refl

end Std.WP
