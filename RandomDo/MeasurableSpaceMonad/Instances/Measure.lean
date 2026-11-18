/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.Defs
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The measurable space monad of measures

**PLACEHOLDER: module documentation.** The monad and lawfulness instances below are implemented.

-/

@[expose] public section

namespace MeasureTheory

@[simps]
noncomputable instance : MeasurableSpaceMonad Measure where
  mPure := Measure.dirac
  mBind := Measure.bind

instance : LawfulMeasurableSpaceMonad Measure where
  mMap_const := by simp [mMapConst, mMap]
  id_mMap μ := by simp [mMap]
  measurable_mPure := by unfold mPure; fun_prop
  measurable_mBind := by unfold mBind; fun_prop
  mBind_mPure_comp _ _ := rfl
  mPure_mBind x _ hf := Measure.dirac_bind hf x
  mBind_assoc _ _ _ hf hg := Measure.bind_bind hf.aemeasurable hg.aemeasurable

end MeasureTheory
