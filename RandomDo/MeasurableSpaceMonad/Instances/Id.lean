/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Constructions
public import RandomDo.MeasurableSpaceMonad.Defs

/-!
# The identity measurable space monad

`MId` carries the measurable space of its value type and is lawful.
Its lifting laws are provided by `RandomDo.MeasurableSpaceMonad.Lift`.
-/

@[expose] public section

namespace MeasureTheory

/-- The identity measurable space monad. -/
abbrev MId := Monad.toMeasurableSpaceMonad _root_.Id

instance {α : Type*} [MeasurableSpace α] : MeasurableSpace (MId α) :=
  inferInstanceAs (MeasurableSpace α)

instance : LawfulMeasurableSpaceMonad MId where
  mMap_const := rfl
  id_mMap _ := rfl
  measurable_mPure {_} _ := measurable_id
  measurable_mBind hf := hf
  mBind_mPure_comp _ _ := rfl
  mPure_mBind _ _ _ := rfl
  mBind_assoc _ _ _ _ _ := rfl

end MeasureTheory
