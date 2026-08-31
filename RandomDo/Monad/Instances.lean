/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Monad.MeasurableSpace
public import Mathlib.Probability.ProductMeasure

/-!
# Instances for `MeasurableSpaceMonad`

**TODO**

-/

@[expose] public section

universe u v w

/-- A (core) monad automatically defines a (not necessarily lawful) measurable space monad by
forgetting the measurable space argument. -/
def Monad.toMeasurableSpaceMonad (m : Type u → Type v) (α : Type u) [_mα : MeasurableSpace α] :
    Type v := m α

instance {m : Type u → Type v} [Monad m] :
    MeasurableSpaceMonad (Monad.toMeasurableSpaceMonad m) where
  mPure := pure
  mBind := bind

/-- A measurable space monad for pseudo random number generation. -/
abbrev PseudoRandomM := Monad.toMeasurableSpaceMonad Rand

open MeasureTheory

open MeasurableSpacePure MeasurableSpaceBind MeasurableSpaceFunctor MeasurableSpaceMonad

@[simps]
noncomputable instance : MeasurableSpaceMonad Measure where
  mPure := Measure.dirac
  mBind := Measure.bind

instance : LawfulMeasurableSpaceMonad Measure where
  mMap_const := by simp [mMapConst, mMap]
  id_mMap μ := by simp [mMap]
  measurable_mPure := by unfold mPure; fun_prop
  measurable_mBind := by unfold mBind; fun_prop
  mBind_mPure_comp _ _ := by rfl
  mPure_mBind x _ hf := Measure.dirac_bind hf x
  mBind_assoc _ _ _ hf hg := Measure.bind_bind hf.aemeasurable hg.aemeasurable

section RandomM

open Function

/-- A monad for random number generation. -/
structure RandomM (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω)
    (α : Type u) [MeasurableSpace α] where
  /-- Draws a value from a state of the source of randomness, and hands back the state left for the
  next draw. -/
  sample : Ω → α × Ω
  measurePreserving : MeasurePreserving sample P ((Measure.map (Prod.fst ∘ sample) P).prod P)

/-- TODO -/
abbrev SampleM (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω) :=
  RandomM (ℕ → Ω) (Measure.infinitePi fun _ : ℕ ↦ P)

end RandomM
