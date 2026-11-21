/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom
public import RandomDo.WP.Id

/-!
# Weakest preconditions of pseudorandom computations

`PseudoRandT σ m` lifts the weakest-precondition interpretation of its base monad to predicates
on the generator state. It follows core's `StateT` interpretation: the postcondition receives
both the returned value and the final state. For `PseudoRand`, this is definitionally core's
interpretation of `RandGT σ Id`.

The state is countable with measurable singletons, as in the lawful measurable monad instance.
These assumptions ensure that a measurable state-indexed postcondition can be evaluated at
the state returned by the computation. They do not change execution or the logical loop model.
-/

@[expose] public section

open Lean.Order Std.WP

namespace MeasureTheory

universe u v w w'

-- These combine core's state interpretation and its monad laws. The adapted base monad
-- supplies the WP interpretation and measurable spaces on its outputs. Countable state with
-- measurable singletons makes evaluation at a varying state measurable, just as in the
-- existing lawful instance for `PseudoRandT`.
#check Std.WP.StateT.wpInst
#check Std.WP.StateT.instWPMonad

instance {σ : Type} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    {m : Type u → Type v} [Monad m]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (Monad.toMeasurableSpaceMonad m α)]
    {Pred : Type w} {EPred : Type w'} [Assertion Pred] [MeasurableSpace Pred] [Assertion EPred]
    [WPMeasurableSpaceMonad (Monad.toMeasurableSpaceMonad m) Pred EPred] :
    WPMeasurableSpaceMonad (PseudoRandT σ m) (ULift σ → Pred) EPred where
  toWP α :=
    { wpTrans := fun x => PredTrans.pushArg (fun s =>
        WP.wpTrans (Prog := Monad.toMeasurableSpaceMonad m (α × ULift σ)) (x.run s))
      wp_trans_monotone := fun x _ _ _ _ hepost hpost s =>
        WP.wp_consequence_econs (Prog := Monad.toMeasurableSpaceMonad m (α × ULift σ))
          (x := x.run s)
          _ _ _ _ (fun p => hpost p.1 p.2) hepost }
  measurable_wp {α} _ {_} hpost epost := Measurable.of_eval fun s =>
    (WPMeasurableSpaceMonad.measurable_wp (m := Monad.toMeasurableSpaceMonad m)
      hpost.uncurry epost).comp
        (measurable_pi_apply (X := fun _ : ULift σ =>
          Monad.toMeasurableSpaceMonad m (α × ULift σ)) s)
  mPure_le_wp_mPure a post epost hpost s :=
    WPMeasurableSpaceMonad.mPure_le_wp_mPure (m := Monad.toMeasurableSpaceMonad m)
      (a, s) (fun p => post p.1 p.2) epost hpost.uncurry
  mBind_le_wp_mBind x f post epost hf hpost s :=
    WPMeasurableSpaceMonad.mBind_le_wp_mBind (m := Monad.toMeasurableSpaceMonad m)
      (x.run s) (fun p => (f p.1).run p.2) (fun p => post p.1 p.2) epost
        (by fun_prop) hpost.uncurry

end MeasureTheory
