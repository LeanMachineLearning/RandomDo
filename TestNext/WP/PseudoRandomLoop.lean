/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

import RandomDo.RDo.Loop
import RandomDo.WP.ForIn
import RandomDo.WP.PseudoRandom
import RandomDo.WP.WithSampling
import RandomDo.Sampling.PCG64
import RandomDo.Sampling.StdGen
import Lean.Elab.Tactic.VCGen

/-!
# Stateful loop verification

The pseudorandom WP interpretation agrees definitionally with core's state interpretation,
including through named sampling wrappers. Stock `vcgen` verifies a loop that changes the
state at every iteration, proving both its return value and the final state.
-/

set_option experimental.vcgen true
set_option experimental.intrinsic true
set_option linter.privateModule false

open MeasureTheory Std.WP

namespace TestNext.WP.PseudoRandomLoop

example {σ : Type} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    {α : Type} [MeasurableSpace α] (x : PseudoRand σ α)
    (post : α → ULift σ → Prop) :
    wp x post estack⟨⟩ =
      @wp (RandGT σ Id α) α (ULift σ → Prop) EStack⟨⟩ _ _ inferInstance
        x post estack⟨⟩ := rfl

example : WPMeasurableSpaceMonad PCG64M (ULift NumLean.PCG64 → Prop) EStack⟨⟩ := inferInstance
example : WPMeasurableSpaceMonad StdGenM (ULift StdGen → Prop) EStack⟨⟩ := inferInstance

def tick : PseudoRand Nat PUnit := fun s => (⟨⟩, ⟨s.down + 1⟩)

theorem tick_spec (Q : PUnit → ULift Nat → Prop) :
    Triple tick (fun s => Q ⟨⟩ ⟨s.down + 1⟩) Q estack⟨⟩ := ⟨fun _ => id⟩

def ticks (n initial : Nat) : PseudoRand Nat Nat := rdo
  let mut remaining := n
  while remaining > 0
    invariant done => fun (s : ULift.{0} Nat) =>
      s.down + remaining = initial + n ∧ (done → remaining = 0)
    decreasing remaining
  rdo
    tick
    remaining := remaining - 1
  return remaining

example (n initial : Nat) :
    Triple (ticks n initial) (fun s => s.down = initial)
      (fun r s => r = 0 ∧ s.down = initial + n) estack⟨⟩ := by
  simp only [ticks, mBind_mPure]
  vcgen [tick_spec]
  all_goals first
    | fun_prop
    | exact measurable_fun_forInStep (measurable_of_countable _) (measurable_of_countable _)
    | grind

end TestNext.WP.PseudoRandomLoop
