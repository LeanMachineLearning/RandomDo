/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDo.MeasurableSpaceMonad.Lift
import RandomDo.MeasurableSpaceMonad.Instances.Measure
import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom

/-!
# Lifting inference, laws, and measurable intermediate results

Two direct lifting instances must compose without an explicit intermediate monad. The measure
example checks that lifting an ordinary value and binding a measurable handler preserves the
handler's result using the supplied source space. The lawful cases
check composition of direct lawful lifts and measurability through the public alias.
Direct-lift measurability and the precedence of native lifts over the core fallback are also
checked. Explicit lifting functions must supply both algebraic laws and measurability to the
existing lifting API, and the mixed-source helper must still allow different universes.
-/

set_option linter.privateModule false

open MeasureTheory

namespace TestNext.MeasurableSpaceMonad.Lift

private structure Source (α : Type) [MeasurableSpace α] where
  value : α

private structure Middle (α : Type) [MeasurableSpace α] where
  value : α
  path : List Nat

private structure Target (α : Type) [MeasurableSpace α] where
  value : α
  path : List Nat

local instance : MeasurableSpaceMonadLift Source Middle where
  mMonadLift x := ⟨x.value, [1]⟩

local instance : MeasurableSpaceMonadLift Middle Target where
  mMonadLift x := ⟨x.value, x.path ++ [2]⟩

example {α : Type} [MeasurableSpace α] (a : α) :
    mMonadLift (m := Source) (n := Target) ⟨a⟩ = ⟨a, [1, 2]⟩ := rfl

example {α : Type} [MeasurableSpace α] (x : Target α) :
    mMonadLift (m := Target) (n := Target) x = x := rfl

-- Lifting an ordinary value uses its supplied space, including non-discrete spaces.
example {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (a : α) (f : α → Measure β) (hf : Measurable f) :
    (mMonadLift (m := MId) (n := Measure) a >>=ₘ f) = f a := by
  exact Internal.LawfulMeasurableSpaceMonadLiftBindFunction.liftBind_mPure
    (m := MId) (n := Measure)
    (liftBind := fun _ _ _ _ f x =>
      mMonadLift (m := MId) (n := Measure) x >>=ₘ f) f a hf

-- The helper also supports a genuinely measurable source monad, without a core `Monad`.
example {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (f : α → Measure β) (g : β → Measure γ)
    (hf : Measurable f) (hg : Measurable g) :
    ((μ >>=ₘ f) >>=ₘ g) = μ >>=ₘ (fun a => f a >>=ₘ g) := by
  exact Internal.LawfulMeasurableSpaceMonadLiftBindFunction.liftBind_mBind
    (m := Measure) (n := Measure) (liftBind := fun _ _ _ _ f x => x >>=ₘ f) g μ f hg hf

-- The alias must use measurable lifting, including for targets without a core `Monad` instance.
example (a : Nat) :
    mLiftM (m := Measure) (n := Measure) (Measure.dirac a) = Measure.dirac a := rfl

-- The generic Id lift must be lawful for the measure interpretation.
example : LawfulMeasurableSpaceMonadLiftT MId Measure :=
  inferInstance

-- A non-Id base exercises the transformer instance rather than the generic Id lift.
example : LawfulMeasurableSpaceMonadLiftT (PseudoRand Bool)
    (PseudoRandT Nat (RandGT Bool Id)) := inferInstance

section Lawful

universe u v w z

variable {m : (α : Type u) → [MeasurableSpace α] → Type v}
  {n : (α : Type u) → [MeasurableSpace α] → Type w}
  {o : (α : Type u) → [MeasurableSpace α] → Type z}
  [MeasurableSpaceMonad m] [MeasurableSpaceMonad n] [MeasurableSpaceMonad o]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (o α)]
  [direct : MeasurableSpaceMonadLift m n] [MeasurableSpaceMonadLift n o]
  [LawfulMeasurableSpaceMonadLift m n] [LawfulMeasurableSpaceMonadLift n o]

-- Regression: stating the direct measurability law using the transitive projection made
-- `fun_prop` unable to find a theorem for the direct projection.
example {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → m β) (hf : Measurable f) :
    Measurable (fun a => direct.mMonadLift (f a)) := by
  fun_prop

-- Infer the lawful composite from two direct lifts without supplying the intermediate monad.
example : LawfulMeasurableSpaceMonadLiftT m o := inferInstance

-- `fun_prop` must find that composite's measurability through the public alias.
example {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → m β) (hf : Measurable f) :
    Measurable (fun a => mLiftM (n := o) (f a)) := by
  fun_prop

end Lawful

section CoreBridge

universe u v w

variable {m : Type u → Type v} {n : Type u → Type w}
  {α : Type u} [MeasurableSpace α]

-- A supplied core self-lift need not be identity. Measurable self-lifting must still use
-- the native identity instance, so these are not two definitionally identical candidates.
example [MonadLiftT m m] (x : Monad.toMeasurableSpaceMonad m α) :
    mMonadLift (n := Monad.toMeasurableSpaceMonad m) x = x := rfl

-- Native composition must also win when a core lift is available for the same endpoints.
example [MonadLiftT m n]
    [native : MeasurableSpaceMonadLift (Monad.toMeasurableSpaceMonad m)
      (Monad.toMeasurableSpaceMonad n)]
    (x : Monad.toMeasurableSpaceMonad m α) :
    mMonadLift (n := Monad.toMeasurableSpaceMonad n) x = native.mMonadLift x := rfl

-- If there is no native route, the bridge must use the supplied core lift.
example [MonadLiftT m n] (x : Monad.toMeasurableSpaceMonad m α) :
    mMonadLift (n := Monad.toMeasurableSpaceMonad n) x = monadLift (n := n) x := rfl

end CoreBridge

section FunctionLaws

universe u v w

variable {m : (α : Type u) → [MeasurableSpace α] → Type v}
  {n : (α : Type u) → [MeasurableSpace α] → Type w}
  [MeasurableSpaceMonad m] [MeasurableSpaceMonad n]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)]
  {lift : ⦃α : Type u⦄ → [MeasurableSpace α] → m α → n α}
  [Internal.LawfulMeasurableSpaceMonadLiftFunction lift]

-- The explicit function must give a lawful direct lift and then a lawful transitive lift.
-- Only the function laws are supplied; there is no pre-existing lifting instance.
example {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (ma : m α) (f : α → m β) (hf : Measurable f) :
    letI : MeasurableSpaceMonadLift m n := ⟨lift (α := _)⟩
    mLiftM (n := n) (ma >>=ₘ f) = mLiftM ma >>=ₘ fun a => mLiftM (f a) := by
  let : MeasurableSpaceMonadLift m n := ⟨lift (α := _)⟩
  exact mLiftM_mBind ma f hf

-- The conversion must preserve measurability too, so the existing `fun_prop` API applies.
example {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → m β) (hf : Measurable f) :
    letI : MeasurableSpaceMonadLift m n := ⟨lift (α := _)⟩
    Measurable (fun a => mLiftM (n := n) (f a)) := by
  let : MeasurableSpaceMonadLift m n := ⟨lift (α := _)⟩
  fun_prop

end FunctionLaws

-- Direct evaluation still allows the source and target to inhabit different universes.
example {n : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad n]
    [∀ α, [MeasurableSpace α] → MeasurableSpace (n α)] :
    Internal.LawfulMeasurableSpaceMonadLiftBindFunction
      (m := MId.{1}) (n := n)
      (fun _ _ _ _ f x => f x.run) := inferInstance

end TestNext.MeasurableSpaceMonad.Lift
