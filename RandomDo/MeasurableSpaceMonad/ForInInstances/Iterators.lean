/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForIn
public import RandomDo.Monad.Notation
public import Init.Data.Iterators.Consumers.Loop
import Init.Data.Iterators.Lemmas.Consumers.Loop
import all Init.Data.Iterators.Basic

/-!
# Iterator loops in measurable space monads

This file adapts core's iterator consumers to `mPure` and `mBind`. A single implementation works
in every `MeasurableSpaceMonad`, including `Measure` and adapted ordinary monads. The loop state
needs a measurable space; the elements and iterator internals do not.

## Main definitions

* `MeasurableSpaceIteratorLoop`: an extension point for producer-specific loop implementations.
* `LawfulMeasurableSpaceIteratorLoop`: agreement with the default consumer on well-founded loops.
* `MeasurableSpaceLiftBind`: lifting of ordinary monadic producer effects into a measurable monad.
* `Iter.instMeasurableSpaceForIn'`, `IterM.instMeasurableSpaceForIn'`: opt-in membership-aware
  consumers. Ordinary `for` loops and `Total`/`Partial` wrappers have global instances.
* `Iter.forIn_eq_match_step`: the one-step equation for finite pure iterators.

## Implementation details

The definitions follow `Init/Data/Iterators/Consumers/Monadic/Loop.lean` and
`Init/Data/Iterators/Consumers/Loop.lean`. The default consumer uses the same
`WellFounded.extrinsicFix₃` recursion and specialization as core. Loop-body effects run directly
in the measurable monad. There is no continuation-monad adapter or final continuation.

The low-priority default supports any iterator. Producer-specific optimizations require their
own `MeasurableSpaceIteratorLoop` instance; an ordinary `Std.IteratorLoop` instance does not
provide one automatically. A function abstract over the iterator type should take the loop
instance as a parameter if it needs to preserve a caller's specialized consumer, as in core.
`ForInInstances.Ranges` supplies the range specializations.

`IterM` producers use an ordinary monad. `MeasurableSpaceLiftBind` runs a producer action and then
passes its internal result to the consumer, without assigning a measurable space to that result.
For adapted ordinary monads such as `PseudoRandomM`, this uses the existing `MonadLiftT` and bind.
Pure iterators apply the function directly and require no lifting instance from the user.
-/

@[expose] public section

namespace MeasureTheory

open Std Std.Iterators MeasurableSpacePure MeasurableSpaceBind

universe u v w w'

/-- Lift an ordinary computation and pass its result to a measurable computation. The source
result type needs no measurable space. This is the `liftBind` argument of core's iterator consumers,
with a measurable target type. -/
class MeasurableSpaceLiftBind (n : Type w → Type w')
    (m : (α : Type u) → [MeasurableSpace α] → Type v) where
  /-- Run the producer action, then apply the function to its result. -/
  liftBind : {α : Type w} → {β : Type u} → [MeasurableSpace β] →
    (α → m β) → n α → m β

instance instMeasurableSpaceLiftBindId {m : (α : Type u) → [MeasurableSpace α] → Type v} :
    MeasurableSpaceLiftBind Id m where
  liftBind f x := f x.run

/-- Loop consumers for an iterator and a measurable space monad. Analogue of
`Std.IteratorLoop`, specialized to bodies returning `m (ForInStep β)`.

Core's extra predicate on loop-body steps is fixed to `True`, as in its `ForIn` instances.
Keeping the body result as `ForInStep β` avoids inserting a monadic bind and pure solely to attach
a proof of `True`. Such an insertion would need measurability hypotheses to simplify in general. -/
class MeasurableSpaceIteratorLoop (ι : Type w) (n : Type w → Type w') {α : Type w}
    [Iterator ι n α] (m : (β : Type u) → [MeasurableSpace β] → Type v) where
  /-- Traverse an iterator, lifting producer effects and threading a measurable loop state. -/
  forIn : (lift : ∀ (γ : Type w) (δ : Type u) [MeasurableSpace δ], (γ → m δ) → n γ → m δ) →
    (β : Type u) → [MeasurableSpace β] → (it : Std.IterM (α := ι) n α) → β →
    ((a : α) → it.IsPlausibleIndirectOutput a → β → m (ForInStep β)) → m β

variable {n : Type w → Type w'} {ι α : Type w} [Iterator ι n α]
  {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]

/-- Direct iteration through `IterM.step`. Analogue of `Std.IterM.DefaultConsumers.forIn'`.
The predicate `P` carries membership information without restricting the iterator's state type. -/
@[always_inline, inline]
def IterM.DefaultConsumers.measurableSpaceForIn'
    (lift : ∀ (γ : Type w) (δ : Type u) [MeasurableSpace δ], (γ → m δ) → n γ → m δ)
    (β : Type u) [MeasurableSpace β] (it : Std.IterM (α := ι) n α) (init : β)
    (P : α → Prop) (hP : ∀ a, it.IsPlausibleIndirectOutput a → P a)
    (f : (a : α) → P a → β → m (ForInStep β)) : m β :=
  haveI : Nonempty (m β) := ⟨mPure init⟩
  WellFounded.extrinsicFix₃ (C₃ := fun _ _ _ => m β)
    (InvImage (IteratorLoop.rel ι n (fun _ _ _ => True)) (fun x => (x.1, x.2.1)))
    (fun it acc (hP : ∀ a, it.IsPlausibleIndirectOutput a → P a) recur =>
      (lift _ _ · it.step) fun s => rdo
        match s.inflate with
        | .yield it' out h =>
          match ← f out (hP out <| .direct ⟨_, h⟩) acc with
          | .yield b =>
            recur it' b (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') (Or.inl ⟨out, h, trivial⟩)
          | .done b => return b
        | .skip it' h =>
          recur it' acc (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') (Or.inr ⟨h, rfl⟩)
        | .done _ => return acc) it init hP

section DefaultLemmas

variable {β : Type u} [MeasurableSpace β]
  {lift : ∀ (γ : Type w) (δ : Type u) [MeasurableSpace δ], (γ → m δ) → n γ → m δ}
  {it : Std.IterM (α := ι) n α} {init : β}
  {P : α → Prop} {hP : ∀ a, it.IsPlausibleIndirectOutput a → P a}
  {f : (a : α) → P a → β → m (ForInStep β)}

/-- Unfold the default consumer when its iteration relation is well-founded. -/
theorem IterM.DefaultConsumers.measurableSpaceForIn'_eq_match_step
    (wf : IteratorLoop.WellFounded ι n (γ := β) (fun _ _ _ => True)) :
    measurableSpaceForIn' lift β it init P hP f =
      (lift _ _ · it.step) (fun s =>
        match s.inflate with
        | .yield it' out h =>
          f out (hP _ <| .direct ⟨_, h⟩) init >>=ₘ fun
            | .yield b => measurableSpaceForIn' lift β it' b P
                (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
            | .done b => mPure b
        | .skip it' h => measurableSpaceForIn' lift β it' init P
            (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
        | .done _ => mPure init) := by
  have : Nonempty (m β) := ⟨mPure init⟩
  rw [measurableSpaceForIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
  congr

/-- The default consumer is independent of the predicate used to carry membership information. -/
theorem IterM.DefaultConsumers.measurableSpaceForIn'_congr
    {it : Std.IterM (α := ι) n α} {init : β}
    {P : α → Prop} {hP : ∀ a, it.IsPlausibleIndirectOutput a → P a}
    {f : (a : α) → P a → β → m (ForInStep β)}
    {Q : α → Prop} {hQ : ∀ a, it.IsPlausibleIndirectOutput a → Q a}
    {g : (a : α) → Q a → β → m (ForInStep β)}
    (wf : IteratorLoop.WellFounded ι n (γ := β) (fun _ _ _ => True))
    (hfg : ∀ a b (ha : P a) (ha' : Q a), f a ha b = g a ha' b) :
    measurableSpaceForIn' lift β it init P hP f =
      measurableSpaceForIn' lift β it init Q hQ g := by
  rw [measurableSpaceForIn'_eq_match_step wf, measurableSpaceForIn'_eq_match_step wf]
  congr; ext step
  split
  · congr 1
    · apply hfg
    · funext result
      cases result
      · rfl
      · apply measurableSpaceForIn'_congr wf hfg
  · apply measurableSpaceForIn'_congr wf hfg
  · rfl
termination_by IteratorLoop.WithWF.mk it init (hwf := wf)
decreasing_by
  · exact Or.inl ⟨_, ‹_›, trivial⟩
  · exact Or.inr ⟨‹_›, rfl⟩

end DefaultLemmas

/-- The generic step-based consumer. Analogue of `Std.IteratorLoop.defaultImplementation`.
Producers can supply a higher-priority instance with a specialized loop. -/
@[always_inline, inline, instance_reducible]
def MeasurableSpaceIteratorLoop.defaultImplementation : MeasurableSpaceIteratorLoop ι n m where
  forIn lift β _ it init :=
    IterM.DefaultConsumers.measurableSpaceForIn' lift β it init _ (fun _ => id)

instance (priority := 100) : MeasurableSpaceIteratorLoop ι n m := .defaultImplementation

/-- An optimized loop agrees with the default consumer on well-founded iterations, provided
lifting a pure producer value applies the supplied function to that value. -/
class LawfulMeasurableSpaceIteratorLoop (ι : Type w) (n : Type w → Type w')
    {α : Type w} [Monad n] [Iterator ι n α]
    (m : (β : Type u) → [MeasurableSpace β] → Type v) [MeasurableSpaceMonad m]
    [i : MeasurableSpaceIteratorLoop ι n m] : Prop where
  /-- Equality with the default implementation. Analogue of `Std.LawfulIteratorLoop.lawful`. -/
  lawful (lift : ∀ (γ : Type w) (δ : Type u) [MeasurableSpace δ], (γ → m δ) → n γ → m δ)
    (hlift : ∀ γ δ [MeasurableSpace δ] (f : γ → m δ) a, lift γ δ f (pure a) = f a)
    (β : Type u) [MeasurableSpace β] (it : Std.IterM (α := ι) n α) (init : β)
    (wf : IteratorLoop.WellFounded ι n (γ := β) (fun _ _ _ => True))
    (f : (a : α) → it.IsPlausibleIndirectOutput a → β → m (ForInStep β)) :
    i.forIn lift β it init f =
      MeasurableSpaceIteratorLoop.defaultImplementation.forIn lift β it init f

instance [Monad n] :
    letI : MeasurableSpaceIteratorLoop ι n m := .defaultImplementation
    LawfulMeasurableSpaceIteratorLoop ι n m where
  lawful _ _ _ _ _ _ _ _ := rfl

/-- Unfold a lawful loop consumer by one producer step. -/
theorem MeasurableSpaceIteratorLoop.forIn_eq_match_step [Monad n]
    [MeasurableSpaceIteratorLoop ι n m] [LawfulMeasurableSpaceIteratorLoop ι n m]
    (lift : ∀ (δ : Type w) (ε : Type u) [MeasurableSpace ε], (δ → m ε) → n δ → m ε)
    (hlift : ∀ δ ε [MeasurableSpace ε] (f : δ → m ε) a, lift δ ε f (pure a) = f a)
    {β : Type u} [MeasurableSpace β] (it : Std.IterM (α := ι) n α) (init : β)
    (wf : IteratorLoop.WellFounded ι n (γ := β) (fun _ _ _ => True))
    (f : (a : α) → it.IsPlausibleIndirectOutput a → β → m (ForInStep β)) :
    MeasurableSpaceIteratorLoop.forIn lift β it init f =
      (lift _ _ · it.step) (fun s =>
        match s.inflate with
        | .yield it' out h => f out (.direct ⟨_, h⟩) init >>=ₘ fun
            | .yield b => MeasurableSpaceIteratorLoop.forIn lift β it' b
                (fun a ha b => f a (.indirect ⟨_, rfl, h⟩ ha) b)
            | .done b => mPure b
        | .skip it' h => MeasurableSpaceIteratorLoop.forIn lift β it' init
            (fun a ha b => f a (.indirect ⟨_, rfl, h⟩ ha) b)
        | .done _ => mPure init) := by
  rw [LawfulMeasurableSpaceIteratorLoop.lawful lift hlift β it init wf]
  simp only [MeasurableSpaceIteratorLoop.forIn]
  rw [IterM.DefaultConsumers.measurableSpaceForIn'_eq_match_step wf]
  congr 1; funext s
  cases s.inflate using Std.PlausibleIterStep.casesOn
  · apply MeasurableSpaceBind.bind_congr
    intro step
    cases step
    · rfl
    · simp only
      rw [LawfulMeasurableSpaceIteratorLoop.lawful lift hlift β _ _ wf]
      exact IterM.DefaultConsumers.measurableSpaceForIn'_congr wf (by intros; rfl)
  · simp only
    rw [LawfulMeasurableSpaceIteratorLoop.lawful lift hlift β _ _ wf]
    exact IterM.DefaultConsumers.measurableSpaceForIn'_congr wf (by intros; rfl)
  · rfl

/-- Membership-aware iteration. Analogue of `Std.IterM.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate. -/
@[always_inline, inline, instance_reducible]
def IterM.instMeasurableSpaceForIn' [MeasurableSpaceLiftBind n m]
    [MeasurableSpaceIteratorLoop ι n m] :
    MeasurableSpaceForIn' m (Std.IterM (α := ι) n α) α
      ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' {β} _ it init f :=
    MeasurableSpaceIteratorLoop.forIn (m := m)
      (fun _ _ _ => MeasurableSpaceLiftBind.liftBind) β it init f

instance IterM.instMeasurableSpaceForIn [MeasurableSpaceLiftBind n m]
    [MeasurableSpaceIteratorLoop ι n m] :
    MeasurableSpaceForIn m (Std.IterM (α := ι) n α) α :=
  haveI := IterM.instMeasurableSpaceForIn' (m := m) (n := n) (ι := ι)
  instMeasurableSpaceForInOfForIn'

/-- Membership-aware iteration. Analogue of `Std.Iter.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate. -/
@[always_inline, inline, instance_reducible]
def Iter.instMeasurableSpaceForIn' {ι α : Type w} [Iterator ι Id α]
    [MeasurableSpaceIteratorLoop ι Id m] :
    MeasurableSpaceForIn' m (Std.Iter (α := ι) α) α
      ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' {β} _ it init f :=
    MeasurableSpaceIteratorLoop.forIn (fun _ _ _ f x => f x.run) β
      it.toIterM init fun out h acc =>
        f out (Std.Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h) acc

instance Iter.instMeasurableSpaceForIn {ι α : Type w} [Iterator ι Id α]
    [MeasurableSpaceIteratorLoop ι Id m] :
    MeasurableSpaceForIn m (Std.Iter (α := ι) α) α :=
  haveI := Iter.instMeasurableSpaceForIn' (m := m) (ι := ι)
  instMeasurableSpaceForInOfForIn'

/-- Membership-aware iteration. Analogue of `Std.Iter.Partial.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate. -/
@[always_inline, inline, instance_reducible]
def Iter.Partial.instMeasurableSpaceForIn'
    {ι α : Type w} [Iterator ι Id α] [MeasurableSpaceIteratorLoop ι Id m] :
    MeasurableSpaceForIn' m (Std.Iter.Partial (α := ι) α) α
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f := Iter.instMeasurableSpaceForIn'.forIn' it.it init f

instance Iter.Partial.instMeasurableSpaceForIn
    {ι α : Type w} [Iterator ι Id α] [MeasurableSpaceIteratorLoop ι Id m] :
    MeasurableSpaceForIn m (Std.Iter.Partial (α := ι) α) α :=
  haveI := Iter.Partial.instMeasurableSpaceForIn' (m := m) (ι := ι)
  instMeasurableSpaceForInOfForIn'

/-- Membership-aware iteration. Analogue of `Std.Iter.Total.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate.
The `Finite` assumption restricts the total wrapper to terminating iterators; its implementation
reuses the ordinary consumer. -/
@[always_inline, inline, instance_reducible, nolint unusedArguments]
def Iter.Total.instMeasurableSpaceForIn'
    {ι α : Type w} [Iterator ι Id α] [MeasurableSpaceIteratorLoop ι Id m] [Finite ι Id] :
    MeasurableSpaceForIn' m (Std.Iter.Total (α := ι) α) α
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f := Iter.instMeasurableSpaceForIn'.forIn' it.it init f

instance Iter.Total.instMeasurableSpaceForIn
    {ι α : Type w} [Iterator ι Id α] [MeasurableSpaceIteratorLoop ι Id m] [Finite ι Id] :
    MeasurableSpaceForIn m (Std.Iter.Total (α := ι) α) α :=
  haveI := Iter.Total.instMeasurableSpaceForIn' (m := m) (ι := ι)
  instMeasurableSpaceForInOfForIn'

/-- Membership-aware iteration. Analogue of `Std.IterM.Partial.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate. -/
@[always_inline, inline, instance_reducible]
def IterM.Partial.instMeasurableSpaceForIn'
    [MeasurableSpaceLiftBind n m] [MeasurableSpaceIteratorLoop ι n m] :
    MeasurableSpaceForIn' m (Std.IterM.Partial (α := ι) n α) α
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f := IterM.instMeasurableSpaceForIn'.forIn' it.it init f

instance IterM.Partial.instMeasurableSpaceForIn
    [MeasurableSpaceLiftBind n m] [MeasurableSpaceIteratorLoop ι n m] :
    MeasurableSpaceForIn m (Std.IterM.Partial (α := ι) n α) α :=
  haveI := IterM.Partial.instMeasurableSpaceForIn' (m := m) (n := n) (ι := ι)
  instMeasurableSpaceForInOfForIn'

/-- Membership-aware iteration. Analogue of `Std.IterM.Total.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate.
The `Finite` assumption restricts the total wrapper to terminating iterators; its implementation
reuses the ordinary consumer. -/
@[always_inline, inline, instance_reducible, nolint unusedArguments]
def IterM.Total.instMeasurableSpaceForIn'
    [MeasurableSpaceLiftBind n m] [MeasurableSpaceIteratorLoop ι n m] [Finite ι n] :
    MeasurableSpaceForIn' m (Std.IterM.Total (α := ι) n α) α
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f := IterM.instMeasurableSpaceForIn'.forIn' it.it init f

instance IterM.Total.instMeasurableSpaceForIn
    [MeasurableSpaceLiftBind n m] [MeasurableSpaceIteratorLoop ι n m] [Finite ι n] :
    MeasurableSpaceForIn m (Std.IterM.Total (α := ι) n α) α :=
  haveI := IterM.Total.instMeasurableSpaceForIn' (m := m) (n := n) (ι := ι)
  instMeasurableSpaceForInOfForIn'

/-- Unfold a finite pure iterator loop by one step. Analogue of `Std.Iter.forIn_eq_match_step`.
This requires no monad laws or measurable space on the iterator's internal state or elements. -/
theorem Iter.forIn_eq_match_step {ι α : Type w} [Iterator ι Id α]
    [MeasurableSpaceIteratorLoop ι Id m] [LawfulMeasurableSpaceIteratorLoop ι Id m]
    [Finite ι Id] {β : Type u} [MeasurableSpace β]
    (it : Std.Iter (α := ι) α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn it init f =
      match it.step with
      | .yield it' out _ => f out init >>=ₘ fun
          | .yield b => MeasureTheory.forIn it' b f
          | .done b => mPure b
      | .skip it' _ => MeasureTheory.forIn it' init f
      | .done _ => mPure init := by
  simp only [MeasureTheory.forIn, MeasureTheory.forIn']
  rw [MeasurableSpaceIteratorLoop.forIn_eq_match_step _ (by intros; rfl)
    _ _ IteratorLoop.wellFounded_of_finite]
  simp only [Std.Iter.step]
  cases it.toIterM.step.run.inflate using Std.PlausibleIterStep.casesOn <;> rfl


end MeasureTheory
