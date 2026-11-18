/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.Loop
public import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators.Core
public import RandomDo.MeasurableSpaceMonad.ForIn
public import RandomDo.MeasurableSpaceMonad.Lift
public import RandomDo.RDo.Core
public import Init.Data.Iterators.Consumers.Loop
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Monadic.Basic
import all Init.Data.Iterators.Basic

/-!
# Measurable consumers for core iterators

The loop instances convert core iterators to measurable producers and use the common loop API.
Pure iterators retain their direct handler, so their element and accumulator universes remain
independent. Membership and termination proofs are transported through the producer conversion.
-/

@[expose] public section

namespace MeasureTheory

open Std Std.Iterators MeasureTheory.Internal

universe w w' w'' x x'

#check Std.IterM.instForIn'

/-- Iterate over an ordinary producer in a measurable space monad.
Analogue of `Std.IterM.instForIn'`. The membership-aware instance is opt-in, as in core. -/
@[always_inline, inline, instance_reducible]
def _root_.Std.IterM.instMeasurableSpaceForIn' {m : Type w → Type w'} [Functor m]
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α β : Type w} [Iterator α m β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α (Monad.toMeasurableSpaceMonad m) n]
    [MeasurableSpaceMonad n] [MeasurableSpaceMonadLiftT (Monad.toMeasurableSpaceMonad m) n] :
    MeasurableSpaceForIn' n (Std.IterM (α := α) m β) β
      ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  mForIn' it init f :=
    IterM.instMeasurableSpaceForIn'.mForIn' it.toMeasurable init fun out h acc =>
      f out (IterM.isPlausibleIndirectOutput_toCore.mp h) acc

#check Std.IterM.instForInOfIteratorLoop

instance {m : Type w → Type w'} [Functor m]
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α β : Type w} [Iterator α m β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α (Monad.toMeasurableSpaceMonad m) n]
    [MeasurableSpaceMonadLiftT (Monad.toMeasurableSpaceMonad m) n] [MeasurableSpaceMonad n] :
    MeasurableSpaceForIn n (Std.IterM (α := α) m β) β :=
  haveI := Std.IterM.instMeasurableSpaceForIn' (m := m) (n := n) (α := α)
  instMeasurableSpaceForInOfForIn'

#check Std.IterM.Partial.instForIn'

/-- Membership-aware iteration. Analogue of `Std.IterM.Partial.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate. -/
@[always_inline, inline, instance_reducible]
def _root_.Std.IterM.Partial.instMeasurableSpaceForIn' {m : Type w → Type w'} [Functor m]
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α (Monad.toMeasurableSpaceMonad m) n]
    [MeasurableSpaceMonadLiftT (Monad.toMeasurableSpaceMonad m) n] [MeasurableSpaceMonad n] :
    MeasurableSpaceForIn' n (Std.IterM.Partial (α := α) m β) β
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  mForIn' it init f :=
    haveI := @Std.IterM.instMeasurableSpaceForIn'
    mForIn' it.it init f

#check Std.IterM.Total.instForIn'

/-- Membership-aware iteration. Analogue of `Std.IterM.Total.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate.
The `Finite` assumption restricts the total wrapper to terminating iterators; its implementation
reuses the ordinary consumer. -/
@[always_inline, inline, instance_reducible, nolint unusedArguments]
def _root_.Std.IterM.Total.instMeasurableSpaceForIn' {m : Type w → Type w'} [Functor m]
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α (Monad.toMeasurableSpaceMonad m) n]
    [MeasurableSpaceMonadLiftT (Monad.toMeasurableSpaceMonad m) n] [MeasurableSpaceMonad n]
    [Finite α m] :
    MeasurableSpaceForIn' n (Std.IterM.Total (α := α) m β) β
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  mForIn' it init f := Std.IterM.instMeasurableSpaceForIn'.mForIn' it.it init f

#check Std.IterM.Partial.instForInOfIteratorLoop

instance _root_.Std.IterM.Partial.instMeasurableSpaceForInOfIteratorLoop {m : Type w → Type w'}
    [Functor m]
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α (Monad.toMeasurableSpaceMonad m) n]
    [MeasurableSpaceMonadLiftT (Monad.toMeasurableSpaceMonad m) n] [MeasurableSpaceMonad n] :
    MeasurableSpaceForIn n (Std.IterM.Partial (α := α) m β) β :=
  haveI : MeasurableSpaceForIn' n (Std.IterM.Partial (α := α) m β) β _ :=
    Std.IterM.Partial.instMeasurableSpaceForIn'
  instMeasurableSpaceForInOfForIn'

#check Std.instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite

instance {m : Type w → Type w'} [Functor m]
    {n : (γ : Type w) → [MeasurableSpace γ] → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α (Monad.toMeasurableSpaceMonad m) n]
    [MeasurableSpaceMonadLiftT (Monad.toMeasurableSpaceMonad m) n] [MeasurableSpaceMonad n]
    [Finite α m] :
    MeasurableSpaceForIn n (Std.IterM.Total (α := α) m β) β :=
  haveI : MeasurableSpaceForIn' n (Std.IterM.Total (α := α) m β) β _ :=
    Std.IterM.Total.instMeasurableSpaceForIn'
  instMeasurableSpaceForInOfForIn'

#check Std.Iter.instForIn'

/-- Membership-aware iteration. Analogue of `Std.Iter.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate. -/
@[always_inline, inline, instance_reducible]
def Iter.instMeasurableSpaceForIn' {α : Type w} {β : Type w}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α MId n] :
    MeasurableSpaceForIn' n (Std.Iter (α := α) β) β
      ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  mForIn' it init f :=
    MeasurableSpaceIteratorLoop.finiteForIn' (fun _ _ _ _ f x => f x.run) |>.mForIn'
      it.toMeasurable init fun out h acc =>
        f out (Std.Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr
          (IterM.isPlausibleIndirectOutput_toCore.mp h)) acc

#check Std.instForInIterOfMonadOfIteratorLoopId

instance (α : Type w) (β : Type w)
    (n : (γ : Type x) → [MeasurableSpace γ] → Type x') [MeasurableSpaceMonad n]
    [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α MId n] :
    MeasurableSpaceForIn n (Std.Iter (α := α) β) β :=
  haveI : MeasurableSpaceForIn' n (Std.Iter (α := α) β) β _ := Iter.instMeasurableSpaceForIn'
  instMeasurableSpaceForInOfForIn'

#check Std.Iter.Partial.instForIn'

/-- Membership-aware iteration. Analogue of `Std.Iter.Partial.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate. -/
@[always_inline, inline, instance_reducible]
def Iter.Partial.instMeasurableSpaceForIn' {α : Type w} {β : Type w}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α MId n] :
    MeasurableSpaceForIn' n (Std.Iter.Partial (α := α) β) β
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  mForIn' it init f :=
    haveI := @Iter.instMeasurableSpaceForIn'
    mForIn' it.it init f

#check Std.instForInPartialOfMonadOfIteratorLoopId

instance (α : Type w) (β : Type w)
    (n : (γ : Type x) → [MeasurableSpace γ] → Type x') [MeasurableSpaceMonad n]
    [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α MId n] :
    MeasurableSpaceForIn n (Std.Iter.Partial (α := α) β) β :=
  haveI : MeasurableSpaceForIn' n (Std.Iter.Partial (α := α) β) β _ :=
    Iter.Partial.instMeasurableSpaceForIn'
  instMeasurableSpaceForInOfForIn'

#check Std.Iter.Total.instForIn'

/-- Membership-aware iteration. Analogue of `Std.Iter.Total.instForIn'`.
As in core, this is opt-in because the generic membership relation is an internal predicate.
The `Finite` assumption restricts the total wrapper to terminating iterators; its implementation
reuses the ordinary consumer. -/
@[always_inline, inline, instance_reducible, nolint unusedArguments]
def Iter.Total.instMeasurableSpaceForIn' {α : Type w} {β : Type w}
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α MId n] [Finite α Id] :
    MeasurableSpaceForIn' n (Std.Iter.Total (α := α) β) β
      ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  mForIn' it init f := Iter.instMeasurableSpaceForIn'.mForIn' it.it init f

#check Std.instForInTotalOfMonadOfIteratorLoopOfFiniteId

instance (α : Type w) (β : Type w)
    (n : (γ : Type x) → [MeasurableSpace γ] → Type x') [MeasurableSpaceMonad n]
    [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpaceIteratorLoop α MId n] [Finite α Id] :
    MeasurableSpaceForIn n (Std.Iter.Total (α := α) β) β :=
  haveI : MeasurableSpaceForIn' n (Std.Iter.Total (α := α) β) β _ :=
    Iter.Total.instMeasurableSpaceForIn'
  instMeasurableSpaceForInOfForIn'

instance _root_.Std.Shrink.instSubsingleton {α : Type w} [Subsingleton α] :
    Subsingleton (Shrink α) where
  allEq a b := by
    have h : a.inflate = b.inflate := Subsingleton.elim _ _
    simpa only [Shrink.deflate_inflate] using congrArg Shrink.deflate h

instance IterM.instSubsingletonStep {α β : Type w}
    {m : (γ : Type w) → [MeasurableSpace γ] → Type w'}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpaceIterator α m β]
    [LawfulDeterministicMeasurableSpaceIterator α m]
    (it : IterM (α := α) m β) : Subsingleton it.Step where
  allEq a b := by
    obtain ⟨step, hs⟩ := LawfulDeterministicMeasurableSpaceIterator.isPlausibleStep_eq_eq (it := it)
    apply Subtype.ext
    have ha : a.val = step := by simpa only [hs] using a.property
    have hb : b.val = step := by simpa only [hs] using b.property
    exact ha.trans hb.symm

-- No separate standard-library analogue: core uses its unconditional `liftBind_pure` law.
-- For measurable lifting, determinism makes every function on the plausible step type measurable.
/-- A lawful measurable lifting function evaluates a deterministic pure producer step directly. -/
theorem IterM.liftBind_step {α β : Type w} [Iterator α Id β]
    [LawfulDeterministicIterator α Id] [MeasurableSpace α] [MeasurableSpace β]
    {n : (δ : Type x) → [MeasurableSpace δ] → Type x'} [MeasurableSpaceMonad n]
    [∀ δ, [MeasurableSpace δ] → MeasurableSpace (n δ)]
    (lift : ∀ (γ : Type w) (δ : Type x) [MeasurableSpace γ] [MeasurableSpace δ],
      (γ → n δ) → MId γ → n δ)
    [hlift : LawfulMeasurableSpaceMonadLiftBindFunction
      (m := MId) (n := n) lift]
    (it : IterM (α := α) MId β) {δ : Type x} [MeasurableSpace δ]
    (f : Shrink it.Step → n δ) :
    lift _ _ f it.step = f it.step.run :=
  hlift.liftBind_mPure f it.step.run Subsingleton.measurable

-- No ordinary core analogue: measurable monad laws require measurability of the remaining loop.
private theorem IterM.DefaultConsumers.measurable_mForIn'
    {α β : Type w} [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β] [Finite α Id]
    {n : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad n]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (n γ)] [LawfulMeasurableSpaceMonad n]
    {γ : Type x} [MeasurableSpace γ]
    (it : IterM (α := α) MId β)
    (P : β → Prop) (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → γ → n {_s : ForInStep γ // True})
    (hf : ∀ b hb, Measurable (f b hb)) :
    Measurable (fun init => mForIn' (fun _ _ _ _ f x => f x.run)
      γ (fun _ _ _ => True) it init P hP f) := by
  induction it using IterM.inductSteps with
  | step it ihy ihs =>
    conv =>
      arg 1; ext init
      rw [mForIn'_eq_match_step _ MeasurableSpaceIteratorLoop.wellFounded_of_finite]
    dsimp only
    cases it.step.run.inflate using Std.PlausibleIterStep.casesOn with
    | yield it' out h =>
      simp only
      have hm : Measurable (fun s : ForInStep γ => match s with
          | .yield c => mForIn' (m := MId)
            (fun _ _ _ _ f x => f x.run) γ
              (fun _ _ _ => True) it' c P (fun b hb => hP b (.indirect ⟨_, rfl, h⟩ hb)) f
          | .done c => mPure c) := by
        apply measurable_fun_forInStep
        · exact measurable_mPure
        · exact ihy h _
      convert (measurable_mBind (hm.comp measurable_subtype_coe)).comp
        (hf out (hP out (.direct ⟨_, h⟩))) using 1
      funext init
      apply MeasurableSpaceBind.bind_congr
      rintro ⟨step, _⟩
      cases step <;> rfl
    | skip it' h => exact ihs h _
    | done h => exact measurable_mPure

-- Keeping the trivial-proof adapter makes this a structural equality; unlike core,
-- no target monad laws or measurable spaces on computation types are needed here.
#check Std.Iter.forIn_eq

/-- Express ordinary iteration through the default consumer, including its trivial step proofs. -/
theorem Iter.mForIn_eq {α β : Type w} [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β] [Finite α Id]
    {m : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad m]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]
    [MeasurableSpaceIteratorLoop α MId m]
    [LawfulMeasurableSpaceIteratorLoop α MId m]
    {γ : Type x} [MeasurableSpace γ] {it : Std.Iter (α := α) β} {init : γ}
    {f : β → γ → m (ForInStep γ)} :
    mForIn it init f =
      IterM.DefaultConsumers.mForIn' (fun _ _ _ _ f x => f x.run)
        γ (fun _ _ _ => True) it.toMeasurable init _ (fun _ => id)
        (fun out _ acc => rdo return ⟨← f out acc, trivial⟩) := by
  simp only [mForIn, mForIn']
  rw [LawfulMeasurableSpaceIteratorLoop.lawful (m := MId) (n := m)
    (lift := fun _ _ _ _ f x => f x.run)
    γ it.toMeasurable init _ MeasurableSpaceIteratorLoop.wellFounded_of_finite]
  rfl

-- No ordinary core analogue: this supplies the measurability needed by the bind laws.
/-- Iteration over a finite pure iterator is measurable in its initial accumulator whenever
its body is measurable in the accumulator. -/
@[fun_prop]
theorem Iter.measurable_mForIn {α β : Type w} [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β] [Finite α Id]
    {m : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad m]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]
    [MeasurableSpaceIteratorLoop α MId m]
    [LawfulMeasurableSpaceIteratorLoop α MId m]
    {γ : Type x} [MeasurableSpace γ]
    (it : Std.Iter (α := α) β) (f : β → γ → m (ForInStep γ))
    (hf : ∀ b, Measurable (f b)) : Measurable (fun init => mForIn it init f) := by
  simp_rw [mForIn_eq]
  apply IterM.DefaultConsumers.measurable_mForIn'
  intro b _
  exact (measurable_mBind (by fun_prop)).comp (hf b)

-- Unlike core, simplifying the trivial-proof adapter requires measurability of the body and
-- the remaining loop, so the measurable bind laws apply.
#check Std.Iter.forIn_eq_match_step

/-- Unfold iteration over a finite pure iterator by one step. -/
theorem Iter.mForIn_eq_match_step {α β : Type w} [Iterator α Id β]
    [MeasurableSpace α] [MeasurableSpace β] [Finite α Id]
    {m : (γ : Type x) → [MeasurableSpace γ] → Type x'} [MeasurableSpaceMonad m]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]
    [MeasurableSpaceIteratorLoop α MId m]
    [LawfulMeasurableSpaceIteratorLoop α MId m]
    {γ : Type x} [MeasurableSpace γ] {it : Std.Iter (α := α) β} {init : γ}
    {f : β → γ → m (ForInStep γ)} (hf : ∀ b, Measurable (f b)) :
    mForIn it init f = (rdo
      match it.step with
      | .yield it' out _ =>
        match ← f out init with
        | .yield c => mForIn it' c f
        | .done c => return c
      | .skip it' _ => mForIn it' init f
      | .done _ => return init) := by
  simp only [mForIn, mForIn']
  rw [MeasurableSpaceIteratorLoop.mForIn_eq_match_step (m := MId)
    (n := m) _ _ _ _
    MeasurableSpaceIteratorLoop.wellFounded_of_finite]
  simp only [Std.Iter.step, Std.Iter.toMeasurable, Std.IterM.inflate_step_toMeasurable]
  cases it.toIterM.step.run.inflate using Std.PlausibleIterStep.casesOn with
  | yield it' out h =>
    simp only [Std.IterM.Step.toPure_yield,
      Std.IterM.Step.toMeasurable, IterStep.mapIterator]
    have hm : Measurable (fun s : ForInStep γ => match s with
        | .yield c => mForIn it'.toIter c f
        | .done c => mPure c) := by
      fun_prop
    have hm := hm.comp (measurable_subtype_coe (p := fun _ => True))
    simp only [mForIn, mForIn'] at hm
    simp only [Std.Iter.toIterM_toIter] at hm ⊢
    rw [mBind_assoc]
    · apply MeasurableSpaceBind.bind_congr
      intro step
      rw [mPure_mBind]
      · cases step <;> rfl
      · convert hm using 1
        ext ⟨step, _⟩
        cases step <;> rfl
    · fun_prop
    · convert hm using 1
      ext ⟨step, _⟩
      cases step <;> rfl
  | skip it' h => simp [Std.IterM.Step.toMeasurable]
  | done h => simp [Std.IterM.Step.toMeasurable]

end MeasureTheory
