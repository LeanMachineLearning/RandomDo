/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForInInstances.Iterators
public import Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Range.Polymorphic.RangeIterator

/-!
# Range instances for measurable space monads

These three consumers follow `Std.Rxc.Iterator.instIteratorLoop`,
`Std.Rxo.Iterator.instIteratorLoop`, and `Std.Rxi.Iterator.instIteratorLoop` in
`Init/Data/Range/Polymorphic/RangeIterator.lean`. They keep the next value directly in the loop
arguments, avoiding the `Option` in the generic range iterator state.

Each implementation is shared by all measurable space monads. The accompanying lawfulness
proofs follow core's well-founded reference loops and show agreement with the default consumer.
They use congruence of bind, without assuming monad laws or measurability of the body.

The nine direct range instances follow `Init/Data/Range/Polymorphic/Iterators.lean`, delegating
to these consumers and converting iterator membership proofs to range membership proofs.
They support `for i in a...b rdo ...` and the other open, closed, and unbounded range forms,
with the same finiteness requirements as core. The `forIn_eq_forIn_iter` lemmas expose this
connection for proofs about range loops.
-/

@[expose] public section

namespace MeasureTheory

open Std Std.Iterators Std.PRange MeasurableSpacePure MeasurableSpaceBind

open MeasureTheory.IterM.DefaultConsumers

universe u v w

namespace Rxc

open Std.Rxc Std.Rxc.Iterator

variable {α : Type w}

/-- Direct range iteration without allocating the `Option` that records exhaustion on each step.
Analogue of `Std.Rxc.Iterator.instIteratorLoop`. -/
@[always_inline, inline]
instance Iterator.instMeasurableSpaceIteratorLoop [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m] :
    MeasurableSpaceIteratorLoop (Rxc.Iterator α) Id m where
  forIn _ γ _ it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      loop γ (next ≤ ·) (fun a b hab hna => ?hle)
        upperBound init next ?hle'' (fun a ha₁ ha₂ c => f a ?hf c)
    | ⟨⟨none, _⟩⟩ => mPure init
  where
    @[always_inline, inline]
    loop (γ : Type u) [MeasurableSpace γ]
        (LargeEnough : α → Prop)
        (hl : ∀ a b : α, a ≤ b → LargeEnough a → LargeEnough b)
        (upperBound : α) (acc : γ) (next : α) (h : LargeEnough next)
        (f : (out : α) → LargeEnough out → out ≤ upperBound → (c : γ) → m (ForInStep γ)) : m γ :=
      haveI : Nonempty (m γ) := ⟨mPure acc⟩
      WellFounded.extrinsicFix₃ (C₃ := fun _ _ _ => m γ)
        (InvImage (IteratorLoop.rel _ Id (fun _ _ _ => True))
          (fun x => (⟨Rxc.Iterator.mk (some x.1) upperBound⟩, x.2.1)))
        (fun next acc (h : LargeEnough next) G => rdo
          if hu : next ≤ upperBound then
            match ← f next h hu acc with
            | .yield acc' =>
              match hs : UpwardEnumerable.succ? next with
              | some next' => G next' acc' (hl _ _ ?hle' h) ?decreasing
              | none => mPure acc'
            | .done acc' => mPure acc'
          else
            mPure acc) next acc h
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      simp only [UpwardEnumerable.le_iff] at ha₁
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      simp only [UpwardEnumerable.le_iff] at hna hab ⊢
      exact UpwardEnumerable.le_trans hna hab
    case hle' =>
      simp only [UpwardEnumerable.le_iff]
      refine ⟨1, ?_⟩
      simpa [succMany?_one] using hs
    case hle'' =>
      exact UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_refl _)
    case decreasing =>
      simp_wf
      simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

private noncomputable def Iterator.instMeasurableSpaceIteratorLoop.loop.wf
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]
    (γ : Type u) [MeasurableSpace γ]
    (wf : IteratorLoop.WellFounded (Rxc.Iterator α) Id (γ := γ) (fun _ _ _ => True))
    (LargeEnough : α → Prop) (hl : ∀ a b : α, a ≤ b → LargeEnough a → LargeEnough b)
    (upperBound : α) (acc : γ) (next : α) (h : LargeEnough next)
    (f : (out : α) → LargeEnough out → out ≤ upperBound → (c : γ) → m (ForInStep γ)) :
    m γ := rdo
  if hu : next ≤ upperBound then
    match ← f next h hu acc with
    | .yield acc' =>
      match hs : UpwardEnumerable.succ? next with
      | some next' =>
        loop.wf γ wf LargeEnough hl upperBound acc' next' (hl _ _ ?hle h) f
      | none => return acc'
    | .done acc' => return acc'
  else
    return acc
termination_by IteratorLoop.WithWF.mk ⟨⟨some next, upperBound⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]
where finally
  case hle =>
    simp only [UpwardEnumerable.le_iff]
    refine ⟨1, ?_⟩
    simpa [succMany?_one] using hs

private theorem Iterator.instMeasurableSpaceIteratorLoop.loop_eq_wf
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]
    {γ : Type u} [MeasurableSpace γ] {LargeEnough hl upperBound} {next hn} {acc} (wf f) :
    loop γ LargeEnough hl upperBound acc next hn f =
      loop.wf (α := α) (m := m) γ wf LargeEnough hl upperBound acc next hn f := by
  have : Nonempty (m γ) := ⟨mPure acc⟩
  rw [loop, WellFounded.extrinsicFix₃_eq_fix]; rotate_left
  · exact InvImage.wf _ wf
  · fun_induction loop.wf γ wf LargeEnough hl upperBound acc next hn f
    · rw [WellFounded.fix_eq]
      simp only [↓reduceDIte, *]
      apply MeasurableSpaceBind.bind_congr; intro forInStep
      split
      · split
        · simp_all
        · simp
      · simp
    · rw [WellFounded.fix_eq]
      simp_all

private theorem Iterator.instMeasurableSpaceIteratorLoop.loopWf_eq
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]
    (γ : Type u) [MeasurableSpace γ]
    {lift : ∀ (δ : Type w) (ε : Type u) [MeasurableSpace ε], (δ → m ε) → Id δ → m ε}
    (hlift : ∀ δ ε [MeasurableSpace ε] (f : δ → m ε) a, lift δ ε f (pure a) = f a)
    (wf : IteratorLoop.WellFounded (Rxc.Iterator α) Id (γ := γ) (fun _ _ _ => True))
    (LargeEnough : α → Prop) (hl : ∀ a b : α, a ≤ b → LargeEnough a → LargeEnough b)
    (upperBound : α) (acc : γ) (next : α) (h : LargeEnough next)
    (f : (out : α) → LargeEnough out → out ≤ upperBound → (c : γ) → m (ForInStep γ)) :
    loop.wf γ wf LargeEnough hl upperBound acc next h f = (rdo
      if hu : next ≤ upperBound then
        match ← f next h hu acc with
        | .yield acc' =>
          letI it' : IterM (α := Rxc.Iterator α) Id α := ⟨⟨succ? next, upperBound⟩⟩
          measurableSpaceForIn' (n := Id) (m := m) lift γ it' acc'
            it'.IsPlausibleIndirectOutput (fun _ => id)
            fun next' h acc' => f next'
              (by
                refine hl next next' ?_ ‹_›
                simp only [it', Monadic.isPlausibleIndirectOutput_iff,
                  ← succMany?_add_one_eq_succ?_bind_succMany?] at h
                exact UpwardEnumerable.le_iff.mpr ⟨h.choose + 1, h.choose_spec.1⟩)
              (by
                simp only [it', Monadic.isPlausibleIndirectOutput_iff] at h
                exact h.choose_spec.2)
              acc'
        | .done acc' => return acc'
      else return acc) := by
  have : Nonempty (m γ) := ⟨mPure acc⟩
  rw [loop.wf]
  congr 1; ext hu
  apply MeasurableSpaceBind.bind_congr; intro forInStep
  split
  · split
    · rw [loopWf_eq (lift := lift) _ hlift wf]
      rw [measurableSpaceForIn'_eq_match_step (lift := lift) wf]
      · simp only [IterM.step_mk, Monadic.step_eq_step, Monadic.step,
          Shrink.inflate_deflate, *]
        split
        · apply MeasurableSpaceBind.bind_congr; intro forInStep
          split
          · apply measurableSpaceForIn'_congr wf ; intros; rfl
          · simp
        · simp
    · rw [measurableSpaceForIn'_eq_match_step wf]
      simp only [IterM.step_eq, Shrink.inflate_deflate, *]
      -- Eliminate the lift and `Shrink` before unfolding the step and its proof indices.
      simp [Monadic.step]
  · simp
termination_by IteratorLoop.WithWF.mk ⟨⟨some next, upperBound⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

instance Iterator.instLawfulMeasurableSpaceIteratorLoop [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m] :
    LawfulMeasurableSpaceIteratorLoop (Rxc.Iterator α) Id m where
  lawful := by
    intro lift hlift γ _ it init wf f
    simp only [MeasurableSpaceIteratorLoop.forIn]
    rw [measurableSpaceForIn'_eq_match_step wf]
    split; rotate_left
    · simp only [Std.IterM.step_eq, hlift, Shrink.inflate_deflate]
      simp [Monadic.step]
    rename_i next _
    rw [instMeasurableSpaceIteratorLoop.loop_eq_wf wf,
      instMeasurableSpaceIteratorLoop.loopWf_eq (lift := lift) _ hlift wf]
    simp only [Std.IterM.step_eq, hlift, Shrink.inflate_deflate]
    simp only [Monadic.step]
    split
    · apply MeasurableSpaceBind.bind_congr; intro forInStep
      split
      · apply measurableSpaceForIn'_congr wf
        intros; rfl
      · rfl
    · rfl

end Rxc

namespace Rxo

open Std.Rxo Std.Rxo.Iterator

variable {α : Type w}

/-- Direct range iteration without allocating the `Option` that records exhaustion on each step.
Analogue of `Std.Rxo.Iterator.instIteratorLoop`. -/
@[always_inline, inline]
instance Iterator.instMeasurableSpaceIteratorLoop [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m] :
    MeasurableSpaceIteratorLoop (Rxo.Iterator α) Id m where
  forIn _ γ _ it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      loop γ (UpwardEnumerable.LE next ·) (fun a b hab hna => ?hle)
        upperBound init next ?hle'' (fun a ha₁ ha₂ c => f a ?hf c)
    | ⟨⟨none, _⟩⟩ => mPure init
  where
    @[always_inline, inline]
    loop (γ : Type u) [MeasurableSpace γ] (LargeEnough : α → Prop)
        (hl : ∀ a b : α, UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b)
        (upperBound : α) (acc : γ) (next : α) (h : LargeEnough next)
        (f : (out : α) → LargeEnough out → out < upperBound → (c : γ) → m (ForInStep γ)) : m γ :=
      haveI : Nonempty (m γ) := ⟨mPure acc⟩
      WellFounded.extrinsicFix₃ (C₃ := fun _ _ _ => m γ)
        (InvImage (IteratorLoop.rel _ Id (fun _ _ _ => True))
          (fun x => (⟨Rxo.Iterator.mk (some x.1) upperBound⟩, x.2.1)))
        (fun next acc (h : LargeEnough next) G => rdo
          if hu : next < upperBound then
            match ← f next h hu acc with
            | .yield acc' =>
              match hs : UpwardEnumerable.succ? next with
              | some next' => G next' acc' (hl _ _ ?hle' h) ?decreasing
              | none => mPure acc'
            | .done acc' => mPure acc'
          else
            mPure acc) next acc h
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact UpwardEnumerable.le_trans hna hab
    case hle' =>
      refine ⟨1, ?_⟩
      simpa [succMany?_one] using hs
    case hle'' =>
      exact UpwardEnumerable.le_refl _
    case decreasing =>
      simp_wf; simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

private noncomputable def Iterator.instMeasurableSpaceIteratorLoop.loop.wf
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]
    (γ : Type u) [MeasurableSpace γ]
    (wf : IteratorLoop.WellFounded (Rxo.Iterator α) Id (γ := γ) (fun _ _ _ => True))
    (LargeEnough : α → Prop)
    (hl : ∀ a b : α, UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b)
    (upperBound : α) (acc : γ) (next : α) (h : LargeEnough next)
    (f : (out : α) → LargeEnough out → out < upperBound → (c : γ) → m (ForInStep γ)) :
    m γ := rdo
  if hu : next < upperBound then
    match ← f next h hu acc with
    | .yield acc' =>
      match hs : UpwardEnumerable.succ? next with
      | some next' =>
        loop.wf γ wf LargeEnough hl upperBound acc' next' (hl _ _ ?hle h) f
      | none => return acc'
    | .done acc' => return acc'
  else
    return acc
termination_by IteratorLoop.WithWF.mk ⟨⟨some next, upperBound⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]
where finally
  case hle =>
    refine ⟨1, ?_⟩
    simpa [succMany?_one] using hs

private theorem Iterator.instMeasurableSpaceIteratorLoop.loop_eq_wf
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]
    {γ : Type u} [MeasurableSpace γ] {LargeEnough hl upperBound} {next hn} {acc} (wf f) :
    loop γ LargeEnough hl upperBound acc next hn f =
      loop.wf (α := α) (m := m) γ wf LargeEnough hl upperBound acc next hn f := by
  have : Nonempty (m γ) := ⟨mPure acc⟩
  rw [loop, WellFounded.extrinsicFix₃_eq_fix]; rotate_left
  · exact InvImage.wf _ wf
  · fun_induction loop.wf γ wf LargeEnough hl upperBound acc next hn f
    · rw [WellFounded.fix_eq]
      simp only [↓reduceDIte, *]
      apply MeasurableSpaceBind.bind_congr; intro forInStep
      split
      · split
        · simp_all
        · simp
      · simp
    · rw [WellFounded.fix_eq]
      simp_all

private theorem Iterator.instMeasurableSpaceIteratorLoop.loopWf_eq
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]
    (γ : Type u) [MeasurableSpace γ]
    {lift : ∀ (δ : Type w) (ε : Type u) [MeasurableSpace ε], (δ → m ε) → Id δ → m ε}
    (hlift : ∀ δ ε [MeasurableSpace ε] (f : δ → m ε) a, lift δ ε f (pure a) = f a)
    (wf : IteratorLoop.WellFounded (Rxo.Iterator α) Id (γ := γ) (fun _ _ _ => True))
    (LargeEnough : α → Prop)
    (hl : ∀ a b : α, UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b)
    (upperBound : α) (acc : γ) (next : α) (h : LargeEnough next)
    (f : (out : α) → LargeEnough out → out < upperBound → (c : γ) → m (ForInStep γ)) :
    loop.wf γ wf LargeEnough hl upperBound acc next h f = (rdo
      if hu : next < upperBound then
        match ← f next h hu acc with
        | .yield acc' =>
          letI it' : IterM (α := Rxo.Iterator α) Id α := ⟨⟨succ? next, upperBound⟩⟩
          measurableSpaceForIn' (n := Id) (m := m) lift γ it' acc'
            it'.IsPlausibleIndirectOutput (fun _ => id)
            fun next' h acc' => f next'
              (by
                refine hl next next' ?_ ‹_›
                simp only [it', Monadic.isPlausibleIndirectOutput_iff,
                  ← succMany?_add_one_eq_succ?_bind_succMany?] at h
                exact ⟨h.choose + 1, h.choose_spec.1⟩)
              (by
                simp only [it', Monadic.isPlausibleIndirectOutput_iff] at h
                exact h.choose_spec.2)
              acc'
        | .done acc' => return acc'
      else return acc) := by
  have : Nonempty (m γ) := ⟨mPure acc⟩
  rw [loop.wf]
  congr 1; ext hu
  apply MeasurableSpaceBind.bind_congr; intro forInStep
  split
  · split
    · rw [loopWf_eq (lift := lift) _ hlift wf]
      rw [measurableSpaceForIn'_eq_match_step (lift := lift) wf]
      · simp only [Std.IterM.step_eq, Monadic.step,
          Shrink.inflate_deflate, *]
        split
        · apply MeasurableSpaceBind.bind_congr; intro forInStep
          split
          · apply measurableSpaceForIn'_congr wf ; intros; rfl
          · simp
        · simp
    · rw [measurableSpaceForIn'_eq_match_step wf]
      simp [Std.IterM.step_eq, Monadic.step, *]
  · simp
termination_by IteratorLoop.WithWF.mk ⟨⟨some next, upperBound⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

instance Iterator.instLawfulMeasurableSpaceIteratorLoop [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m] :
    LawfulMeasurableSpaceIteratorLoop (Rxo.Iterator α) Id m where
  lawful := by
    intro lift hlift γ _ it init wf f
    simp only [MeasurableSpaceIteratorLoop.forIn]
    rw [measurableSpaceForIn'_eq_match_step wf]
    split; rotate_left
    · simp only [Std.IterM.step_eq, hlift, Shrink.inflate_deflate]
      simp [Monadic.step]
    rename_i next _
    rw [instMeasurableSpaceIteratorLoop.loop_eq_wf wf,
      instMeasurableSpaceIteratorLoop.loopWf_eq (lift := lift) _ hlift wf]
    simp only [Std.IterM.step_eq, hlift, Shrink.inflate_deflate]
    simp only [Monadic.step]
    split
    · apply MeasurableSpaceBind.bind_congr; intro forInStep
      split
      · apply measurableSpaceForIn'_congr wf
        intros; rfl
      · rfl
    · rfl

end Rxo

namespace Rxi

open Std.Rxi Std.Rxi.Iterator

variable {α : Type w}

/-- Direct range iteration without allocating the `Option` that records exhaustion on each step.
Analogue of `Std.Rxi.Iterator.instIteratorLoop`. -/
@[always_inline, inline]
instance Iterator.instMeasurableSpaceIteratorLoop [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m] :
    MeasurableSpaceIteratorLoop (Rxi.Iterator α) Id m where
  forIn _ γ _ it init f :=
    match it with
    | ⟨⟨some next⟩⟩ =>
      loop γ (UpwardEnumerable.LE next ·) (fun a b hab hna => ?hle)
        init next ?hle'' (fun a ha c => f a ?hf c)
    | ⟨⟨none⟩⟩ => mPure init
  where
    @[always_inline, inline]
    loop (γ : Type u) [MeasurableSpace γ]
        (LargeEnough : α → Prop)
        (hl : ∀ a b : α, UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b)
        (acc : γ) (next : α) (h : LargeEnough next)
        (f : (out : α) → LargeEnough out → (c : γ) → m (ForInStep γ)) : m γ :=
      haveI : Nonempty (m γ) := ⟨mPure acc⟩
      WellFounded.extrinsicFix₃ (C₃ := fun _ _ _ => m γ)
        (InvImage (IteratorLoop.rel _ Id (fun _ _ _ => True))
          (fun x => (⟨Rxi.Iterator.mk (some x.1)⟩, x.2.1)))
        (fun next acc (h : LargeEnough next) G => rdo
          match ← f next h acc with
          | .yield acc' =>
            match hs : UpwardEnumerable.succ? next with
            | some next' => G next' acc' (hl _ _ ?hle' h) ?decreasing
            | none => mPure acc'
          | .done acc' => mPure acc') next acc h
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      exact ha
    case hle =>
      exact UpwardEnumerable.le_trans hna hab
    case hle' =>
      refine ⟨1, ?_⟩
      simpa [succMany?_one] using hs
    case hle'' =>
      exact UpwardEnumerable.le_refl _
    case decreasing =>
      simp_wf; simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

private noncomputable def Iterator.instMeasurableSpaceIteratorLoop.loop.wf [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]
    (γ : Type u) [MeasurableSpace γ]
    (wf : IteratorLoop.WellFounded (Rxi.Iterator α) Id (γ := γ) (fun _ _ _ => True))
    (LargeEnough : α → Prop)
    (hl : ∀ a b : α, UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b)
    (acc : γ) (next : α) (h : LargeEnough next)
    (f : (out : α) → LargeEnough out → (c : γ) → m (ForInStep γ)) :
    m γ := rdo
    match ← f next h acc with
    | .yield acc' =>
      match hs : UpwardEnumerable.succ? next with
      | some next' =>
        loop.wf γ wf LargeEnough hl acc' next' (hl _ _ ?hle h) f
      | none => return acc'
    | .done acc' => return acc'
termination_by IteratorLoop.WithWF.mk ⟨⟨some next⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]
where finally
  case hle =>
    refine ⟨1, ?_⟩
    simpa [succMany?_one] using hs

private theorem Iterator.instMeasurableSpaceIteratorLoop.loop_eq_wf [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]
    {γ : Type u} [MeasurableSpace γ] {LargeEnough hl} {next hn} {acc} (wf f) :
    loop γ LargeEnough hl acc next hn f =
      loop.wf (α := α) (m := m) γ wf LargeEnough hl acc next hn f := by
  have : Nonempty (m γ) := ⟨mPure acc⟩
  rw [loop, WellFounded.extrinsicFix₃_eq_fix]; rotate_left
  · exact InvImage.wf _ wf
  · fun_induction loop.wf γ wf LargeEnough hl acc next hn f
    · rw [WellFounded.fix_eq]
      dsimp only
      apply MeasurableSpaceBind.bind_congr; intro forInStep
      split
      · split
        · simp_all
        · simp
      · simp

private theorem Iterator.instMeasurableSpaceIteratorLoop.loopWf_eq [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m]
    (γ : Type u) [MeasurableSpace γ]
    {lift : ∀ (δ : Type w) (ε : Type u) [MeasurableSpace ε], (δ → m ε) → Id δ → m ε}
    (hlift : ∀ δ ε [MeasurableSpace ε] (f : δ → m ε) a, lift δ ε f (pure a) = f a)
    (wf : IteratorLoop.WellFounded (Rxi.Iterator α) Id (γ := γ) (fun _ _ _ => True))
    (LargeEnough : α → Prop)
    (hl : ∀ a b : α, UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b)
    (acc : γ) (next : α) (h : LargeEnough next)
    (f : (out : α) → LargeEnough out → (c : γ) → m (ForInStep γ)) :
    loop.wf γ wf LargeEnough hl acc next h f = (rdo
        match ← f next h acc with
        | .yield acc' =>
          letI it' : IterM (α := Rxi.Iterator α) Id α := ⟨⟨succ? next⟩⟩
          measurableSpaceForIn' (n := Id) (m := m) lift γ it' acc'
            it'.IsPlausibleIndirectOutput (fun _ => id)
            fun next' h acc' => f next'
              (by
                refine hl next next' ?_ ‹_›
                simp only [it', Monadic.isPlausibleIndirectOutput_iff,
                  ← succMany?_add_one_eq_succ?_bind_succMany?] at h
                exact ⟨h.choose + 1, h.choose_spec⟩)
              acc'
        | .done acc' => return acc') := by
  have : Nonempty (m γ) := ⟨mPure acc⟩
  rw [loop.wf]
  apply MeasurableSpaceBind.bind_congr; intro forInStep
  split
  · split
    · rw [loopWf_eq (lift := lift) _ hlift wf]
      rw [measurableSpaceForIn'_eq_match_step (lift := lift) wf]
      · simp only [Monadic.step_eq_step, Monadic.step,
          Shrink.inflate_deflate, *]
        apply MeasurableSpaceBind.bind_congr; intro forInStep
        split
        · apply measurableSpaceForIn'_congr wf ; intros; rfl
        · simp
    · rw [measurableSpaceForIn'_eq_match_step wf]
      simp [Monadic.step_eq_step, Monadic.step, *]
  · simp
termination_by IteratorLoop.WithWF.mk ⟨⟨some next⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

instance Iterator.instLawfulMeasurableSpaceIteratorLoop [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    {m : (β : Type u) → [MeasurableSpace β] → Type v} [MeasurableSpaceMonad m] :
    LawfulMeasurableSpaceIteratorLoop (Rxi.Iterator α) Id m where
  lawful := by
    intro lift hlift γ _ it init wf f
    simp only [MeasurableSpaceIteratorLoop.forIn]
    rw [measurableSpaceForIn'_eq_match_step wf]
    split; rotate_left
    · simp only [Monadic.step_eq_step, hlift, Shrink.inflate_deflate]
      simp [Monadic.step]
    rename_i next _
    rw [instMeasurableSpaceIteratorLoop.loop_eq_wf wf,
      instMeasurableSpaceIteratorLoop.loopWf_eq (lift := lift) _ hlift wf]
    simp only [Monadic.step_eq_step, hlift, Shrink.inflate_deflate]
    simp only [Monadic.step]
    apply MeasurableSpaceBind.bind_congr; intro forInStep
    split
    · apply measurableSpaceForIn'_congr wf
      intros; rfl
    · rfl

end Rxi

/-! ## Direct range instances

As in core, these instances are defaults so that the element type can determine the range's
endpoint type. The `Finite` assumptions retain core's termination requirements; the implementations
reuse the consumers above.
-/

variable {α : Type w} {m : (β : Type u) → [MeasurableSpace β] → Type v}
  {β : Type u} [MeasurableSpace β]

namespace Rcc

open Std.Rcc

variable [UpwardEnumerable α]
  [LE α] [DecidableLE α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
  [MeasurableSpaceMonad m]

@[no_expose, default_instance, nolint unusedArguments]
instance instMeasurableSpaceForIn' [Finite (Rxc.Iterator α) Id] :
    MeasurableSpaceForIn' m (Rcc α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instMeasurableSpaceForIn' (ι := Rxc.Iterator α) (m := m)
    refine MeasurableSpaceForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

/-- A range loop is the corresponding iterator loop. -/
theorem forIn_eq_forIn_iter [Finite (Rxc.Iterator α) Id]
    (r : Rcc α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn r init f = MeasureTheory.forIn (Internal.iter r) init f := by
  rfl

end Rcc

namespace Rco

open Std.Rco

variable [UpwardEnumerable α] [LE α] [LT α] [DecidableLT α]
  [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
  [MeasurableSpaceMonad m]

@[no_expose, default_instance, nolint unusedArguments]
instance instMeasurableSpaceForIn' [Finite (Rxo.Iterator α) Id] :
    MeasurableSpaceForIn' m (Rco α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instMeasurableSpaceForIn' (ι := Rxo.Iterator α) (m := m)
    refine MeasurableSpaceForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

/-- A range loop is the corresponding iterator loop. -/
theorem forIn_eq_forIn_iter [Finite (Rxo.Iterator α) Id]
    (r : Rco α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn r init f = MeasureTheory.forIn (Internal.iter r) init f := by
  rfl

end Rco

namespace Rci

open Std.Rci

variable [UpwardEnumerable α]
  [LE α]
  [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
  [MeasurableSpaceMonad m]

@[no_expose, default_instance, nolint unusedArguments]
instance instMeasurableSpaceForIn' [Finite (Rxi.Iterator α) Id] :
    MeasurableSpaceForIn' m (Rci α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instMeasurableSpaceForIn' (ι := Rxi.Iterator α) (m := m)
    refine MeasurableSpaceForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

/-- A range loop is the corresponding iterator loop. -/
theorem forIn_eq_forIn_iter [Finite (Rxi.Iterator α) Id]
    (r : Rci α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn r init f = MeasureTheory.forIn (Internal.iter r) init f := by
  rfl

end Rci

namespace Roc

open Std.Roc

variable [UpwardEnumerable α]
  [LE α] [DecidableLE α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
  [LT α] [LawfulUpwardEnumerableLT α]
  [MeasurableSpaceMonad m]

@[no_expose, default_instance, nolint unusedArguments]
instance instMeasurableSpaceForIn' [Finite (Rxc.Iterator α) Id] :
    MeasurableSpaceForIn' m (Roc α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instMeasurableSpaceForIn' (ι := Rxc.Iterator α) (m := m)
    refine MeasurableSpaceForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

/-- A range loop is the corresponding iterator loop. -/
theorem forIn_eq_forIn_iter [Finite (Rxc.Iterator α) Id]
    (r : Roc α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn r init f = MeasureTheory.forIn (Internal.iter r) init f := by
  rfl

end Roc

namespace Roo

open Std.Roo

variable [UpwardEnumerable α]
  [LT α] [DecidableLT α]
  [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
  [MeasurableSpaceMonad m]

@[no_expose, default_instance, nolint unusedArguments]
instance instMeasurableSpaceForIn' [Finite (Rxo.Iterator α) Id] :
    MeasurableSpaceForIn' m (Roo α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instMeasurableSpaceForIn' (ι := Rxo.Iterator α) (m := m)
    refine MeasurableSpaceForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

/-- A range loop is the corresponding iterator loop. -/
theorem forIn_eq_forIn_iter [Finite (Rxo.Iterator α) Id]
    (r : Roo α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn r init f = MeasureTheory.forIn (Internal.iter r) init f := by
  rfl

end Roo

namespace Roi

open Std.Roi

variable [UpwardEnumerable α]
  [LT α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
  [MeasurableSpaceMonad m]

@[no_expose, default_instance, nolint unusedArguments]
instance instMeasurableSpaceForIn' [Finite (Rxi.Iterator α) Id] :
    MeasurableSpaceForIn' m (Roi α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instMeasurableSpaceForIn' (ι := Rxi.Iterator α) (m := m)
    refine MeasurableSpaceForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

/-- A range loop is the corresponding iterator loop. -/
theorem forIn_eq_forIn_iter [Finite (Rxi.Iterator α) Id]
    (r : Roi α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn r init f = MeasureTheory.forIn (Internal.iter r) init f := by
  rfl

end Roi

namespace Ric

open Std.Ric

variable [UpwardEnumerable α]
  [LE α] [DecidableLE α] [Least? α]
  [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
  [LawfulUpwardEnumerableLeast? α]
  [MeasurableSpaceMonad m]

@[no_expose, default_instance, nolint unusedArguments]
instance instMeasurableSpaceForIn' [Finite (Rxc.Iterator α) Id] :
    MeasurableSpaceForIn' m (Ric α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instMeasurableSpaceForIn' (ι := Rxc.Iterator α) (m := m)
    refine MeasurableSpaceForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

/-- A range loop is the corresponding iterator loop. -/
theorem forIn_eq_forIn_iter [Finite (Rxc.Iterator α) Id]
    (r : Ric α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn r init f = MeasureTheory.forIn (Internal.iter r) init f := by
  rfl

end Ric

namespace Rio

open Std.Rio

variable [UpwardEnumerable α]
  [LT α] [DecidableLT α] [Least? α]
  [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
  [LawfulUpwardEnumerableLeast? α]
  [MeasurableSpaceMonad m]

@[no_expose, default_instance, nolint unusedArguments]
instance instMeasurableSpaceForIn' [Finite (Rxo.Iterator α) Id] :
    MeasurableSpaceForIn' m (Rio α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instMeasurableSpaceForIn' (ι := Rxo.Iterator α) (m := m)
    refine MeasurableSpaceForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

/-- A range loop is the corresponding iterator loop. -/
theorem forIn_eq_forIn_iter [Finite (Rxo.Iterator α) Id]
    (r : Rio α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn r init f = MeasureTheory.forIn (Internal.iter r) init f := by
  rfl

end Rio

namespace Rii

open Std.Rii

variable [UpwardEnumerable α] [Least? α]
  [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
  [MeasurableSpaceMonad m]

@[no_expose, default_instance, nolint unusedArguments]
instance instMeasurableSpaceForIn' [Finite (Rxi.Iterator α) Id] :
    MeasurableSpaceForIn' m (Rii α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instMeasurableSpaceForIn' (ι := Rxi.Iterator α) (m := m)
    refine MeasurableSpaceForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

/-- A range loop is the corresponding iterator loop. -/
theorem forIn_eq_forIn_iter [Finite (Rxi.Iterator α) Id]
    (r : Rii α) (init : β) (f : α → β → m (ForInStep β)) :
    MeasureTheory.forIn r init f = MeasureTheory.forIn (Internal.iter r) init f := by
  rfl

end Rii

end MeasureTheory
