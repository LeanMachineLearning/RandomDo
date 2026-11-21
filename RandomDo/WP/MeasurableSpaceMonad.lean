/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.Defs
public import Std.WP.Triple.SpecLemmas
public import Std.WP.Monad.Instances
public import Std.WP.Gadget.Assert

/-!
# Weakest-precondition interpretations of measurable space monads

This file defines the `WPMeasurableSpaceMonad` class which provides an API for defining and
using (monadic) weakest preconditions for measurable space monads. It is the analogue
of core Lean's `WPMonad`.
-/

@[expose] public section

open Lean.Order MeasureTheory Std.WP

universe u v w w'

namespace Std.WP

/-- Weakest precondition measurable space monad: A measurable space monad `m` whose weakest
precondition interpretation is sound for `mPure` and `mBind`.
Analogue of core Lean's `Std.WP.WPMonad`. -/
class WPMeasurableSpaceMonad (m : (α : Type u) → [MeasurableSpace α] → Type v)
    (Pred : outParam (Type w)) (EPred : outParam (Type w'))
    [MeasurableSpaceMonad m] [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    [Assertion Pred] [MeasurableSpace Pred] [Assertion EPred]
    extends LawfulMeasurableSpaceMonad m where
  /-- The weakest precondition interpretation of `m` at every measurable result type. -/
  toWP : ∀ α, [MeasurableSpace α] → WP (m α) α Pred EPred
  /-- A measurable postcondition gives a measurable weakest precondition. -/
  measurable_wp {α : Type u} [MeasurableSpace α] {post : α → Pred}
    (hpost : Measurable post) (epost : EPred) :
    Measurable (fun x : m α ↦ (toWP α).wp x post epost)
  /-- Soundness of `mPure`: the postcondition applied to `x` implies the weakest
  precondition of `mPure x`. -/
  mPure_le_wp_mPure {α : Type u} [MeasurableSpace α]
    (x : α) (post : α → Pred) (epost : EPred) (hpost : Measurable post) :
    post x ⊑ (toWP α).wp (mPure (f := m) x) post epost
  /-- Soundness of `mBind`: composing weakest preconditions is at least as strong as the weakest
  precondition of `>>=ₘ`. -/
  mBind_le_wp_mBind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred)
    (hf : Measurable f) (hpost : Measurable post) :
    (toWP α).wp x (fun a ↦ (toWP β).wp (f a) post epost) epost ⊑
      (toWP β).wp (x >>=ₘ f) post epost

attribute [fun_prop] WPMeasurableSpaceMonad.measurable_wp

-- Reuse core's `Id` weakest-precondition interpretation for `MId`.
#check Std.WP.Id.instWPMonad

instance : WPMeasurableSpaceMonad MId Prop EStack⟨⟩ where
  toWP _ := inferInstanceAs (WP (Id _) _ Prop EStack⟨⟩)
  measurable_wp hpost _ := hpost
  mPure_le_wp_mPure _ _ _ _ := PartialOrder.rel_refl
  mBind_le_wp_mBind _ _ _ _ _ _ := PartialOrder.rel_refl

end Std.WP

variable {m : (α : Type u) → [MeasurableSpace α] → Type v}
  [MeasurableSpaceMonad m] [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  {Pred : Type w} {EPred : Type w'} [Assertion Pred] [MeasurableSpace Pred] [Assertion EPred]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
  {pre : Pred} {epost : EPred}

namespace Std.WP

/-- A monadic `WP` interpretation is sourced from the monad's `WPMeasurableSpaceMonad` instance.
Low priority so a program type with a bespoke `WP` (e.g. a non-monadic one) is preferred. -/
instance (priority := low) WPMeasurableSpaceMonad.instWP
    [inst : WPMeasurableSpaceMonad m Pred EPred] : WP (m α) α Pred EPred :=
  inst.toWP α

variable [WPMeasurableSpaceMonad m Pred EPred]

theorem WPMeasurableSpaceMonad.mMap_le_wp_mMap (f : α → β) (x : m α) (hf : Measurable f) :
    ∀ post epost, Measurable post →
      wp x (fun a => post (f a)) epost ⊑ wp (f <$>ₘ x) post epost := by
  intro post epost hpost
  rw [← mBind_mPure_comp hf]
  apply PartialOrder.rel_trans; rotate_left
  · exact mBind_le_wp_mBind x (mPure <| f ·) post epost (by fun_prop) hpost
  apply WP.wp_consequence
  intro a; exact mPure_le_wp_mPure (f a) post epost hpost

namespace Triple

theorem mPure {post : α → Pred} (a : α) (h : pre ⊑ post a) (hpost : Measurable post) :
    Triple (MeasureTheory.mPure (f := m) a) pre post epost :=
  ⟨PartialOrder.rel_trans h (WPMeasurableSpaceMonad.mPure_le_wp_mPure a post epost hpost)⟩

theorem mBind {post : β → Pred} (x : m α) (f : α → m β) (mid : α → Pred)
    (hx : Triple x pre mid epost) (hf : ∀ a, Triple (f a) (mid a) post epost)
    (hf_meas : Measurable f) (hpost : Measurable post) :
    Triple (x >>=ₘ f) pre post epost :=
  ⟨PartialOrder.rel_trans hx.le_wp
    (PartialOrder.rel_trans
      (WP.wp_consequence x mid (fun a => wp (f a) post epost) epost (fun a => (hf a).le_wp))
      (WPMeasurableSpaceMonad.mBind_le_wp_mBind x f post epost hf_meas hpost))⟩

theorem mMap {post : β → Pred} (f : α → β) (x : m α)
    (h : Triple x pre (fun a => post (f a)) epost)
    (hf : Measurable f) (hpost : Measurable post) :
    Triple (f <$>ₘ x) pre post epost :=
  ⟨PartialOrder.rel_trans h.le_wp
    (WPMeasurableSpaceMonad.mMap_le_wp_mMap f x hf post epost hpost)⟩

end Triple

@[spec] theorem Spec.mPure (a : α) {post : α → Pred} (hpost : Measurable post) :
    Triple (MeasureTheory.mPure (f := m) a) (post a) post epost :=
  Triple.mPure a PartialOrder.rel_refl hpost

@[spec] theorem Spec.mBind (x : m α) (f : α → m β) {post : β → Pred}
    (hf : Measurable f) (hpost : Measurable post) :
    Triple (x >>=ₘ f) (wp x (fun a => binderNameHint a f (wp (f a) post epost)) epost)
      post epost :=
  Triple.mBind x f (fun a => wp (f a) post epost)
    (Triple.intro PartialOrder.rel_refl) (fun _ => Triple.intro PartialOrder.rel_refl) hf hpost

@[spec] theorem Spec.mMap (f : α → β) (x : m α) {post : β → Pred}
    (hf : Measurable f) (hpost : Measurable post) :
    Triple (f <$>ₘ x) (wp x (fun a => post (f a)) epost) post epost :=
  Triple.mMap f x (Triple.intro PartialOrder.rel_refl) hf hpost

end Std.WP

section Assert

namespace MeasureTheory.WP

set_option linter.unusedVariables false in
/-- A no-op computation used as a verification gadget to inject assertions into the program.

The `as` parameter is the assertion to be checked. At runtime, `assertGadget` is simply
`mPure ⟨⟩`. Analogue of core's `Std.WP.Gadget.assertGadget`. -/
@[nolint unusedArguments]
def assertGadget [WPMeasurableSpaceMonad m Pred EPred] (as : Pred) : m PUnit := mPure ⟨⟩

variable [WPMeasurableSpaceMonad m Pred EPred]

@[fun_prop] theorem measurable_assertGadget {α : Type*} [MeasurableSpace α] (as : α → Pred) :
    Measurable (fun a => assertGadget (m := m) (as a)) := measurable_const

@[spec] theorem Spec.assertGadget (as : Pred) [Heyting Pred]
    {post : PUnit → Pred} :
    Triple (WP.assertGadget (m := m) as) (as ⊓ (as ⇨ post ⟨⟩)) post epost := by
  simpa [WP.assertGadget] using
    (Triple.mPure (m := m) (pre := as ⊓ (as ⇨ post ⟨⟩)) (post := post) (epost := epost)
      ⟨⟩ meet_himp_le (by fun_prop))

end MeasureTheory.WP

end Assert
