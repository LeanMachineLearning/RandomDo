/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Verification.Measure
public import RandomDo.Tactic.IsMarkov.Lemmas

/-!
# Quantitative invariants for finite `rdo` loops

The invariant interface is Lean's existing `Std.Internal.Do.Invariant`: an assertion depending
on the consumed prefix, the remaining suffix, and the current accumulator. The loop rule below
also allows `break`. Measurability of the body and invariant is explicit; no probability-mass
assumption is needed.
-/

@[expose] public section

open MeasureTheory MeasurableSpacePure Std.Internal.Do
open scoped ENNReal

namespace ForInStep

/-- A case analysis on a loop step is measurable when both branches are measurable. -/
@[fun_prop] theorem measurable_cases {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {done yield : α → β} (hdone : Measurable done) (hyield : Measurable yield) :
    Measurable (fun s : ForInStep α ↦
      ForInStep.casesOn (motive := fun _ ↦ β) s done yield) :=
  fun _ ht ↦ ⟨hyield ht, hdone ht⟩

end ForInStep

namespace MeasureTheory.Measure

variable {ι α : Type*} [MeasurableSpace α]

/-- A finite measure-valued loop is measurable in its initial accumulator. -/
@[fun_prop] theorem measurable_forIn_list (xs : List ι)
    (f : ι → α → Measure (ForInStep α)) (hf : ∀ a ∈ xs, Measurable (f a)) :
    Measurable (fun b ↦ MeasurableSpaceForIn.forIn (m := Measure) xs b f) := by
  induction xs with
  | nil =>
    simpa only [IsMarkov.forIn_nil, mPure_def] using measurable_dirac
  | cons a xs ih =>
    simp only [IsMarkov.forIn_cons, mBind_def, mPure_def]
    exact (measurable_bind' (ForInStep.measurable_cases measurable_dirac
      (ih fun x hx ↦ hf x (List.mem_cons_of_mem a hx)))).comp (hf a (by simp))

/-- A quantitative invariant rule for finite list loops, including early termination.

This has the same invariant shape as Lean's ordinary `forIn` specification, so `vcgen` uses its
existing `invariants` syntax. The additional hypotheses ensure sound measure-theoretic bind.
-/
@[spec] theorem forIn_list_spec (xs : List ι) (init : α)
    (f : ι → α → Measure (ForInStep α)) (inv : Invariant ι α ℝ≥0∞) (E : EPost.Nil)
    (hf : ∀ a ∈ xs, Measurable (f a)) (hi : ∀ pref suff, Measurable (inv pref suff))
    (step : ∀ pref cur suff (_h : xs = pref ++ cur :: suff) b,
      Triple (f cur b) (inv pref (cur :: suff) b)
        (fun r ↦ match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv xs [] b') E) :
    Triple (MeasurableSpaceForIn.forIn (m := Measure) xs init f)
      (inv [] xs init) (inv xs []) E := by
  dsimp only [Invariant] at inv
  suffices h : ∀ suff pref (hxs : xs = pref ++ suff) b,
      Triple (MeasurableSpaceForIn.forIn (m := Measure) suff b f)
        (inv pref suff b) (inv xs []) E from h xs [] rfl init
  intro suff
  induction suff with
  | nil =>
    intro pref hxs b
    have hp : xs = pref := by simpa using hxs
    subst pref
    rw [IsMarkov.forIn_nil]
    exact mPure_spec_of_measurable b _ E (hi xs [])
  | cons cur suff ih =>
    intro pref hxs b
    rw [IsMarkov.forIn_cons]
    have htail : Measurable (fun b ↦
        MeasurableSpaceForIn.forIn (m := Measure) suff b f) :=
      measurable_forIn_list suff f fun a ha ↦ hf a (by simp [hxs, ha])
    refine ⟨?_⟩
    simp only [mPure_def]
    rw [wp_mBind _ _ _ _ (ForInStep.measurable_cases measurable_dirac htail) (hi xs [])]
    refine (step pref cur suff hxs b).le_wp.trans (lintegral_mono ?_)
    intro r
    cases r with
    | done b' => exact (wp_dirac_of_measurable b' (hi xs []) E).ge
    | yield b' =>
      exact (ih (pref ++ [cur]) (by simpa [List.append_assoc] using hxs) b').le_wp

end MeasureTheory.Measure
