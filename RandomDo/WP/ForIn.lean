/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.MeasurableSpaceMonad.ForInInstances.List
public import RandomDo.WP.MeasurableSpaceMonad
public import Std.WP.Gadget.ForIn

/-!
# Loop-invariant annotations for measurable space monads

These wrappers retain loop annotations in the elaborated program for verification tools.
They are definitionally the corresponding `mForIn` or `mForIn'` call; annotations do not affect
execution. Import this file to use `invariant` clauses in `rdo` loops.

Core's `Invariant` and `WhileInvariant` types are reused. The wrappers require only the iteration
instance and a measurable space on the loop state, not a weakest-precondition interpretation.
The collection-loop specifications reduce to list iteration through `PureMeasurableSpaceForIn`
and `PureMeasurableSpaceForIn'`.

Unbounded-loop specifications use the one-step equation from `LawfulMeasurableSpaceLoop`
and core's well-founded `Variant` interface. They also require measurability of the loop in
its initial state. Quantitative almost-sure-termination rules for `Measure` are provided
separately in `RandomDo.WP.Measure.Loop`.

## Main theorems

* `Spec.mForInPure`, `Spec.mForInPure'`: verify annotated collection loops using their invariants.
* `Spec.mForIn_list`, `Spec.mForIn'_list`: the underlying list-loop specifications.
* `Spec.mForIn_loop`: verify an unbounded loop with an invariant and a well-founded variant.

The specifications require the loop body to be measurable in the state and the invariant at loop
exit to be measurable. The step hypotheses supply triples for the body; establishing those triples
may require further measurability hypotheses. The collection's elements need no measurable space.
-/

@[expose] public section

namespace MeasureTheory.WP

open Std.WP Lean.Order

universe u u₁ u₂ v w

section List

universe uₚ uₑ

variable {α : Type u₁} {β : Type u₂}
  {m : (α : Type u₂) → [MeasurableSpace α] → Type v}
  {Pred : Type uₚ} {EPred : Type uₑ}
  [MeasurableSpaceMonad m] [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]
  [Assertion Pred] [MeasurableSpace Pred] [Assertion EPred] [WPMeasurableSpaceMonad m Pred EPred]
  [MeasurableSpace β]

@[spec] theorem Spec.mForIn'_list
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant α β Pred) {epost : EPred}
    (hf : ∀ a h, Measurable (f a h)) (hinv : Measurable (inv xs []))
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [h]) b)
        (inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv xs [] b')
        epost) :
    Triple (mForIn' xs init f) (inv [] xs init) (fun b => inv xs [] b) epost := by
  suffices h : ∀ pref suff (hxs : xs = pref ++ suff),
      Triple
        (mForIn' (m := m) suff init (fun a ha => f a (by simp [hxs, ha])))
        (inv pref suff init)
        (fun b => inv xs [] b)
        epost from h [] xs rfl
  intro pref suff hxs
  induction suff generalizing pref init with
  | nil =>
    apply Triple.mPure _ _ hinv
    simp [hxs]
    rfl
  | cons x suff ih =>
    rw [List.mForIn'_cons]
    refine Triple.mBind _ _ _ (step _ _ _ hxs init) ?_ (by fun_prop) hinv
    rintro (b | b)
    · exact Triple.mPure b (by rfl) hinv
    · exact ih (pref := pref ++ [x]) (by simp [hxs])

@[spec] theorem Spec.mForIn_list
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant α β Pred) {epost : EPred}
    (hf : ∀ a ∈ xs, Measurable (f a)) (hinv : Measurable (inv xs []))
    (step : ∀ pref cur suff (_h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv xs [] b')
        epost) :
    Triple (mForIn xs init f) (inv [] xs init) (fun b => inv xs [] b) epost :=
  Spec.mForIn'_list inv hf hinv step

end List

section MForInPure

variable {α : Type u₁} {β : Type (max u₁ u₂)}
  {m : (α : Type (max u₁ u₂)) → [MeasurableSpace α] → Type v}
  {Pred : Type (max u₁ u₂)} [MeasurableSpace β]

set_option linter.unusedVariables false in
/-- An `mForIn` loop annotated with its loop invariant, which `vcgen` reads from the `inv`
argument. It is definitionally `mForIn xs init f`, so the annotation is erased at runtime. The
invariant ranges over the elements consumed so far, the elements remaining, and the loop state.
Analogue of core Lean's `Std.WP.Gadget.forInPureWithInvariant`. -/
@[inline, nolint unusedArguments]
def mForInPureWithInvariant {ρ : Type w} [MeasurableSpaceForIn m ρ α]
    (xs : ρ) (init : β) (f : α → β → m (ForInStep β))
    (inv : Invariant α β Pred) : m β :=
  mForIn xs init f

set_option linter.unusedVariables false in
/-- A membership-aware `mForIn'` loop annotated with its loop invariant, which `vcgen` reads from
the `inv` argument. It is definitionally `mForIn' xs init f`, so the annotation is erased at
runtime. The invariant ranges over the elements consumed so far, the elements remaining, and the
loop state.
Analogue of core Lean's `Std.WP.Gadget.forInPureWithInvariant'`. -/
@[inline, nolint unusedArguments]
def mForInPureWithInvariant' {ρ : Type w} {d : Membership α ρ}
    [MeasurableSpaceForIn' m ρ α d] (xs : ρ) (init : β)
    (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : Invariant α β Pred) : m β :=
  mForIn' xs init f

open MeasureTheory.Internal Std.Internal

variable {EPred : Type (max u₁ u₂)}
  [MeasurableSpaceMonad m] [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]
  [Assertion Pred] [MeasurableSpace Pred] [Assertion EPred] [WPMeasurableSpaceMonad m Pred EPred]

-- As in core, pure traversal reduces the specification to the list rule. The extra hypotheses
-- are exactly the body and exit-postcondition measurability needed by that rule.

/-- Verify an annotated collection loop using its supplied invariant.
Analogue of core Lean's `Std.WP.Spec.forInPure`. -/
@[spec] theorem Spec.mForInPure {ρ : Type w} [MeasurableSpaceForIn m ρ α] [ForIn Id ρ α]
    [PureMeasurableSpaceForIn m ρ α]
    {xs : ρ} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant α β Pred) {epost : EPred}
    (hf : ∀ a ∈ ForIn.toList xs, Measurable (f a))
    (hinv : Measurable (inv (ForIn.toList xs) []))
    (step : ∀ pref cur suff (_h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (binderNameHint pref inv <| binderNameHint suff (inv pref) <|
          binderNameHint cur f <| binderNameHint b (inv pref (cur :: suff)) <|
          inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv (ForIn.toList xs) [] b')
        epost) :
    Triple
      (mForInPureWithInvariant xs init f inv)
      (inv [] (ForIn.toList xs) init)
      (fun b => binderNameHint b (inv (ForIn.toList xs) []) <| inv (ForIn.toList xs) [] b)
      epost := by
  rw [mForInPureWithInvariant, PureMeasurableSpaceForIn.mForIn_eq]
  exact Spec.mForIn_list inv hf hinv step

@[spec] theorem Spec.mForInPure' {ρ : Type w} {d : Membership α ρ}
    [MeasurableSpaceForIn' m ρ α d] [ForIn Id ρ α] [LawfulMemForInId ρ α]
    [PureMeasurableSpaceForIn' m ρ α]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant α β Pred) {epost : EPred}
    (hf : ∀ a h, Measurable (f a h)) (hinv : Measurable (inv (ForIn.toList xs) []))
    (step : ∀ pref cur suff (h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple
        (f cur (LawfulMemForInId.mem_toList_iff.mp (by simp [h])) b)
        (binderNameHint pref inv <| binderNameHint suff (inv pref) <|
          binderNameHint cur f <| binderNameHint b (inv pref (cur :: suff)) <|
          inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv (ForIn.toList xs) [] b')
        epost) :
    Triple
      (mForInPureWithInvariant' xs init f inv)
      (inv [] (ForIn.toList xs) init)
      (fun b => binderNameHint b (inv (ForIn.toList xs) []) <| inv (ForIn.toList xs) [] b)
      epost := by
  rw [mForInPureWithInvariant', PureMeasurableSpaceForIn'.mForIn'_eq]
  exact Spec.mForIn'_list inv (fun a _ => hf a _) hinv step

end MForInPure

section Loop

universe uₚ uₑ uγ'

open Std.Internal Assertion

-- Core obtains the `Lean.Loop` iterator from `Monad`. Here it is an explicit parameter:
-- choosing an unbounded-loop implementation is independent of retaining its annotations.

#check Std.WP.Gadget.forInLoopWithInvariant

set_option linter.unusedVariables false in
/-- A loop annotated with the invariant that `vcgen` reads from `inv`.
The annotation is erased at runtime. The invariant takes an exit flag, `false` while the
loop iterates and `true` once it is done. -/
@[inline, nolint unusedArguments]
def mForInLoopWithInvariant {β : Type u}
    {m : (α : Type u) → [MeasurableSpace α] → Type v} {Pred : Type uₚ}
    [MeasurableSpace β] [MeasurableSpaceForIn m Lean.Loop Unit]
    (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (inv : WhileInvariant β Pred) : m β :=
  mForIn l init f

#check Std.WP.Gadget.forInLoopWithVariant

set_option linter.unusedVariables false in
/-- A loop annotated with the termination measure that `vcgen` reads from `var`.
The annotation is erased at runtime. The measure is the function from which a `Variant`
is built in the assertion language used for verification. -/
@[inline, nolint unusedArguments]
def mForInLoopWithVariant {β : Type u}
    {m : (α : Type u) → [MeasurableSpace α] → Type v} {Fun : Type}
    [MeasurableSpace β] [MeasurableSpaceForIn m Lean.Loop Unit]
    (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (var : β → Fun) : m β :=
  mForIn l init f

#check Std.WP.Gadget.forInLoopWithInvariantAndVariant

set_option linter.unusedVariables false in
/-- A loop annotated with the invariant and termination measure that `vcgen` reads from
`inv` and `var`. Both annotations are erased at runtime. -/
@[inline, nolint unusedArguments]
def mForInLoopWithInvariantAndVariant {β : Type u}
    {m : (α : Type u) → [MeasurableSpace α] → Type v} {Pred : Type uₚ}
    {Fun : Type} [MeasurableSpace β] [MeasurableSpaceForIn m Lean.Loop Unit]
    (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (inv : WhileInvariant β Pred) (var : β → Fun) : m β :=
  mForIn l init f

variable {β : Type u} {m : (α : Type u) → [MeasurableSpace α] → Type v}
  {Pred : Type uₚ} {EPred : Type uₑ}
  [MeasurableSpace β] [MeasurableSpaceMonad m]
  [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
  [MeasurableSpaceForIn m Lean.Loop Unit] [LawfulMeasurableSpaceLoop m]
  [Assertion Pred] [MeasurableSpace Pred] [Assertion EPred]
  [WPMeasurableSpaceMonad m Pred EPred]

-- Core factors this proof through `Spec.repeatM`. We use the same well-founded induction
-- directly on `ForInStep`, so it applies to any implementation satisfying the loop equation.
-- Measurability of the recursive continuation and exit postcondition is explicit. Unlike
-- core's `MonadTail` prerequisite, this interface imposes no order on computations.
#check Std.WP.Spec.repeatM
#check Std.WP.Spec.forIn_loop

-- Core gives its analogue default priority. Here Measure's almost-sure-termination rules
-- take precedence when no decreasing annotation supplies a variant to this generic rule.
@[spec low] theorem Spec.mForIn_loop
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [∀ P : Pred, PreservesSup (meet P)]
    (measure : Variant β Pred) (inv : WhileInvariant β Pred) (einv : EPred)
    (hf : Measurable (f ())) (hloop : Measurable (fun b => mForIn l b f))
    (hinv : Measurable (inv true))
    (step : ∀ b (mb : measure.γ),
      Triple (f () b) (measure.EvalsTo b mb ⊓ inv false b)
        (fun r => match r with
          | .yield b' => measure.EvalsBelow b' mb ⊓ inv false b'
          | .done b' => inv true b') einv) :
    Triple (mForIn l init f) (inv false init) (fun b => inv true b) einv := by
  refine Triple.intro <| measure.le_of_total_le init ?_
  refine iSup_le _ _ fun minit => ?_
  suffices key : ∀ (n : measure.γ), Acc measure.rel n → ∀ b,
      Triple (mForIn l b f) (measure.EvalsTo b n ⊓ inv false b)
        (fun b => inv true b) einv
    from (key minit (measure.wf.apply minit) init).le_wp
  intro n hacc
  induction hacc with
  | intro n _ ih =>
    intro b
    rw [LawfulMeasurableSpaceLoop.mForIn_eq l b (f ()) hf]
    refine Triple.mBind (f () b)
      (fun r => match r with | .done b' => MeasureTheory.mPure b' | .yield b' => mForIn l b' f)
      (fun r => match r with
        | .yield b' => measure.EvalsBelow b' n ⊓ inv false b'
        | .done b' => inv true b') (step b n) ?_ (by fun_prop) hinv
    rintro (b' | b')
    · exact Triple.mPure b' Lean.Order.PartialOrder.rel_refl hinv
    · refine Triple.intro <| iSup_meet_le fun mb' => ?_
      rw [meet_comm (P := measure.EvalsTo b' mb'), meet_assoc]
      exact ofProp_meet_le_left fun hlt => (ih mb' hlt b').le_wp

-- These wrappers and proofs follow core; the extra hypotheses are those of the shared rule.
#check Std.WP.Spec.forInLoop_invariant_variant

@[spec]
theorem Spec.mForInLoop_invariant_variant {Fun : Type} {γ : Type uγ'}
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [NondetFun Pred Fun γ] [WellFoundedRelation γ] [∀ P : Pred, PreservesSup (meet P)]
    (measure : β → Fun)
    (inv : Bool → β → Pred)
    (einv : EPred)
    (hf : Measurable (f ())) (hloop : Measurable (fun b => mForIn l b f))
    (hinv : Measurable (inv true))
    (step : ∀ b (mb : γ),
      Triple
        (f () b)
        (binderNameHint b (inv false) <|
          (Variant.ofMeasure (Pred := Pred) measure).EvalsTo b mb ⊓ inv false b)
        (fun r => match r with
          | .yield b' =>
            (Variant.ofMeasure (Pred := Pred) measure).EvalsBelow b' mb ⊓ inv false b'
          | .done b' => inv true b')
        einv) :
    Triple
      (mForInLoopWithInvariantAndVariant l init f (WhileInvariant.mk inv) measure)
      (inv false init)
      (fun b => binderNameHint b (inv true) <| inv true b)
      einv := by
  unfold mForInLoopWithInvariantAndVariant
  exact Spec.mForIn_loop (Variant.ofMeasure measure) inv einv hf hloop hinv step

#check Std.WP.Spec.forInLoop_invariant

-- As for `Spec.mForIn_loop`, prefer specialized rules over inferring a missing variant.
@[spec low]
theorem Spec.mForInLoop_invariant
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [∀ P : Pred, PreservesSup (meet P)]
    (measure : Variant β Pred)
    (inv : Bool → β → Pred)
    (einv : EPred)
    (hf : Measurable (f ())) (hloop : Measurable (fun b => mForIn l b f))
    (hinv : Measurable (inv true))
    (step : ∀ b (mb : measure.γ),
      Triple
        (f () b)
        (binderNameHint b (inv false) <| measure.EvalsTo b mb ⊓ inv false b)
        (fun r => match r with
          | .yield b' => measure.EvalsBelow b' mb ⊓ inv false b'
          | .done b' => inv true b')
        einv) :
    Triple
      (mForInLoopWithInvariant l init f (WhileInvariant.mk inv))
      (inv false init)
      (fun b => binderNameHint b (inv true) <| inv true b)
      einv := by
  unfold mForInLoopWithInvariant
  exact Spec.mForIn_loop measure inv einv hf hloop hinv step

#check Std.WP.Spec.forInLoop_variant

@[spec]
theorem Spec.mForInLoop_variant {Fun : Type} {γ : Type uγ'}
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [NondetFun Pred Fun γ] [WellFoundedRelation γ] [∀ P : Pred, PreservesSup (meet P)]
    (measure : β → Fun)
    (inv : WhileInvariant β Pred)
    (einv : EPred)
    (hf : Measurable (f ())) (hloop : Measurable (fun b => mForIn l b f))
    (hinv : Measurable (inv true))
    (step : ∀ b (mb : γ),
      Triple
        (f () b)
        (binderNameHint b (inv false) <|
          (Variant.ofMeasure (Pred := Pred) measure).EvalsTo b mb ⊓ inv false b)
        (fun r => match r with
          | .yield b' =>
            (Variant.ofMeasure (Pred := Pred) measure).EvalsBelow b' mb ⊓ inv false b'
          | .done b' => inv true b')
        einv) :
    Triple
      (mForInLoopWithVariant l init f measure)
      (inv false init)
      (fun b => binderNameHint b (inv true) <| inv true b)
      einv := by
  unfold mForInLoopWithVariant
  exact Spec.mForIn_loop (Variant.ofMeasure measure) inv einv hf hloop hinv step

end Loop

end MeasureTheory.WP
