/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Tactic.IsMarkov.Defs
public import RandomDo.Monad.MeasurableSpace

/-!
# Measurability of `ForInStep`

The body of a `for` loop in an `rdo`-block returns a `ForInStep β`: `yield b` to carry on with `b`
as the new state, `done b` to stop the loop there. Carrying measurability, and then the Markov
property, through a loop therefore means carrying them through that type, whose σ-algebra is the
largest one making both `ForInStep.yield` and `ForInStep.done` measurable.

## Main definitions
* `ForInStep.isDone`: whether a `ForInStep` stops the loop or carries on with it.

## Main results
* `measurable_yield`, `measurable_run`, `measurable_isDone`: the maps relating `ForInStep β` to `β`
  and to `Bool` are measurable.
* The points of `ForInStep β` are measurable as soon as those of `β` are, and `ForInStep.yield` is a
  measurable embedding.
* `measurable_CasesOn`: a case analysis on a `ForInStep`, measurable in each of its two branches, is
  measurable.
* `IsMarkov.forInStepCasesOn`: the same statement for the Markov property.
-/

@[expose] public section

open MeasureTheory

namespace ForInStep

variable {β : Type*}

/-- Whether a `ForInStep` stops the loop it is the result of, or carries on with it. -/
def isDone : ForInStep β → Bool
  | .done _ => true
  | .yield _ => false

@[simp]
lemma isDone_done (b : β) : (ForInStep.done b).isDone = true := rfl

@[simp]
lemma isDone_yield (b : β) : (ForInStep.yield b).isDone = false := rfl

variable {α γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

@[fun_prop]
lemma measurable_done : Measurable (ForInStep.done : β → ForInStep β) := fun _ hs => hs.2

@[fun_prop]
lemma measurable_yield : Measurable (ForInStep.yield : β → ForInStep β) := fun _ hs => hs.1

@[fun_prop]
lemma measurable_run : Measurable (ForInStep.run : ForInStep β → β) := fun _ hs => ⟨hs, hs⟩

/-- The points of `ForInStep β` are measurable as soon as those of `β` are. -/
instance [MeasurableSingletonClass β] : MeasurableSingletonClass (ForInStep β) where
  measurableSet_singleton t := by
    -- A singleton's preimages under `yield` and `done` are a singleton and the empty set.
    constructor <;> cases t <;> change MeasurableSet (_ ⁻¹' _) <;> simp [Set.preimage]

lemma measurableEmbedding_yield : MeasurableEmbedding (ForInStep.yield : β → ForInStep β) where
  injective _ _ h := ForInStep.yield.inj h
  measurable := measurable_yield
  measurableSet_image' S hS := by
    refine ⟨?_, ?_⟩
    · change MeasurableSet (ForInStep.yield ⁻¹' _)
      rwa [Set.preimage_image_eq _ fun _ _ h ↦ ForInStep.yield.inj h]
    · change MeasurableSet (ForInStep.done ⁻¹' _)
      convert MeasurableSet.empty (α := β)
      ext; simp

instance [Countable β] : Countable (ForInStep β) :=
  Function.Injective.countable (f := fun t : ForInStep β ↦ (t.isDone, t.run)) <| by
    rintro (_ | _) (_ | _) h <;> simp_all

@[fun_prop]
lemma measurable_isDone : Measurable (ForInStep.isDone : ForInStep β → Bool) := by
  intro s _
  constructor <;>
  · change MeasurableSet (_ ⁻¹' (ForInStep.isDone ⁻¹' s))
    first
    | (by_cases h : (false : Bool) ∈ s
       · convert MeasurableSet.univ using 1; ext b; simp [h]
       · convert MeasurableSet.empty using 1; ext b; simp [h])
    | (by_cases h : (true : Bool) ∈ s
       · convert MeasurableSet.univ using 1; ext b; simp [h]
       · convert MeasurableSet.empty using 1; ext b; simp [h])

@[fun_prop]
lemma measurable_CasesOn {done yield : α → γ → β}
    (h_done : Measurable fun p : α × γ ↦ done p.1 p.2)
    (h_yield : Measurable fun p : α × γ ↦ yield p.1 p.2) :
    Measurable fun q : α × ForInStep γ ↦
      ForInStep.casesOn (motive := fun _ ↦ β) q.2 (done q.1) (yield q.1) := by
  suffices (fun q : α × ForInStep γ ↦ ForInStep.casesOn q.2 (done q.1) (yield q.1)) =
      (fun q ↦ if q.2.isDone then done q.1 q.2.run else yield q.1 q.2.run) by
    rw [this]
    exact Measurable.ite (by measurability) (by fun_prop) (by fun_prop)
  ext ⟨c, s⟩
  cases s <;> simp [ForInStep.run]

lemma _root_.IsMarkov.forInStepCasesOn {done yield : α → γ → Measure β}
  (h_done : IsMarkov fun p : α × γ ↦ done p.1 p.2)
  (h_yield : IsMarkov fun p : α × γ ↦ yield p.1 p.2) :
  IsMarkov fun q : α × ForInStep γ ↦
    ForInStep.casesOn (motive := fun _ ↦ Measure β) q.2 (done q.1) (yield q.1) := by
  refine ⟨by fun_prop, ?_⟩
  rintro ⟨c, s⟩
  cases s with
  | done b => exact h_done.isProbabilityMeasure (c, b)
  | yield b => exact h_yield.isProbabilityMeasure (c, b)

end ForInStep
