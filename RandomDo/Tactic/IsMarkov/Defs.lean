/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Kernel.Defs

/-!
# `IsMarkov`

A function `κ : γ → Measure α` is a Markov kernel if it is measurable and every `κ c` is a
probability measure. This is a generalization of the `IsMarkovKernel` typeclass, which is defined
for `Kernel γ α` instead of `γ → Measure α`. The `IsMarkov` class allows to state that an arbitrary
function is a Markov kernel, without first proving that it of type `Kernel`.

## Main definitions
* `IsMarkov` states that the family of measures `κ : γ → Measure α` is a *Markov kernel*.
* `IsMarkov.toKernel` states that a family of measures `κ : γ → Measure α` endowed with `IsMarkov`
  is also a `Kernel` endowed with `IsMarkovKernel`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

variable {γ α : Type*} [MeasurableSpace γ] [MeasurableSpace α]

/-- `IsMarkov κ` states that the family of measures `κ : γ → Measure α` is a *Markov kernel*:
it is measurable, and every `κ c` is a probability measure. -/
class IsMarkov (κ : γ → Measure α) : Prop where
  /-- A Markov kernel is measurable as a map into the Giry monad. -/
  measurable' : Measurable κ
  /-- A Markov kernel takes values in probability measures. -/
  isProbabilityMeasure (c : γ) : IsProbabilityMeasure (κ c)

instance (κ : Kernel γ α) [IsMarkovKernel κ] : IsMarkov κ :=
  ⟨κ.measurable, fun _ ↦ inferInstance⟩

instance (μ : Measure α) [IsProbabilityMeasure μ] : IsMarkov fun _ : γ ↦ μ :=
  ⟨measurable_const, fun _ ↦ ‹_›⟩

namespace IsMarkov

@[fun_prop]
lemma measurable {κ : γ → Measure α} [IsMarkov κ] : Measurable κ :=
  IsMarkov.measurable'

lemma const {μ : Measure α} (h : IsProbabilityMeasure μ) : IsMarkov fun _ : γ ↦ μ :=
  ⟨measurable_const, fun _ ↦ h⟩

/-- A family of measures `κ : γ → Measure α` endowed with `IsMarkov` is also a `Kernel` endowed
with `IsMarkovKernel`. -/
def toKernel (κ : γ → Measure α) [IsMarkov κ] : Kernel γ α :=
  ⟨κ, IsMarkov.measurable⟩

instance (κ : γ → Measure α) [IsMarkov κ] : IsMarkovKernel (IsMarkov.toKernel κ) := by
  refine ⟨fun s ↦ ?_⟩
  simpa [IsMarkov.toKernel] using IsMarkov.isProbabilityMeasure s

lemma congr {κ η : γ → Measure α} [hη : IsMarkov η] (h : ∀ c, κ c = η c) : IsMarkov κ :=
  funext h ▸ hη

end IsMarkov
