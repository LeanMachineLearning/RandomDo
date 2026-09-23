module

public import Test.Common

set_option linter.style.header false

/-!
# The random-variable monad

Check evaluation-domain inference across universes, measurability automation, and both the
operational and distribution semantics of an `rdo` program that changes its source state.
-/

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind MeasurableSpaceFunctor

@[expose] public section

namespace Test.RandomM

universe u w

section Abstract

variable {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [RandomM.MeasurableEvalDomain.{u, w} Ω P]
  {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

example : RandomM.MeasurableEval Ω P α := inferInstance

example {f : α → RandomM Ω P β} (hf : Measurable f) :
    Measurable (fun p : α × Ω ↦ (f p.1).sample p.2) := by fun_prop

example {f : α → RandomM Ω P β} (hf : Measurable f) :
    Measurable (fun x : RandomM Ω P α ↦ (x >>=ₘ f).law) := by fun_prop

example (x : RandomM Ω P α) {f : α → RandomM Ω P β} {g : β → RandomM Ω P γ}
    (hf : Measurable f) (hg : Measurable g) :
    x >>=ₘ f >>=ₘ g = x >>=ₘ fun a ↦ f a >>=ₘ g :=
  LawfulMeasurableSpaceMonad.mBind_assoc x hf hg

example (x : RandomM Ω P α) : x >>=ₘ mPure = x := by simp

example (x : RandomM Ω P α) {f : α → β} (hf : Measurable f) :
    (f <$>ₘ x).law = f <$>ₘ x.law := by
  rw [RandomM.law_mMap f hf, ← Measure.bind_dirac_eq_map x.law hf]
  rfl

end Abstract

/-! The countable-source instance also works for result spaces in higher universes. -/

example : RandomM.MeasurableEvalDomain.{u, 0} ℕ (Measure.dirac 0) := inferInstance

/-- Return the current state and halve it. Zero is preserved, so `dirac 0` is an invariant source.
Running at a nonzero state checks the exact state-passing semantics, even away from the support. -/
def halve : RandomM ℕ (Measure.dirac 0) ℕ where
  sample n := (n, n / 2)
  measurePreserving := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_dirac' (by fun_prop), Measure.map_dirac' (by fun_prop)]
    simp [Measure.dirac_prod_dirac]

/-- The second sampler sees the state left by the first. -/
noncomputable def twiceHalve : RandomM ℕ (Measure.dirac 0) ℕ := rdo
  let a ← halve
  let b ← halve
  return a + b

example : twiceHalve.sample 8 = (12, 2) := by
  simp (disch := fun_prop) [twiceHalve, halve]

example : twiceHalve.law = Measure.dirac 0 := by
  have h : halve.law = Measure.dirac 0 := by
    simp [RandomM.law, halve, Function.comp_def]
  simp (disch := fun_prop) [twiceHalve, h]

/-! Explicitly jointly measurable families can still be bound on an arbitrary source. -/

example {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {α : Type u} [MeasurableSpace α] (x : RandomM Ω P α) :
    RandomM.bindOfMeasurable x (fun a ↦ RandomM.pure a) (by fun_prop) = x := by
  apply RandomM.ext
  intro ω
  rfl

section SampleM

variable {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-! Constructing stream programs needs no evaluation-domain assumption. -/

noncomputable example :
    MeasurableSpaceMonad (SampleM Ω P : (α : Type u) → [MeasurableSpace α] → Type (max u w)) :=
  inferInstance

/-- Return a value without consuming any stream entries. -/
noncomputable def streamReturn (a : α) : SampleM Ω P α := rdo
  return a

example (a : α) (ω : ℕ → Ω) : (streamReturn (P := P) a).sample ω = (a, ω) := by
  simp [streamReturn]

example (a : α) : (streamReturn (P := P) a).law = Measure.dirac a := by
  simp [streamReturn]

/-- Bind stream samplers without requiring a global measurable-evaluation instance. -/
noncomputable def streamBind (x : SampleM Ω P α) (f : α → SampleM Ω P β) : SampleM Ω P β := rdo
  let a ← x
  f a

example (x : SampleM Ω P α) : streamBind x streamReturn = x := RandomM.bind_pure x

example (x : SampleM Ω P α) {f : α → β} (hf : Measurable f) :
    (f <$>ₘ x).law = x.law.map f := by simp [hf]

example (x : SampleM Ω P α) (f : α → SampleM Ω P β)
    (hf : Measurable (fun p : α × (ℕ → Ω) ↦ (f p.1).sample p.2)) (ω : ℕ → Ω) :
    (streamBind x f).sample ω = (f (x.sample ω).1).sample (x.sample ω).2 :=
  RandomM.sample_bind_of_measurable x f hf ω

example (x : SampleM Ω P α) (f : α → SampleM Ω P β)
    (hf : Measurable (fun p : α × (ℕ → Ω) ↦ (f p.1).sample p.2)) :
    (streamBind x f).law = x.law.bind (fun a ↦ (f a).law) :=
  RandomM.law_bind_of_measurable x f hf

example (x : SampleM Ω P α) (f : α → SampleM Ω P β) (g : β → SampleM Ω P γ)
    (hf : Measurable (fun p : α × (ℕ → Ω) ↦ (f p.1).sample p.2))
    (hg : Measurable (fun p : β × (ℕ → Ω) ↦ (g p.1).sample p.2)) :
    streamBind (streamBind x f) g = streamBind x (fun a ↦ streamBind (f a) g) :=
  RandomM.bind_assoc_of_measurable x hf hg

/-! The lawful instance still records the hypothesis on the full stream space. -/

example [RandomM.MeasurableEvalDomain.{u, w} (ℕ → Ω) (Measure.infinitePi fun _ : ℕ ↦ P)] :
    LawfulMeasurableSpaceMonad
      (SampleM Ω P : (α : Type u) → [MeasurableSpace α] → Type (max u w)) := inferInstance

end SampleM

end Test.RandomM

end
