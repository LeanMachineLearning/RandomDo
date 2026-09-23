module

public import Test.Common

set_option linter.style.header false

/-!
# Certified interpretations of unchanged polymorphic programs

The generated bridges relate the original definitions, interpreted in `RandomM` and `Measure`.
These tests include continuous outputs and dependent kernel draws, without assuming joint
evaluation on the entire sampler space. The recursive Bernoulli example is in `Test.SampleM`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Test.Program

universe u v w

/-- A program with two continuous draws. -/
@[rdo_program]
def addDraws {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] (x y : m ℝ) : m ℝ := rdo
  let a ← x
  let b ← y
  return a + b

example {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x y : RandomM Ω P ℝ) : (addDraws x y).law = addDraws x.law y.law :=
  addDraws.law x y

example {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x y : RandomM Ω P ℝ) : (addDraws.program x y).sampleSemantics = addDraws x y :=
  addDraws.sample_bridge x y

example {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x y : RandomM Ω P ℝ) : (addDraws.program x y).measureSemantics = addDraws x.law y.law :=
  addDraws.measure_bridge x y

example {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x y : RandomM Ω P ℝ) : (addDraws x y).law = addDraws x.law y.law := by
  have h := (addDraws.certified x y).law
  change (addDraws.program x y).sampleSemantics.law =
    (addDraws.program x y).measureSemantics at h
  simpa only [addDraws.sample_bridge, addDraws.measure_bridge] using h

/-- A measurable branch depending on a sampled real number. -/
@[rdo_program]
noncomputable def positivePart {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] (x : m ℝ) : m ℝ := rdo
  let a ← x
  if a ≤ 0 then return 0 else return a

example {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x : RandomM Ω P ℝ) : (positivePart x).law = positivePart x.law :=
  positivePart.law x

/-- A primitive draw can depend on a preceding continuous result. -/
@[rdo_program]
def dependentDraws {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] (x : m ℝ) (k : ℝ → m ℝ) : m ℝ := rdo
  let a ← x
  let b ← k a
  return a + b

example (x : SampleM unitInterval volume ℝ) (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    (dependentDraws x (SampleM.ofKernel κ)).law = dependentDraws x.law κ := by
  simpa only [SampleM.law_ofKernel] using
    dependentDraws.law x (SampleM.ofKernel κ) (by fun_prop)

/-- Result types may be universe polymorphic; supplied measurability proofs remain usable. -/
@[rdo_program]
def mapDraw {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (x : m α) (f : α → β) (_hf : Measurable f) : m β := rdo
  let a ← x
  return f a

example {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (x : RandomM Ω P α) (f : α → β) (hf : Measurable f) :
    (mapDraw x f hf).law = mapDraw x.law f hf :=
  mapDraw.law x f hf

/-- An arbitrary real function need not be measurable, so it cannot be silently certified. -/
def uncertifiedMap {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] (x : m ℝ) (f : ℝ → ℝ) : m ℝ := rdo
  let a ← x
  return f a

/--
error: unsolved goals
case hf
Ω : Type rdo_w
instΩ : MeasurableSpace Ω
P : Measure Ω
prob : IsProbabilityMeasure P
x : RandomM Ω P ℝ
f : ℝ → ℝ
⊢ Measurable fun c ↦ f c.2
-/
#guard_msgs in
attribute [rdo_program] uncertifiedMap

/-- error: Unknown constant `Test.Program.uncertifiedMap.program` -/
#guard_msgs in
#check Test.Program.uncertifiedMap.program

/-- The recording interpretation needs an independent output-universe parameter. -/
def fixedUniverse {m : (α : Type) → [MeasurableSpace α] → Type}
    [MeasurableSpaceMonad m] (x : m ℝ) : m ℝ := x

/-- error: rdo_program: the monad's output universe must be a universe parameter -/
#guard_msgs in
attribute [rdo_program] fixedUniverse

end Test.Program
