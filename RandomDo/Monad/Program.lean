/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Monad.Sample

/-!
# Certified representations of random programs

`RDo.Program` records returns, primitive samplers, and binds. A polymorphic `rdo` definition
can be interpreted in this monad without changing its source. `RDo.Program.Valid` certifies
families of programs compositionally, including the joint measurability needed by bind.
Its soundness theorem relates the actual `RandomM` and `Measure` interpretations.
-/

@[expose] public section

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

namespace RDo

universe u w

/-- A program tree whose primitive operations are samplers on a fixed probability source. -/
inductive Program (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω) :
    (α : Type u) → [MeasurableSpace α] → Type (max (u + 1) w)
  /-- Return a value. -/
  | pure {α : Type u} [MeasurableSpace α] (a : α) : Program Ω P α
  /-- Perform a primitive sampler. -/
  | sample {α : Type u} [MeasurableSpace α] (x : RandomM Ω P α) : Program Ω P α
  /-- Sequence two programs. -/
  | bind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      (x : Program Ω P α) (f : α → Program Ω P β) : Program Ω P β

namespace Program

variable {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω}

instance : MeasurableSpaceMonad (Program Ω P :
    (α : Type u) → [MeasurableSpace α] → Type (max (u + 1) w)) where
  mPure := pure
  mBind := bind

variable [IsProbabilityMeasure P]

/-- Interpret a program using the original sampler operations. -/
noncomputable def sampleSemantics {α : Type u} [MeasurableSpace α] :
    Program Ω P α → RandomM Ω P α
  | .pure a => mPure a
  | .sample x => x
  | @Program.bind _ _ _ _ _ _ _ x f =>
    RandomM.bind (sampleSemantics x) fun a ↦ sampleSemantics (f a)

/-- Interpret a program using the laws of its primitives and the measure monad. -/
noncomputable def measureSemantics {α : Type u} [MeasurableSpace α] :
    Program Ω P α → Measure α
  | .pure a => mPure a
  | .sample x => x.law
  | @Program.bind _ _ _ _ _ _ _ x f =>
    (measureSemantics x).bind fun a ↦ measureSemantics (f a)

/-- A compositional certificate for a family of program trees. The input parameter includes
values returned by previous draws, so measurability is checked jointly through nested binds. -/
inductive Valid : {γ α : Type u} → [MeasurableSpace γ] → [MeasurableSpace α] →
    (γ → Program Ω P α) → Prop
  /-- A measurable return expression. -/
  | pure {γ α : Type u} [MeasurableSpace γ] [MeasurableSpace α]
      (f : γ → α) (hf : Measurable f) : Valid (fun c ↦ .pure (f c))
  /-- A jointly measurable family of primitive samplers. -/
  | sample {γ α : Type u} [MeasurableSpace γ] [MeasurableSpace α]
      (f : γ → RandomM Ω P α)
      (hf : Measurable (fun p : γ × Ω ↦ (f p.1).sample p.2)) :
      Valid (fun c ↦ .sample (f c))
  /-- Bind certificates compose, carrying the previous input along with the returned value. -/
  | bind {γ α β : Type u} [MeasurableSpace γ] [MeasurableSpace α] [MeasurableSpace β]
      (x : γ → Program Ω P α) (f : γ → α → Program Ω P β)
      (hx : Valid x) (hf : Valid (Function.uncurry f)) :
      Valid (fun c ↦ .bind (x c) (f c))
  /-- Reparameterize a certified family by a measurable function. -/
  | comp {γ δ α : Type u} [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace α]
      (p : γ → Program Ω P α) (g : δ → γ) (hp : Valid p) (hg : Measurable g) :
      Valid (fun c ↦ p (g c))
  /-- Branch on a measurable predicate. -/
  | ite {γ α : Type u} [MeasurableSpace γ] [MeasurableSpace α]
      (p : γ → Prop) [DecidablePred p] (x y : γ → Program Ω P α)
      (hp : Measurable p) (hx : Valid x) (hy : Valid y) :
      Valid (fun c ↦ if p c then x c else y c)

variable {γ α : Type u} [MeasurableSpace γ] [MeasurableSpace α]

/-- Soundness of the certificate: sampling is jointly measurable, and its pushforward agrees
with the measure interpretation. No global measurable-evaluation assumption is needed. -/
theorem Valid.sound {p : γ → Program Ω P α} (hp : Valid p) :
    Measurable (fun z : γ × Ω ↦ (sampleSemantics (p z.1)).sample z.2) ∧
      ∀ c, (sampleSemantics (p c)).law = measureSemantics (p c) := by
  classical
  induction hp with
  | pure f hf =>
    exact ⟨hf.prodMap measurable_id, fun _ ↦ RandomM.law_mPure _⟩
  | sample f hf => exact ⟨hf, fun _ ↦ rfl⟩
  | @bind γ α β _ _ _ x f hx hf ihx ihf =>
    have hfc (c : γ) : Measurable (fun z : α × Ω ↦ (sampleSemantics (f c z.1)).sample z.2) :=
      ihf.1.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    constructor
    · have h := ihf.1.comp ((measurable_fst.prodMk ihx.1.fst).prodMk ihx.1.snd)
      convert h using 1
      funext z
      exact RandomM.sample_bind_of_measurable _ _ (hfc z.1) z.2
    · intro c
      change (RandomM.bind _ _).law = (measureSemantics (x c)).bind _
      rw [RandomM.law_bind_of_measurable _ _ (hfc c), ihx.2 c]
      exact congrArg (Measure.bind _) (funext fun a ↦ ihf.2 (c, a))
  | comp p g hp hg ih =>
    exact ⟨ih.1.comp (hg.prodMap measurable_id), fun c ↦ ih.2 (g c)⟩
  | ite p x y hp hx hy ihx ihy =>
    constructor
    · have h : Measurable (fun z : _ × Ω ↦
          if p z.1 then (sampleSemantics (x z.1)).sample z.2
          else (sampleSemantics (y z.1)).sample z.2) :=
        ihx.1.ite ((hp.comp measurable_fst).setOf) ihy.1
      convert h using 1
      funext z
      by_cases h : p z.1 <;> simp only [h, ite_true, ite_false]
    · intro c
      by_cases h : p c
      · simpa only [h, ite_true] using ihx.2 c
      · simpa only [h, ite_false] using ihy.2 c

omit [IsProbabilityMeasure P] in
/-- A closed certificate can be used in a larger input context. -/
theorem Valid.const {p : Program Ω P α} (hp : Valid (fun _ : PUnit ↦ p)) :
    Valid (fun _ : γ ↦ p) :=
  .comp (fun _ : PUnit ↦ p) (fun _ ↦ PUnit.unit) hp measurable_const

/-- A program together with its compositional certificate. -/
structure Certified (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : Type u) [MeasurableSpace α] where
  /-- The recorded program. -/
  program : Program Ω P α
  /-- Joint measurability is certified at every bind. -/
  valid : Valid (fun _ : PUnit ↦ program)

/-- The universal sampler-to-measure theorem for certified program representations. -/
theorem Certified.law (p : Certified Ω P α) :
    (sampleSemantics p.program).law = measureSemantics p.program :=
  p.valid.sound.2 PUnit.unit

/-- Transport the universal theorem through bridges to existing program definitions. -/
theorem Certified.law_of_bridge (p : Certified Ω P α) (x : RandomM Ω P α) (μ : Measure α)
    (hs : sampleSemantics p.program = x) (hm : measureSemantics p.program = μ) : x.law = μ := by
  rw [← hs, ← hm]
  exact p.law

end Program

end RDo
