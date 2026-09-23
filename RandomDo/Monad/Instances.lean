/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Monad.MeasurableSpace
public import Mathlib.Probability.ProductMeasure

/-!
# Instances for `MeasurableSpaceMonad`

`Measure` gives distribution semantics, and `PseudoRandomM` gives executable pseudorandom sampling.
`RandomM Ω P α` pairs a sampler with a proof that its returned value is independent of the remaining
source state, whose distribution is still `P`.

For a probability source `P`, `RandomM` supports `pure`, measurable `map`, and `bindOfMeasurable`
for jointly measurable sampler families. Its `MeasurableSpaceMonad` instance checks this condition
inside `bind`. The `LawfulMeasurableSpaceMonad` instance additionally assumes
`RandomM.MeasurableEvalDomain Ω P`. Countable sources with measurable singletons satisfy this
assumption.

-/

@[expose] public section

universe u v w

/-- A (core) monad automatically defines a (not necessarily lawful) measurable space monad by
forgetting the measurable space argument. -/
def Monad.toMeasurableSpaceMonad (m : Type u → Type v) (α : Type u) [_mα : MeasurableSpace α] :
    Type v := m α

instance {m : Type u → Type v} [Monad m] :
    MeasurableSpaceMonad (Monad.toMeasurableSpaceMonad m) where
  mPure := pure
  mBind := bind

/-- A measurable space monad for pseudo random number generation. -/
abbrev PseudoRandomM := Monad.toMeasurableSpaceMonad Rand

open MeasureTheory

open MeasurableSpacePure MeasurableSpaceBind MeasurableSpaceFunctor MeasurableSpaceMonad

@[simps]
noncomputable instance : MeasurableSpaceMonad Measure where
  mPure := Measure.dirac
  mBind := Measure.bind

instance : LawfulMeasurableSpaceMonad Measure where
  mMap_const := by simp [mMapConst, mMap]
  id_mMap μ := by simp [mMap]
  measurable_mPure := by unfold mPure; fun_prop
  measurable_mBind := by unfold mBind; fun_prop
  mBind_mPure_comp _ _ := by rfl
  mPure_mBind x _ hf := Measure.dirac_bind hf x
  mBind_assoc _ _ _ hf hg := Measure.bind_bind hf.aemeasurable hg.aemeasurable

section RandomM

open Function

/-- A monad for random variables. -/
structure RandomM (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω)
    (α : Type u) [MeasurableSpace α] where
  /-- Return a value together with the remaining source state. -/
  sample : Ω → α × Ω
  /-- The remaining state has law `P` and is independent of the returned value. -/
  measurePreserving : MeasurePreserving sample P ((Measure.map (Prod.fst ∘ sample) P).prod P)

namespace RandomM

variable {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω}
  {α β γ : Type u} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

@[ext]
theorem ext {x y : RandomM Ω P α} (h : ∀ ω, x.sample ω = y.sample ω) : x = y := by
  cases x
  cases y
  congr
  exact funext h

theorem sample_injective : Injective (sample : RandomM Ω P α → Ω → α × Ω) :=
  fun _ _ h ↦ ext fun ω ↦ congrFun h ω

/-- The distribution of the value returned by a sampler. -/
noncomputable def law (x : RandomM Ω P α) : Measure α :=
  P.map (Prod.fst ∘ x.sample)

@[fun_prop]
theorem measurable_sample (x : RandomM Ω P α) : Measurable x.sample :=
  x.measurePreserving.measurable

@[fun_prop]
theorem measurable_fst_sample (x : RandomM Ω P α) : Measurable (Prod.fst ∘ x.sample) :=
  measurable_fst.comp x.measurable_sample

@[fun_prop]
theorem measurable_snd_sample (x : RandomM Ω P α) : Measurable (Prod.snd ∘ x.sample) :=
  measurable_snd.comp x.measurable_sample

/-- A sampler family indexed by a countable space with measurable singletons is jointly
measurable, even when the source of randomness is uncountable. -/
@[fun_prop]
theorem measurable_sample_uncurry_of_countable {δ : Type*} [MeasurableSpace δ]
    [Countable δ] [MeasurableSingletonClass δ] (f : δ → RandomM Ω P α) :
    Measurable (fun p : δ × Ω ↦ (f p.1).sample p.2) :=
  measurable_from_prod_countable_right fun a ↦ (f a).measurable_sample

@[simp]
theorem map_sample (x : RandomM Ω P α) : P.map x.sample = x.law.prod P :=
  x.measurePreserving.map_eq

theorem measurePreserving_fst (x : RandomM Ω P α) :
    MeasurePreserving (Prod.fst ∘ x.sample) P x.law :=
  ⟨x.measurable_fst_sample, rfl⟩

/-- The measurable structure induced by evaluating samplers at each fixed source state. -/
instance : MeasurableSpace (RandomM Ω P α) :=
  MeasurableSpace.comap sample inferInstance

theorem measurable_iff {δ : Type*} [MeasurableSpace δ] {f : δ → RandomM Ω P α} :
    Measurable f ↔ ∀ ω, Measurable fun d ↦ (f d).sample ω := by
  change Measurable[_, MeasurableSpace.comap sample inferInstance] f ↔ _
  rw [measurable_comap_iff, measurable_pi_iff]
  rfl

@[fun_prop]
theorem measurable_sample_apply (ω : Ω) :
    Measurable (fun x : RandomM Ω P α ↦ x.sample ω) :=
  measurable_iff.1 measurable_id ω

/-- Evaluation of a sampler at a varying source state is jointly measurable. -/
class MeasurableEval (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω)
    (α : Type u) [MeasurableSpace α] : Prop where
  /-- Evaluating a varying sampler at a varying source state is measurable. -/
  measurable_eval : Measurable (fun p : RandomM Ω P α × Ω ↦ p.1.sample p.2)

/-- A source admits jointly measurable evaluation for every result space in universe `u`.

This is an additional assumption on the source, not a consequence of the measurability of each
sampler. In particular, the pointwise measurable structure does not supply it for arbitrary
uncountable sources. -/
class MeasurableEvalDomain (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω) : Prop where
  /-- Joint measurability of evaluation for each result space. -/
  hasMeasurableEval (α : Type u) [MeasurableSpace α] : MeasurableEval Ω P α

instance [h : MeasurableEvalDomain.{u, w} Ω P] : MeasurableEval Ω P α :=
  h.hasMeasurableEval α

instance [Countable Ω] [MeasurableSingletonClass Ω] : MeasurableEvalDomain Ω P where
  hasMeasurableEval _ _ :=
    ⟨measurable_from_prod_countable_left fun ω ↦ measurable_sample_apply ω⟩

attribute [fun_prop] MeasurableEval.measurable_eval

@[fun_prop]
theorem measurable_sample_uncurry [MeasurableEval Ω P α]
    {δ : Type*} [MeasurableSpace δ] {f : δ → RandomM Ω P α} (hf : Measurable f) :
    Measurable (fun p : δ × Ω ↦ (f p.1).sample p.2) :=
  MeasurableEval.measurable_eval.comp (hf.prodMap measurable_id)

theorem measurable_iff_uncurry [MeasurableEval Ω P α]
    {δ : Type*} [MeasurableSpace δ] {f : δ → RandomM Ω P α} :
    Measurable f ↔ Measurable (fun p : δ × Ω ↦ (f p.1).sample p.2) :=
  ⟨measurable_sample_uncurry, fun hf ↦ measurable_iff.2 fun _ ↦
    hf.comp measurable_prodMk_right⟩

variable [IsProbabilityMeasure P]

instance (x : RandomM Ω P α) : IsProbabilityMeasure x.law :=
  Measure.isProbabilityMeasure_map x.measurable_fst_sample.aemeasurable

theorem measurePreserving_snd (x : RandomM Ω P α) :
    MeasurePreserving (Prod.snd ∘ x.sample) P P :=
  (MeasureTheory.measurePreserving_snd (μ := x.law) (ν := P)).comp x.measurePreserving

/-- Return a value without consuming any of the source of randomness. -/
def pure (a : α) : RandomM Ω P α where
  sample ω := (a, ω)
  measurePreserving := by
    refine ⟨measurable_const.prodMk measurable_id, ?_⟩
    simp [Function.comp_def, Measure.dirac_prod]

@[simp]
theorem sample_pure (a : α) (ω : Ω) : (pure (P := P) a).sample ω = (a, ω) := rfl

@[simp]
theorem law_pure (a : α) : (pure (P := P) a).law = Measure.dirac a := by
  simp [law, pure, Function.comp_def]

@[fun_prop]
theorem measurable_pure : Measurable (pure : α → RandomM Ω P α) :=
  measurable_iff.2 fun _ ↦ measurable_id.prodMk measurable_const

section Map

variable {β : Type v} {γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]

/-- Apply a measurable function to the returned value, retaining the remaining source state. -/
def map (f : α → β) (hf : Measurable f) (x : RandomM Ω P α) : RandomM Ω P β where
  sample := Prod.map f id ∘ x.sample
  measurePreserving := by
    have h := ((hf.measurePreserving x.law).prod (MeasurePreserving.id P)).comp
      x.measurePreserving
    convert h using 1
    rw [law, Measure.map_map hf x.measurable_fst_sample]
    rfl

@[simp]
theorem sample_map (f : α → β) (hf : Measurable f) (x : RandomM Ω P α) (ω : Ω) :
    (map f hf x).sample ω = (f (x.sample ω).1, (x.sample ω).2) := rfl

@[simp]
theorem law_map (f : α → β) (hf : Measurable f) (x : RandomM Ω P α) :
    (map f hf x).law = x.law.map f := by
  rw [law, law, Measure.map_map hf x.measurable_fst_sample]
  rfl

@[fun_prop]
theorem measurable_map (f : α → β) (hf : Measurable f) :
    Measurable (map f hf : RandomM Ω P α → RandomM Ω P β) := by
  apply measurable_iff.2
  intro ω
  exact (hf.comp (measurable_sample_apply ω).fst).prodMk (measurable_sample_apply ω).snd

@[simp]
theorem map_id (x : RandomM Ω P α) : map id measurable_id x = x :=
  ext fun _ ↦ rfl

theorem map_map (f : α → β) (hf : Measurable f) (g : β → γ) (hg : Measurable g)
    (x : RandomM Ω P α) : map g hg (map f hf x) = map (g ∘ f) (hg.comp hf) x :=
  ext fun _ ↦ rfl

@[simp]
theorem map_pure (f : α → β) (hf : Measurable f) (a : α) :
    map f hf (pure (P := P) a) = pure (f a) :=
  ext fun _ ↦ rfl

end Map

theorem measurable_law_of_uncurry {δ : Type*} [MeasurableSpace δ]
    {f : δ → RandomM Ω P α}
    (hf : Measurable (fun p : δ × Ω ↦ (f p.1).sample p.2)) :
    Measurable (fun d ↦ (f d).law) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [law, Measure.map_apply (measurable_fst_sample _) hs]
  exact measurable_measure_prodMk_left (hf.fst hs)

@[fun_prop]
theorem measurable_law [MeasurableEval Ω P α] :
    Measurable (law : RandomM Ω P α → Measure α) :=
  measurable_law_of_uncurry MeasurableEval.measurable_eval

private theorem map_bind_sample_prod (x : RandomM Ω P α) (f : α → RandomM Ω P β)
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2))
    {s : Set β} {t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P.map (fun ω ↦ (f (x.sample ω).1).sample (x.sample ω).2) (s ×ˢ t) =
      (∫⁻ a, (f a).law s ∂x.law) * P t := by
  change P.map ((fun p : α × Ω ↦ (f p.1).sample p.2) ∘ x.sample) (s ×ˢ t) = _
  rw [← Measure.map_map hf x.measurable_sample, x.map_sample,
    Measure.map_apply hf (hs.prod ht), Measure.prod_apply (hf (hs.prod ht))]
  have h (a : α) :
      P (Prod.mk a ⁻¹' ((fun p : α × Ω ↦ (f p.1).sample p.2) ⁻¹' (s ×ˢ t))) =
        (f a).law s * P t := by
    change P ((f a).sample ⁻¹' (s ×ˢ t)) = _
    rw [← Measure.map_apply (f a).measurable_sample (hs.prod ht), (f a).map_sample,
      Measure.prod_prod]
  simp_rw [h]
  exact lintegral_mul_const _ ((Measure.measurable_coe hs).comp
    (measurable_law_of_uncurry hf))

private theorem map_fst_bind_sample (x : RandomM Ω P α) (f : α → RandomM Ω P β)
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2))
    {s : Set β} (hs : MeasurableSet s) :
    P.map (fun ω ↦ ((f (x.sample ω).1).sample (x.sample ω).2).1) s =
      ∫⁻ a, (f a).law s ∂x.law := by
  change P.map (Prod.fst ∘ ((fun p : α × Ω ↦ (f p.1).sample p.2) ∘ x.sample)) s = _
  rw [← Measure.map_map measurable_fst (hf.comp x.measurable_sample),
    Measure.map_apply measurable_fst hs]
  simpa only [Function.comp_def, Set.prod_univ, measure_univ, mul_one] using
    map_bind_sample_prod x f hf hs MeasurableSet.univ

/-- Sequence samplers whose sampling functions are jointly measurable in the value and state.
This construction does not require a `MeasurableEvalDomain` instance. -/
def bindOfMeasurable (x : RandomM Ω P α) (f : α → RandomM Ω P β)
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2)) : RandomM Ω P β where
  sample ω := (f (x.sample ω).1).sample (x.sample ω).2
  measurePreserving := by
    refine ⟨hf.comp x.measurable_sample, ?_⟩
    apply Eq.symm
    apply Measure.prod_eq
    intro s t hs ht
    rw [map_bind_sample_prod x f hf hs ht]
    exact congrArg (· * P t) (map_fst_bind_sample x f hf hs).symm

@[simp]
theorem sample_bindOfMeasurable (x : RandomM Ω P α) (f : α → RandomM Ω P β)
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2)) (ω : Ω) :
    (bindOfMeasurable x f hf).sample ω = (f (x.sample ω).1).sample (x.sample ω).2 := rfl

@[simp]
theorem law_bindOfMeasurable (x : RandomM Ω P α) (f : α → RandomM Ω P β)
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2)) :
    (bindOfMeasurable x f hf).law = x.law.bind (fun a ↦ (f a).law) := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_law_of_uncurry hf).aemeasurable]
  exact map_fst_bind_sample x f hf hs

@[fun_prop]
theorem measurable_bindOfMeasurable (f : α → RandomM Ω P β)
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2)) :
    Measurable (fun x ↦ bindOfMeasurable x f hf) :=
  measurable_iff.2 fun ω ↦ hf.comp (measurable_sample_apply ω)

/-- Sequence samplers when the continuation's sampling function is jointly measurable.
Otherwise select one of its samplers arbitrarily. The joint-measurability condition is checked
inside this definition, so constructing a bind does not require a `MeasurableEval` instance. -/
noncomputable def bind (x : RandomM Ω P α) (f : α → RandomM Ω P β) : RandomM Ω P β := by
  classical
  exact if hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2) then bindOfMeasurable x f hf
    else f (x.sample (Classical.choice (nonempty_of_isProbabilityMeasure P))).1

theorem bind_eq_bindOfMeasurable (x : RandomM Ω P α) (f : α → RandomM Ω P β)
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2)) :
    bind x f = bindOfMeasurable x f hf := by
  classical
  simp only [bind, dite_eq_left hf]

/-- The sampling equation needs only joint measurability of this particular continuation. -/
theorem sample_bind_of_measurable (x : RandomM Ω P α) (f : α → RandomM Ω P β)
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2)) (ω : Ω) :
    (bind x f).sample ω = (f (x.sample ω).1).sample (x.sample ω).2 := by
  rw [bind_eq_bindOfMeasurable x f hf, sample_bindOfMeasurable]

theorem law_bind_of_measurable (x : RandomM Ω P α) (f : α → RandomM Ω P β)
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2)) :
    (bind x f).law = x.law.bind (fun a ↦ (f a).law) := by
  rw [bind_eq_bindOfMeasurable x f hf, law_bindOfMeasurable]

@[simp]
theorem sample_bind_of_countable [Countable α] [MeasurableSingletonClass α]
    (x : RandomM Ω P α) (f : α → RandomM Ω P β) (ω : Ω) :
    (bind x f).sample ω = (f (x.sample ω).1).sample (x.sample ω).2 :=
  sample_bind_of_measurable x f (measurable_sample_uncurry_of_countable f) ω

@[simp]
theorem law_bind_of_countable [Countable α] [MeasurableSingletonClass α]
    (x : RandomM Ω P α) (f : α → RandomM Ω P β) :
    (bind x f).law = x.law.bind (fun a ↦ (f a).law) :=
  law_bind_of_measurable x f (measurable_sample_uncurry_of_countable f)

@[fun_prop]
theorem measurable_bind_of_uncurry {f : α → RandomM Ω P β}
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2)) :
    Measurable (fun x ↦ bind x f) := by
  simpa only [bind_eq_bindOfMeasurable _ f hf] using measurable_bindOfMeasurable f hf

@[simp]
theorem sample_bind [MeasurableEval Ω P β] (x : RandomM Ω P α)
    (f : α → RandomM Ω P β) (hf : Measurable f) (ω : Ω) :
    (bind x f).sample ω = (f (x.sample ω).1).sample (x.sample ω).2 :=
  sample_bind_of_measurable x f (measurable_sample_uncurry hf) ω

@[simp]
theorem law_bind [MeasurableEval Ω P β] (x : RandomM Ω P α)
    (f : α → RandomM Ω P β) (hf : Measurable f) :
    (bind x f).law = x.law.bind (fun a ↦ (f a).law) :=
  law_bind_of_measurable x f (measurable_sample_uncurry hf)

@[fun_prop]
theorem measurable_bind [MeasurableEval Ω P β] {f : α → RandomM Ω P β}
    (hf : Measurable f) : Measurable (fun x ↦ bind x f) :=
  measurable_bind_of_uncurry (measurable_sample_uncurry hf)

/-- Bind a measurable family of samplers to a jointly measurable family of continuations. -/
@[fun_prop]
theorem measurable_bind₂ [MeasurableEval Ω P β] {δ : Type*} [MeasurableSpace δ]
    {x : δ → RandomM Ω P α} {f : δ → α → RandomM Ω P β}
    (hx : Measurable x) (hf : Measurable (uncurry f)) :
    Measurable (fun d ↦ bind (x d) (f d)) := by
  apply measurable_iff.2
  intro ω
  have hs := (measurable_sample_apply ω).comp hx
  have h := MeasurableEval.measurable_eval.comp
    ((hf.comp (measurable_id.prodMk hs.fst)).prodMk hs.snd)
  convert h using 1
  funext d
  exact sample_bind (x d) (f d) hf.of_uncurry_left ω

@[simp]
theorem pure_bind (a : α) (f : α → RandomM Ω P β) : bind (pure a) f = f a := by
  classical
  by_cases hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2)
  · apply ext
    intro ω
    simp only [sample_bind_of_measurable _ _ hf, sample_pure]
  · simp only [bind, dite_eq_right hf, sample_pure]

@[simp]
theorem bind_pure (x : RandomM Ω P α) : bind x pure = x := by
  apply ext
  intro ω
  exact sample_bind_of_measurable x pure measurable_id ω

theorem bind_assoc_of_measurable (x : RandomM Ω P α)
    {f : α → RandomM Ω P β} {g : β → RandomM Ω P γ}
    (hf : Measurable (fun p : α × Ω ↦ (f p.1).sample p.2))
    (hg : Measurable (fun p : β × Ω ↦ (g p.1).sample p.2)) :
    bind (bind x f) g = bind x (fun a ↦ bind (f a) g) := by
  have hfg : Measurable (fun p : α × Ω ↦ (bind (f p.1) g).sample p.2) := by
    simp_rw [sample_bind_of_measurable _ _ hg]
    exact hg.comp hf
  apply ext
  intro ω
  simp only [sample_bind_of_measurable _ _ hf, sample_bind_of_measurable _ _ hg,
    sample_bind_of_measurable x (fun a ↦ bind (f a) g) hfg]

theorem bind_assoc [MeasurableEval Ω P β] [MeasurableEval Ω P γ] (x : RandomM Ω P α)
    {f : α → RandomM Ω P β} {g : β → RandomM Ω P γ} (hf : Measurable f) (hg : Measurable g) :
    bind (bind x f) g = bind x (fun a ↦ bind (f a) g) :=
  bind_assoc_of_measurable x (measurable_sample_uncurry hf) (measurable_sample_uncurry hg)

theorem bind_pure_comp (x : RandomM Ω P α)
    {f : α → β} (hf : Measurable f) : bind x (fun a ↦ pure (f a)) = map f hf x := by
  have hpf : Measurable (fun p : α × Ω ↦ (pure (P := P) (f p.1)).sample p.2) :=
    hf.prodMap measurable_id
  apply ext
  intro ω
  simp only [sample_bind_of_measurable x (fun a ↦ pure (f a)) hpf, sample_pure, sample_map]

noncomputable instance :
    MeasurableSpaceMonad (RandomM Ω P : (α : Type u) → [MeasurableSpace α] → Type (max u w)) where
  mPure := pure
  mBind := bind

instance [MeasurableEvalDomain.{u, w} Ω P] :
    LawfulMeasurableSpaceMonad
      (RandomM Ω P : (α : Type u) → [MeasurableSpace α] → Type (max u w)) where
  mMap_const := rfl
  id_mMap := bind_pure
  measurable_mPure {α} {_} := @measurable_pure Ω _ P α _ _
  measurable_mBind := measurable_bind
  mBind_mPure_comp _ _ := rfl
  mPure_mBind a f _ := pure_bind a f
  mBind_assoc x _ _ hf hg := bind_assoc x hf hg

@[simp]
theorem sample_mPure (a : α) (ω : Ω) : (mPure a : RandomM Ω P α).sample ω = (a, ω) := rfl

@[simp]
theorem law_mPure (a : α) : (mPure a : RandomM Ω P α).law = Measure.dirac a := law_pure a

@[fun_prop]
theorem measurable_mBind₂ [MeasurableEval Ω P β] {δ : Type*} [MeasurableSpace δ]
    {x : δ → RandomM Ω P α} {f : δ → α → RandomM Ω P β}
    (hx : Measurable x) (hf : Measurable (uncurry f)) :
    Measurable (fun d ↦ x d >>=ₘ f d) := measurable_bind₂ hx hf

@[simp]
theorem sample_mBind [MeasurableEval Ω P β] (x : RandomM Ω P α)
    (f : α → RandomM Ω P β) (hf : Measurable f)
    (ω : Ω) : (x >>=ₘ f).sample ω = (f (x.sample ω).1).sample (x.sample ω).2 :=
  sample_bind x f hf ω

@[simp]
theorem law_mBind [MeasurableEval Ω P β] (x : RandomM Ω P α)
    (f : α → RandomM Ω P β) (hf : Measurable f) :
    (x >>=ₘ f).law = x.law.bind (fun a ↦ (f a).law) := law_bind x f hf

@[simp]
theorem sample_mBind_of_countable [Countable α] [MeasurableSingletonClass α]
    (x : RandomM Ω P α) (f : α → RandomM Ω P β) (ω : Ω) :
    (x >>=ₘ f).sample ω = (f (x.sample ω).1).sample (x.sample ω).2 :=
  sample_bind_of_countable x f ω

@[simp]
theorem law_mBind_of_countable [Countable α] [MeasurableSingletonClass α]
    (x : RandomM Ω P α) (f : α → RandomM Ω P β) :
    (x >>=ₘ f).law = x.law.bind (fun a ↦ (f a).law) := law_bind_of_countable x f

theorem mMap_eq_map (f : α → β) (hf : Measurable f) (x : RandomM Ω P α) :
    f <$>ₘ x = map f hf x := bind_pure_comp x hf

@[simp]
theorem sample_mMap (f : α → β) (hf : Measurable f) (x : RandomM Ω P α) (ω : Ω) :
    (f <$>ₘ x).sample ω = (f (x.sample ω).1, (x.sample ω).2) := by
  rw [mMap_eq_map f hf x, sample_map]

@[simp]
theorem law_mMap (f : α → β) (hf : Measurable f) (x : RandomM Ω P α) :
    (f <$>ₘ x).law = x.law.map f := by
  rw [mMap_eq_map f hf x, law_map]

end RandomM

/-- Samplers driven by a sequence of independent source values with common law `P`.
For a probability measure `P`, the monad operations are available without a domain assumption.
The lawful instance still requires measurable evaluation on the full stream space `ℕ → Ω`. -/
abbrev SampleM (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω)
    (α : Type u) [MeasurableSpace α] : Type (max u w) :=
  RandomM (ℕ → Ω) (Measure.infinitePi fun _ : ℕ ↦ P) α

end RandomM
