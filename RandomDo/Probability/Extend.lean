/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.Probability.Transfer
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public meta import Lean.Elab.Tactic.Basic

set_option linter.style.header false

/-!
# Extending a probability space by a new random variable

`extend_space μ` adds to the probability space `(Ω, P)` of the goal a random variable `Z` with law
`μ`, independent of everything defined on `Ω`. It is the tactic form of "without loss of
generality, let `Z ~ μ` be independent of the rest". Underneath, the new space is `Ω × E` with the
product measure, presented as an abstract space related to the old one by a measure-preserving map
`f`, which is all the extended goal may use. Three presentations are available.

* `extend_space μ` keeps the names: `Ω`, `P`, every random variable `X : Ω → α` and every event
  `s : Set Ω` now denote objects on the extended space, hypotheses about them are transported, and
  the goal reads as before. The old space and its objects are still there, renamed `Ω₀`, `P₀`,
  `X₀`, …, together with the map `f : Ω → Ω₀`, `hf : MeasurePreserving f P P₀` and the defining
  equations `hX_def : ∀ ω, X₀ (f ω) = X ω`. A hypothesis that cannot be transported stays about the
  old space, under its `₀` name. The context gains `Z : Ω → E`, `hZ : HasLaw Z μ P` and
  `hind`, the independence of `Z` from the transported random variables, as a tuple.
* `extend_space! μ` does the same and clears the old space, the map, and everything that
  mentions them.
* `extend_space_map μ` is the explicit form: nothing is renamed, the new space is `Ω'` with
  `P'`, `f : Ω' → Ω`, `hf`, `Z`, `hZ : HasLaw Z μ P'` and `hind : IndepFun f Z P'`, and the goal
  is restated with `fun ω ↦ X (f ω)` for `X` and `f ⁻¹' s` for `s`. Hypotheses about the old space
  stay as they are and are pulled back on demand, by `transfer hf at h` or by hand.

In every case a `transfer` goal is left when the `transfer` tactic cannot discharge it: the
obligation that the statement pulls back along any measure-preserving map, which is what makes
the replacement sound. A hypothesis the goal itself depends on, such as a measurability proof
inside a `Kernel.comap`, is generalized along with the goal.

`extend_space κ` for a Markov kernel `κ : Kernel Ω E` gives instead a draw with conditional law
`κ` given the old space, `hZ : HasCondDistrib Z f κ P'`, and no `hind`. For a draw conditional on
a random variable `X`, extend with `κ.comap X hX`: `extend_space` then states `hZ` as
`HasCondDistrib Z X κ P`.

Compare `alg_env_trace`: there the new space is not an extension of the old one, only a space with
the same trajectory law, so its `transfer` obligation is about laws and has to be proved
statement by statement. Here the projection `f` is measure preserving, which is a uniform principle.

## Main results

* `RDo.wlog_extend`, `RDo.wlog_extend_kernel`: the principles behind the tactic.
* `MeasureTheory.MeasurePreserving.map_fun_comp`, `hasLaw_fun_comp_iff`, `indepFun_fun_comp_iff`,
  `hasCondDistrib_fun_comp_iff`: pulling statements back along a measure-preserving map.
* The `@[transfer]` lemmas `MeasurePreserving.transfer_*` and the `@[transfer_forward]` lemmas
  `*.comp_measurePreserving`, `*.preimage_measurePreserving`: the same facts in the forms the
  `transfer` tactic uses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ### Pulling statements back along a measure-preserving map -/

namespace MeasureTheory.MeasurePreserving

variable {Ω Ω' 𝓧 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} {P' : Measure Ω'}
  {f : Ω' → Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨}

/-- The law of `X ∘ f` under `P'` is the law of `X` under `P`. -/
lemma map_fun_comp (hf : MeasurePreserving f P' P) (hX : AEMeasurable X P) :
    P'.map (fun ω ↦ X (f ω)) = P.map X := by
  rw [← hf.map_eq] at hX ⊢
  exact (AEMeasurable.map_map_of_aemeasurable hX hf.measurable.aemeasurable).symm

lemma hasLaw_fun_comp_iff (hf : MeasurePreserving f P' P) (hX : Measurable X) {ν : Measure 𝓧} :
    HasLaw (fun ω ↦ X (f ω)) ν P' ↔ HasLaw X ν P where
  mp h := ⟨hX.aemeasurable, by rw [← hf.map_fun_comp hX.aemeasurable]; exact h.map_eq⟩
  mpr h := h.comp hf.hasLaw

lemma indepFun_fun_comp_iff (hf : MeasurePreserving f P' P) (hX : Measurable X)
    (hY : Measurable Y) :
    IndepFun (fun ω ↦ X (f ω)) (fun ω ↦ Y (f ω)) P' ↔ IndepFun X Y P := by
  simp only [indepFun_iff_measure_inter_preimage_eq_mul]
  refine forall₄_congr fun s t hs ht ↦ ?_
  change P' (f ⁻¹' (X ⁻¹' s) ∩ f ⁻¹' (Y ⁻¹' t))
    = P' (f ⁻¹' (X ⁻¹' s)) * P' (f ⁻¹' (Y ⁻¹' t)) ↔ _
  rw [← Set.preimage_inter, hf.measure_preimage ((hX hs).inter (hY ht)).nullMeasurableSet,
    hf.measure_preimage (hX hs).nullMeasurableSet, hf.measure_preimage (hY ht).nullMeasurableSet]

lemma hasCondDistrib_fun_comp_iff (hf : MeasurePreserving f P' P) (hX : Measurable X)
    (hY : Measurable Y) {κ : Kernel 𝓧 𝓨} :
    HasCondDistrib (fun ω ↦ Y (f ω)) (fun ω ↦ X (f ω)) κ P' ↔ HasCondDistrib Y X κ P := by
  unfold HasCondDistrib
  rw [hf.map_fun_comp hX.aemeasurable]
  exact hf.hasLaw_fun_comp_iff (hX.prodMk hY)

/-! ### The `@[transfer]` lemmas: from the old space to the new one

The same facts, stated with the old space on the left and `hf` as the first explicit argument,
which is what the `transfer` tactic rewrites with. -/

@[transfer]
lemma transfer_map (hf : MeasurePreserving f P' P) (hX : AEMeasurable X P) :
    P.map X = P'.map (fun ω ↦ X (f ω)) :=
  (hf.map_fun_comp hX).symm

@[transfer]
lemma transfer_measure (hf : MeasurePreserving f P' P) {s : Set Ω} (hs : NullMeasurableSet s P) :
    P s = P' (f ⁻¹' s) :=
  (hf.measure_preimage hs).symm

@[transfer]
lemma transfer_real (hf : MeasurePreserving f P' P) {s : Set Ω} (hs : NullMeasurableSet s P) :
    P.real s = P'.real (f ⁻¹' s) := by
  simp only [measureReal_def, hf.measure_preimage hs]

@[transfer]
lemma transfer_hasLaw (hf : MeasurePreserving f P' P) (hX : Measurable X) {ν : Measure 𝓧} :
    HasLaw X ν P ↔ HasLaw (fun ω ↦ X (f ω)) ν P' :=
  (hf.hasLaw_fun_comp_iff hX).symm

@[transfer]
lemma transfer_indepFun (hf : MeasurePreserving f P' P) (hX : Measurable X) (hY : Measurable Y) :
    IndepFun X Y P ↔ IndepFun (fun ω ↦ X (f ω)) (fun ω ↦ Y (f ω)) P' :=
  (hf.indepFun_fun_comp_iff hX hY).symm

@[transfer]
lemma transfer_hasCondDistrib (hf : MeasurePreserving f P' P) (hX : Measurable X)
    (hY : Measurable Y) {κ : Kernel 𝓧 𝓨} :
    HasCondDistrib Y X κ P ↔ HasCondDistrib (fun ω ↦ Y (f ω)) (fun ω ↦ X (f ω)) κ P' :=
  (hf.hasCondDistrib_fun_comp_iff hX hY).symm

@[transfer]
lemma transfer_integral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hf : MeasurePreserving f P' P) {g : Ω → G} (hg : AEStronglyMeasurable g P) :
    ∫ ω, g ω ∂P = ∫ ω, g (f ω) ∂P' := by
  rw [← hf.map_eq] at hg ⊢
  exact integral_map hf.measurable.aemeasurable hg

@[transfer]
lemma transfer_lintegral (hf : MeasurePreserving f P' P) {g : Ω → ENNReal}
    (hg : AEMeasurable g P) :
    ∫⁻ ω, g ω ∂P = ∫⁻ ω, g (f ω) ∂P' := by
  rw [← hf.map_eq] at hg ⊢
  exact lintegral_map' hg hf.measurable.aemeasurable

@[transfer]
lemma transfer_ae (hf : MeasurePreserving f P' P) {p : Ω → Prop}
    (hp : NullMeasurableSet {ω | p ω} P) :
    (∀ᵐ ω ∂P, p ω) ↔ ∀ᵐ ω ∂P', p (f ω) := by
  rw [ae_iff, ae_iff, ← hf.measure_preimage (s := {ω | ¬ p ω}) hp.compl, Set.preimage_ofPred_eq]

@[transfer]
lemma transfer_ae_eq (hf : MeasurePreserving f P' P) {X Y : Ω → 𝓧}
    (h : NullMeasurableSet {ω | X ω = Y ω} P) :
    X =ᵐ[P] Y ↔ (fun ω ↦ X (f ω)) =ᵐ[P'] fun ω ↦ Y (f ω) :=
  hf.transfer_ae h

@[transfer]
lemma transfer_integrable {G : Type*} [NormedAddCommGroup G] (hf : MeasurePreserving f P' P)
    {g : Ω → G} (hg : AEStronglyMeasurable g P) :
    Integrable g P ↔ Integrable (fun ω ↦ g (f ω)) P' :=
  (hf.integrable_comp hg).symm

end MeasureTheory.MeasurePreserving

/-! ### Forward transport of hypotheses

A hypothesis about the old space gives one about the new space. These are the
`@[transfer_forward]` lemmas: the hypothesis first, then `hf`, then side conditions. -/

section Forward

variable {Ω Ω' 𝓧 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} {P' : Measure Ω'}
  {f : Ω' → Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨}

@[transfer_forward]
lemma Measurable.comp_measurePreserving (hX : Measurable X) (hf : MeasurePreserving f P' P) :
    Measurable fun ω ↦ X (f ω) :=
  hX.comp hf.measurable

@[transfer_forward]
lemma AEMeasurable.comp_measurePreserving (hX : AEMeasurable X P)
    (hf : MeasurePreserving f P' P) :
    AEMeasurable (fun ω ↦ X (f ω)) P' :=
  hX.comp_quasiMeasurePreserving hf.quasiMeasurePreserving

attribute [transfer_forward] MeasureTheory.AEStronglyMeasurable.comp_measurePreserving

@[transfer_forward]
lemma MeasurableSet.preimage_measurePreserving {s : Set Ω} (hs : MeasurableSet s)
    (hf : MeasurePreserving f P' P) :
    MeasurableSet (f ⁻¹' s) :=
  hf.measurable hs

@[transfer_forward]
lemma MeasureTheory.NullMeasurableSet.preimage_measurePreserving {s : Set Ω}
    (hs : NullMeasurableSet s P) (hf : MeasurePreserving f P' P) :
    NullMeasurableSet (f ⁻¹' s) P' :=
  hs.preimage hf.quasiMeasurePreserving

@[transfer_forward]
lemma ProbabilityTheory.HasLaw.comp_measurePreserving {ν : Measure 𝓧} (hX : HasLaw X ν P)
    (hf : MeasurePreserving f P' P) :
    HasLaw (fun ω ↦ X (f ω)) ν P' :=
  hX.comp hf.hasLaw

/-- A conditional law pulls back along a measure-preserving map. -/
@[transfer_forward]
lemma ProbabilityTheory.HasCondDistrib.comp_measurePreserving {κ : Kernel 𝓧 𝓨}
    (h : HasCondDistrib Y X κ P) (hf : MeasurePreserving f P' P) :
    HasCondDistrib (fun ω ↦ Y (f ω)) (fun ω ↦ X (f ω)) κ P' := by
  have hX := h.aemeasurable_fst
  unfold HasCondDistrib at h ⊢
  rw [hf.map_fun_comp hX]
  exact h.comp hf.hasLaw

@[transfer_forward]
lemma ProbabilityTheory.IndepFun.comp_measurePreserving (h : IndepFun X Y P)
    (hf : MeasurePreserving f P' P) (hX : Measurable X) (hY : Measurable Y) :
    IndepFun (fun ω ↦ X (f ω)) (fun ω ↦ Y (f ω)) P' :=
  (hf.indepFun_fun_comp_iff hX hY).2 h

@[transfer_forward]
lemma MeasureTheory.Integrable.comp_measurePreserving {G : Type*} [NormedAddCommGroup G]
    {g : Ω → G} (hg : Integrable g P) (hf : MeasurePreserving f P' P) :
    Integrable (fun ω ↦ g (f ω)) P' :=
  (hf.integrable_comp hg.aestronglyMeasurable).2 hg

end Forward

namespace RDo

/-! ### The product extension -/

section Product

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω}

/-- Under a product of probability measures, the two coordinates are independent. -/
lemma indepFun_fst_snd_prod [IsProbabilityMeasure P] (μ : Measure E) [IsProbabilityMeasure μ] :
    IndepFun (Prod.fst : Ω × E → Ω) Prod.snd (P.prod μ) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable]
  simp [Measure.map_id', measurePreserving_fst.map_eq, measurePreserving_snd.map_eq]

/-- The first coordinate of `P ⊗ₘ κ` has law `P`. -/
lemma measurePreserving_fst_compProd [SFinite P] (κ : Kernel Ω E) [IsMarkovKernel κ] :
    MeasurePreserving Prod.fst (P ⊗ₘ κ) P :=
  ⟨measurable_fst, Measure.fst_compProd P κ⟩

/-- Under `P ⊗ₘ κ`, the second coordinate has conditional law `κ` given the first. -/
lemma hasCondDistrib_snd_fst_compProd [SFinite P] (κ : Kernel Ω E) [IsMarkovKernel κ] :
    HasCondDistrib Prod.snd Prod.fst κ (P ⊗ₘ κ) := by
  change HasLaw _ ((P ⊗ₘ κ).fst ⊗ₘ κ) _
  rw [Measure.fst_compProd]
  exact HasLaw.id

end Product

universe u v

/-- **The principle behind `extend_space κ`.** To prove a statement `motive` about the probability
space `(Ω, P)`, it is enough to prove it on a space `(Ω', P')` that projects onto `Ω` by a
measure-preserving map `f` and carries a draw `Z` with conditional law `κ` given `f`, *provided*
the statement pulls back along measure-preserving maps, which is what `transfer` asks for.

The space `Ω'` is the product `Ω × E` with the measure `P ⊗ₘ κ`, but `extended` may not use that:
all it knows of `Ω'` is `f`, `Z` and their laws. The universe of `E` may not exceed that of `Ω`,
since the product has to live in the universe of `Ω`. -/
theorem wlog_extend_kernel {Ω : Type (max u v)} [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] {P : Measure Ω} [hP : IsProbabilityMeasure P]
    {motive : (Ω' : Type (max u v)) → [MeasurableSpace Ω'] → (P' : Measure Ω') →
      [IsProbabilityMeasure P'] → (Ω' → Ω) → Prop}
    (κ : Kernel Ω E) [IsMarkovKernel κ]
    (extended : ∀ (Ω' : Type (max u v)) [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (f : Ω' → Ω), MeasurePreserving f P' P → ∀ (Z : Ω' → E),
      HasCondDistrib Z f κ P' → motive Ω' P' f)
    (transfer : ∀ (Ω' : Type (max u v)) [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (f : Ω' → Ω), MeasurePreserving f P' P →
      motive Ω' P' f → motive Ω P id) :
    motive Ω P id :=
  transfer (Ω × E) (P ⊗ₘ κ) Prod.fst (measurePreserving_fst_compProd κ)
    (extended (Ω × E) (P ⊗ₘ κ) Prod.fst (measurePreserving_fst_compProd κ) Prod.snd
      (hasCondDistrib_snd_fst_compProd κ))

/-- **The principle behind `extend_space μ`.** To prove a statement `motive` about the probability
space `(Ω, P)`, it is enough to prove it on a space `(Ω', P')` that projects onto `Ω` by a
measure-preserving map `f` and carries a draw `Z` with law `μ`, independent of `f`, *provided*
the statement pulls back along measure-preserving maps, which is what `transfer` asks for.

The space `Ω'` is the product `Ω × E` with the product measure, but `extended` may not use that:
all it knows of `Ω'` is `f`, `Z` and their laws. The universe of `E` may not exceed that of `Ω`,
since the product has to live in the universe of `Ω`. -/
theorem wlog_extend {Ω : Type (max u v)} [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] {P : Measure Ω} [hP : IsProbabilityMeasure P]
    {motive : (Ω' : Type (max u v)) → [MeasurableSpace Ω'] → (P' : Measure Ω') →
      [IsProbabilityMeasure P'] → (Ω' → Ω) → Prop}
    (μ : Measure E) [IsProbabilityMeasure μ]
    (extended : ∀ (Ω' : Type (max u v)) [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (f : Ω' → Ω), MeasurePreserving f P' P → ∀ (Z : Ω' → E),
      HasLaw Z μ P' → IndepFun f Z P' → motive Ω' P' f)
    (transfer : ∀ (Ω' : Type (max u v)) [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (f : Ω' → Ω), MeasurePreserving f P' P →
      motive Ω' P' f → motive Ω P id) :
    motive Ω P id :=
  transfer (Ω × E) (P.prod μ) Prod.fst measurePreserving_fst
    (extended (Ω × E) (P.prod μ) Prod.fst measurePreserving_fst Prod.snd
      measurePreserving_snd.hasLaw (indepFun_fst_snd_prod μ))

end RDo

end

end

public meta section

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic
open MeasureTheory ProbabilityTheory

namespace RDo.Tactic

/-! ### The space and what depends on it -/

/-- The probability space being extended, as local hypotheses: the space, its σ-algebra, the
measure and, when it is a local hypothesis, its `IsProbabilityMeasure` instance. They have to be
local hypotheses, since the goal is abstracted over them. -/
structure ProbSpace where
  /-- The space. -/
  Ω : FVarId
  /-- Its σ-algebra. -/
  mΩ : FVarId
  /-- The measure. -/
  P : FVarId
  /-- The `IsProbabilityMeasure` hypothesis, when it is a local one. -/
  hP : Option FVarId

/-- The `IsProbabilityMeasure` hypothesis for `P`, if there is a local one. -/
def findIsProbabilityMeasure? (P : Expr) : MetaM (Option FVarId) := do
  let target ← mkAppM ``IsProbabilityMeasure #[P]
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      if (← instantiateMVars d.type) == target then return some d.fvarId
  return none

/-- The space of a measure `P`, read off its type `Measure Ω`. -/
def ProbSpace.ofMeasure (P : Expr) : MetaM ProbSpace := do
  let .fvar Pf := P
    | throwError "extend_space: the measure must be a local hypothesis, but {P} is not"
  let ty ← whnfR (← inferType P)
  unless ty.isAppOfArity ``Measure 2 do throwError "extend_space: {P} is not a measure"
  let Ω := ty.appFn!.appArg!
  let mΩ := ty.appArg!
  let .fvar Ωf := Ω
    | throwError "extend_space: the space must be a local hypothesis, but {Ω} is not"
  let .fvar mf := mΩ
    | throwError "extend_space: the σ-algebra on {Ω} must be a local hypothesis, but {mΩ} is not"
  return { Ω := Ωf, mΩ := mf, P := Pf, hP := ← findIsProbabilityMeasure? P }

/-- The local hypotheses of type `Measure Ω`, with `Ω` a local hypothesis, that `e` mentions. -/
def measureFVars (e : Expr) : MetaM (Array FVarId) := do
  let mut out := #[]
  for f in (Lean.collectFVars {} e).fvarIds do
    let ty ← whnfR (← instantiateMVars (← f.getType))
    if ty.isAppOfArity ``Measure 2 && ty.appFn!.appArg!.isFVar then out := out.push f
  return out

/-- The local hypotheses depending on the space, directly or through other hypotheses. The space
itself, its σ-algebra, the measure and its `IsProbabilityMeasure` hypothesis are included. -/
def spaceDependents (sp : ProbSpace) : MetaM FVarIdSet := do
  let mut dep : FVarIdSet := {}
  for f in #[sp.Ω, sp.mΩ, sp.P] ++ sp.hP.toArray do dep := dep.insert f
  for d in ← getLCtx do
    if d.isImplementationDetail || dep.contains d.fvarId then continue
    -- A hypothesis introduced by `have` may still carry assigned metavariables in its type.
    let mentions (e : Expr) : MetaM Bool := return (← instantiateMVars e).hasAnyFVar dep.contains
    if (← mentions d.type) || (← (d.value?.mapM mentions)).getD false then
      dep := dep.insert d.fvarId
  return dep

/-- The shape of a transportable type, `ι₁ → ⋯ → ιₖ → Ω → α` or `ι₁ → ⋯ → ιₖ → Set Ω` with `Ω`
appearing nowhere else: the number `k` of leading binders, and whether it is a family of sets. -/
partial def transportShape (Ω : FVarId) (ty : Expr) (k : Nat := 0) : Option (Nat × Bool) :=
  if ty.isAppOfArity ``Set 1 then
    if ty.appArg! == .fvar Ω then some (k, true) else none
  else match ty with
    | .forallE _ d b _ =>
      if d == .fvar Ω then (if b.containsFVar Ω then none else some (k, false))
      else if d.containsFVar Ω then none
      else transportShape Ω b (k + 1)
    | _ => none

/-- Whether a local hypothesis of type `ty` can be transported along `f : Ω' → Ω`. -/
def transportable (Ω : FVarId) (ty : Expr) : Bool :=
  (transportShape Ω ty).isSome

/-- Transport `x : ι₁ → ⋯ → ιₖ → Ω → α` along `f : Ω' → Ω` to `fun i₁ … iₖ ω ↦ x i₁ … iₖ (f ω)`,
and `s : ι₁ → ⋯ → ιₖ → Set Ω` to `fun i₁ … iₖ ↦ f ⁻¹' s i₁ … iₖ`. -/
partial def transportAlong (Ω Ω' f : Expr) (x ty : Expr) : MetaM Expr := do
  if ty.isAppOfArity ``Set 1 then
    return ← mkAppM ``Set.preimage #[f, x]
  match ty with
  | .forallE n d b bi =>
    if d == Ω then
      withLocalDecl `ω bi Ω' fun ω ↦ mkLambdaFVars #[ω] (mkApp x (mkApp f ω))
    else
      let n := if n.hasMacroScopes || n.isAnonymous then `i else n
      withLocalDecl n bi d fun i ↦ do
        mkLambdaFVars #[i] (← transportAlong Ω Ω' f (mkApp x i) (b.instantiate1 i))
  | _ => throwError "extend_space: cannot transport {x} : {ty} to the extended space"

/-- The local hypotheses that `e` mentions, that depend on the space but cannot be transported:
these are generalized. The set is closed under the hypotheses their types mention, so that it is
compatible with `mkForallFVars`. -/
partial def toGeneralize (sp : ProbSpace) (deps special : FVarIdSet) (e : Expr) :
    MetaM (Array FVarId) :=
  go (Lean.collectFVars {} e).fvarIds.toList {} #[]
where
  go (todo : List FVarId) (seen : FVarIdSet) (acc : Array FVarId) : MetaM (Array FVarId) := do
    match todo with
    | [] => return acc
    | f :: todo =>
      if seen.contains f then return ← go todo seen acc
      let seen := seen.insert f
      if !deps.contains f || special.contains f then return ← go todo seen acc
      let d ← f.getDecl
      let ty ← instantiateMVars d.type
      if transportable sp.Ω ty then return ← go todo seen acc
      if d.isLet then throwError
        "extend_space: the goal depends on the local definition {Expr.fvar f}, which cannot be \
        transported to the extended space"
      go ((Lean.collectFVars {} ty).fvarIds.toList ++ todo) seen (acc.push f)

/-- Index of the binder named `n` in a `∀`-telescope. -/
partial def binderIndex? (ty : Expr) (n : Name) (i : Nat := 0) : Option Nat :=
  match ty with
  | .forallE m _ b _ => if m == n then some i else binderIndex? b n (i + 1)
  | _ => none

/-- The domain of the `i`-th binder of a `∀`-telescope. -/
def binderDomain! (ty : Expr) : Nat → Expr
  | 0 => ty.bindingDomain!
  | i + 1 => binderDomain! ty.bindingBody! i

/-- The number of leading `∀`s. -/
partial def forallArity : Expr → Nat
  | .forallE _ _ b _ => forallArity b + 1
  | _ => 0

/-! ### The hidden presentation -/

/-- The new space and what comes with it, once the extended goal has been introduced. -/
structure NewSpace where
  /-- The new space. -/
  Ω : FVarId
  /-- Its σ-algebra. -/
  mΩ : FVarId
  /-- The new measure. -/
  P : FVarId
  /-- Its `IsProbabilityMeasure` instance. -/
  hP : FVarId
  /-- The projection onto the old space. -/
  f : FVarId
  /-- `MeasurePreserving f P' P`. -/
  hf : FVarId
  /-- The new draw. -/
  Z : FVarId
  /-- Its law, or its conditional law given `f`. -/
  hZ : FVarId
  /-- `IndepFun f Z P'`, in the independent case. -/
  hind? : Option FVarId

/-- Eta-reduce every subterm. -/
def etaAll (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e ↦ return .done e.eta)

/-- Replace, in `e`, `X i₁ … iₖ (f t)` by `X' i₁ … iₖ t` and `f ⁻¹' s i₁ … iₖ` by `s' i₁ … iₖ`,
for every transported variable `(X, k, isSet, X')`. -/
partial def foldTransports (f : FVarId) (subst : Array (FVarId × Nat × Bool × Expr)) (e : Expr) :
    Expr :=
  e.replace fun e ↦
    if e.isAppOfArity ``Set.preimage 4 && e.getArg! 2 == .fvar f then
      let s := e.appArg!
      match s.getAppFn with
      | .fvar x =>
        match subst.find? (·.1 == x) with
        | some (_, k, true, s') =>
          let args := s.getAppArgs
          if args.size == k then some (mkAppN s' (args.map (foldTransports f subst))) else none
        | _ => none
      | _ => none
    else match e.getAppFn with
      | .fvar x =>
        match subst.find? (·.1 == x) with
        | some (_, k, false, X') =>
          let args := e.getAppArgs
          if h : k < args.size then
            let a := args[k]
            if a.isApp && a.appFn! == .fvar f then
              let args' := (args.extract 0 k).push a.appArg! ++ args.extract (k + 1) args.size
              some (mkAppN X' (args'.map (foldTransports f subst)))
            else none
          else none
        | _ => none
      | _ => none

/-- The old-space version of a transported random variable `x : ι₁ → ⋯ → ιₖ → Ω → α`, as a
random variable `fun ω ↦ fun i₁ … iₖ ↦ x i₁ … iₖ ω` for the independence statement. -/
partial def oldComponent (Ω ω x ty : Expr) : MetaM Expr :=
  match ty with
  | .forallE n d b bi =>
    if d == Ω then pure (mkApp x ω)
    else
      let n := if n.hasMacroScopes || n.isAnonymous then `i else n
      withLocalDecl n bi d fun i ↦ do
        mkLambdaFVars #[i] (← oldComponent Ω ω (mkApp x i) (b.instantiate1 i))
  | _ => throwError "extend_space: internal error, {x} : {ty} is not a random variable"

/-- Generalize the transports in the goal: for each transported variable `(X, v, k, isSet, name)`
with transport `v`, the goal `G` becomes `∀ (X' : _) (hX'_def : ∀ i… ω, X i… (f ω) = X' i… ω), G'`
where `G'` is `G` with `v` folded into `X'`. Returns the goal with those introduced, the new
variables and the defining equations. -/
def generalizeTransports (g : MVarId) (f : FVarId)
    (transported : Array (FVarId × Expr × Nat × Bool × Name)) :
    MetaM (MVarId × Array FVarId × Array FVarId) := g.withContext do
  let G ← instantiateMVars (← g.getType)
  let n := transported.size
  let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) ←
    transported.mapM fun (_, v, _, _, name) ↦ do
      let ty ← inferType v
      pure (name, .default, fun _ ↦ pure ty)
  let (ty, args) ← withLocalDecls decls fun X's ↦ do
    let defDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) ←
      (transported.zip X's).mapM fun ((_, v, _, _, name), X') ↦ do
        let dty ← forallTelescope (← inferType v) fun bs _ ↦ do
          mkForallFVars bs (← mkEq (mkAppN v bs).headBeta (mkAppN X' bs))
        pure (Name.mkSimple s!"h{name}_def", .default, fun _ ↦ pure dty)
    withLocalDecls defDecls fun hdefs ↦ do
      let subst := (transported.zip X's).map fun ((x, _, k, isSet, _), X') ↦ (x, k, isSet, X')
      let G' ← etaAll (foldTransports f subst G)
      let ty ← mkForallFVars (X's ++ hdefs) G'
      let rfls ← transported.mapM fun (_, v, _, _, _) ↦ do
        forallTelescope (← inferType v) fun bs _ ↦ do
          mkLambdaFVars bs (← mkEqRefl (mkAppN v bs).headBeta)
      pure (ty, transported.map (·.2.1) ++ rfls)
  let g₂ ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  g.assign (mkAppN g₂ args)
  let (fvs, g₂) ← g₂.mvarId!.introNP (2 * n)
  return (g₂, fvs.extract 0 n, fvs.extract n (2 * n))

/-- Prove the transported statement `φ'` of a hypothesis `h` about the old space: by a
`@[transfer_forward]` lemma, by transferring a copy of `h`, or, for a measurability statement or
an instance, from scratch. -/
def proveTransported (h : FVarId) (φ' : Expr) (new : NewSpace) : TacticM (Option Expr) := do
  let hE := Expr.fvar h
  let hfE := Expr.fvar new.hf
  if let some (ty, pf) ← transferForward? hE hfE then
    if ← isDefEq ty φ' then return some pf
  let hStx ← Term.exprToSyntax hE
  let hfStx ← Term.exprToSyntax hfE
  let mut tacs : Array (TSyntax `tactic) :=
    #[← `(tactic| (have h' := $hStx; transfer $hfStx at h'; exact h'))]
  if (← isClass? φ').isSome then tacs := tacs.push (← `(tactic| infer_instance))
  let funProps : Array Name := #[``Measurable, ``AEMeasurable, ``AEStronglyMeasurable,
    ``StronglyMeasurable]
  let setProps : Array Name := #[``MeasurableSet, ``NullMeasurableSet]
  if let some c := φ'.getForallBody.getAppFn.constName? then
    if funProps.contains c then tacs := tacs.push (← `(tactic| (intros; fun_prop)))
    if setProps.contains c then tacs := tacs.push (← `(tactic| (intros; measurability)))
  for tac in tacs do
    let goal ← mkFreshExprSyntheticOpaqueMVar φ'
    if let some pf ← tryTactic? goal.mvarId! tac then return some pf
  return none

/-- The independence of `Z` from the transported random variables, as the independence of `Z`
and the tuple of those whose measurability `fun_prop` can prove. -/
def deriveIndep (g : MVarId) (sp : ProbSpace) (new : NewSpace) (hind : FVarId)
    (transported : Array (FVarId × Expr × Nat × Bool)) : TacticM (Option (FVarId × MVarId)) :=
  g.withContext do
    let ΩE := Expr.fvar sp.Ω
    let mut comps : Array (Expr × Expr) := #[]
    for (x, _, _, isSet) in transported do
      if isSet then continue
      let ty ← instantiateMVars (← x.getType)
      let c ← withLocalDecl `ω .default ΩE fun ω ↦ do
        mkLambdaFVars #[ω] (← oldComponent ΩE ω (.fvar x) ty)
      let c := c.eta
      let goal ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Measurable #[c])
      if let some hc ← tryTactic? goal.mvarId! (← `(tactic| fun_prop)) then
        comps := comps.push (c, hc)
    if comps.isEmpty then return none
    let rec mkTuple : List (Expr × Expr) → MetaM (Expr × Expr)
      | [] => throwError "extend_space: internal error, empty tuple"
      | [ch] => pure ch
      | (c, hc) :: rest => do
        let (r, hr) ← mkTuple rest
        let φ ← withLocalDecl `ω .default ΩE fun ω ↦ do
          mkLambdaFVars #[ω] (← mkAppM ``Prod.mk #[(mkApp c ω).headBeta, (mkApp r ω).headBeta])
        pure (φ, ← mkAppM ``Measurable.prodMk #[hc, hr])
    let (φ, hφ) ← mkTuple comps.toList
    let fE := Expr.fvar new.f
    let tuple ← withLocalDecl `ω .default (.fvar new.Ω) fun ω ↦ do
      mkLambdaFVars #[ω] (← Core.betaReduce (mkApp φ (mkApp fE ω)))
    let ty ← mkAppM ``ProbabilityTheory.IndepFun #[tuple, .fvar new.Z, .fvar new.P]
    let goal ← mkFreshExprSyntheticOpaqueMVar ty
    let hindStx ← Term.exprToSyntax (.fvar hind)
    let hφStx ← Term.exprToSyntax hφ
    let some pf ← tryTactic? goal.mvarId!
      (← `(tactic| exact ProbabilityTheory.IndepFun.comp $hindStx $hφStx measurable_id))
      | return none
    let g ← g.assert (← hind.getUserName) ty pf
    let (hind', g) ← g.intro1P
    return some (hind', g)

/-- For a kernel `κ.comap X hX` with `X` a transported variable, the conditional law of `Z` given
`X` on the new space, `HasCondDistrib Z (fun ω ↦ X (f ω)) κ P'`. -/
def deriveCondDistrib (g : MVarId) (new : NewSpace) (κ : Expr) (transported : FVarIdSet) :
    TacticM (Option (FVarId × MVarId)) := g.withContext do
  unless κ.isAppOfArity ``ProbabilityTheory.Kernel.comap 9 do return none
  let X := κ.getArg! 7
  let .fvar x := X | return none
  unless transported.contains x do return none
  let κ₀ := κ.getArg! 6
  let fE := Expr.fvar new.f
  let Xf ← withLocalDecl `ω .default (.fvar new.Ω) fun ω ↦
    mkLambdaFVars #[ω] (mkApp X (mkApp fE ω))
  let ty ← mkAppM ``ProbabilityTheory.HasCondDistrib #[.fvar new.Z, Xf, κ₀, .fvar new.P]
  let goal ← mkFreshExprSyntheticOpaqueMVar ty
  let hZStx ← Term.exprToSyntax (.fvar new.hZ)
  let some pf ← tryTactic? goal.mvarId!
    (← `(tactic| exact ProbabilityTheory.HasCondDistrib.comp_right $hZStx)) | return none
  let g ← g.assert (← new.hZ.getUserName) ty pf
  let (hZ', g) ← g.intro1P
  return some (hZ', g)

/-- Hide the extension. The new space and its objects take the names of the old ones, which are
renamed with `₀`; every hypothesis about the old space is transported when possible; the
transports `fun ω ↦ X (f ω)` become fresh variables `X` with defining equations
`hX_def : ∀ ω, X₀ (f ω) = X ω`; the independence of `Z` is restated against the transported random
variables; and, for a kernel `κ.comap X hX`, the conditional law of `Z` is stated given `X`.
With `clearOld`, the old space, the map and everything mentioning them are cleared. -/
def hidePresentation (g : MVarId) (sp : ProbSpace) (deps special : FVarIdSet) (new : NewSpace)
    (gensOld gensNew : Array FVarId) (κ? : Option Expr) (clearOld : Bool) : TacticM MVarId := do
  let ΩE := Expr.fvar sp.Ω
  let Ω'E := Expr.fvar new.Ω
  let fE := Expr.fvar new.f
  let hfE := Expr.fvar new.hf
  -- The old objects, in context order, with their names.
  let olds ← g.withContext do
    let mut out : Array (FVarId × Name) := #[]
    for d in ← getLCtx do
      if !d.isImplementationDetail && deps.contains d.fvarId then
        out := out.push (d.fvarId, d.userName)
    pure out
  let origName (x : FVarId) : Name := ((olds.find? (·.1 == x)).map (·.2)).getD .anonymous
  -- 1. The old objects are renamed with `₀`, and the new space takes the old names.
  let mut g := g
  for (x, n) in olds do
    unless n.hasMacroScopes do g ← g.rename x (n.appendAfter "₀")
  g ← g.rename new.Ω (origName sp.Ω)
  g ← g.rename new.P (origName sp.P)
  unless (origName sp.mΩ).hasMacroScopes do g ← g.rename new.mΩ (origName sp.mΩ)
  if let some hP := sp.hP then
    unless (origName hP).hasMacroScopes do g ← g.rename new.hP (origName hP)
  -- 2. `Measurable f`, for `fun_prop` and `measurability`.
  let (hfm, g') ← g.withContext do
    let g ← g.assert `hfm (← mkAppM ``Measurable #[fE])
      (← mkAppM ``MeasurePreserving.measurable #[hfE])
    g.intro1P
  g := g'
  -- 3. The transportable variables and their transports.
  let transported ← g.withContext do
    let mut out : Array (FVarId × Expr × Nat × Bool) := #[]
    for (x, _) in olds do
      if special.contains x then continue
      let ty ← instantiateMVars (← x.getType)
      if ← isProp ty then continue
      if let some (k, isSet) := transportShape sp.Ω ty then
        out := out.push (x, ← transportAlong ΩE Ω'E fE (.fvar x) ty, k, isSet)
    pure out
  let transportedSet : FVarIdSet := transported.foldl (fun s t ↦ s.insert t.1) {}
  let xs := #[ΩE, .fvar sp.mΩ, .fvar sp.P] ++ sp.hP.toArray.map Expr.fvar
    ++ transported.map (Expr.fvar ·.1)
  let vs := #[Ω'E, .fvar new.mΩ, .fvar new.P] ++ (if sp.hP.isSome then #[.fvar new.hP] else #[])
    ++ transported.map (·.2.1)
  -- 4. The hypotheses about the old space are transported when possible.
  let mut moved : Array FVarId := #[]
  for (h, n) in olds do
    if special.contains h || transportedSet.contains h || gensOld.contains h then continue
    let r ← g.withContext do
      let φ ← instantiateMVars (← h.getType)
      unless ← isProp φ do return none
      if φ.hasAnyFVar (fun x ↦ deps.contains x && !special.contains x
          && !transportedSet.contains x) then
        return none
      let φ' ← Core.betaReduce (φ.replaceFVars xs vs)
      let ok ← try check φ'; pure true catch _ => pure false
      unless ok do return none
      let some pf ← proveTransported h φ' new | return none
      let g ← g.assert n φ' pf
      let (h', g) ← g.intro1P
      return some (h', g)
    if let some (h', g') := r then
      g := g'
      moved := moved.push h'
  -- 5. The independence of `Z`, against the transported random variables.
  let mut toClear : Array FVarId := #[hfm]
  if let some hind := new.hind? then
    if let some (hind', g') ← deriveIndep g sp new hind transported then
      g := g'
      moved := moved.push hind'
      toClear := toClear.push hind
  -- 6. The conditional law of `Z` given the conditioning variable, for `κ.comap X hX`.
  if let some κ := κ? then
    if let some (hZ', g') ← deriveCondDistrib g new κ transportedSet then
      g := g'
      moved := moved.push hZ'
      toClear := toClear.push new.hZ
  -- 7. The transports become fresh variables, named as the old ones.
  let mut hdefs : Array FVarId := #[]
  unless transported.isEmpty do
    let (reverted, g') ← g.revert (moved ++ gensNew)
    let (g', _, hdefs') ← generalizeTransports g' new.f
      (transported.map fun (x, v, k, isSet) ↦ (x, v, k, isSet, origName x))
    let (_, g') ← g'.introNP reverted.size
    g := g'
    hdefs := hdefs'
  -- 8. Clean up.
  if clearOld then
    toClear := toClear ++ hdefs ++ #[new.f, new.hf] ++ olds.map (·.1)
  let sorted ← g.withContext do sortFVarIds toClear
  g.tryClearMany sorted

/-! ### The tactics -/

/-- How the extended space is presented. -/
inductive ExtendMode where
  /-- `extend_space_map`: the new space is `Ω'`, with the map `f : Ω' → Ω` explicit. -/
  | map
  /-- `extend_space`: the new space takes the names of the old one, which is renamed with `₀`. -/
  | hidden
  /-- `extend_space!`: as `hidden`, and the old space is cleared. -/
  | clear

/-- The common implementation of `extend_space`, `extend_space!` and `extend_space_map`. -/
def extendSpace (mode : ExtendMode) (μ : Term) (P? : Option Ident) (given : Array Name) :
    TacticM Unit := withMainContext do
  let tac := match mode with
    | .map => "extend_space_map"
    | .hidden => "extend_space"
    | .clear => "extend_space!"
  let g ← getMainGoal
  let T₀ ← instantiateMVars (← g.getType)
  -- The measure or kernel to extend with.
  let μE ← Term.elabTerm μ none
  Term.synthesizeSyntheticMVarsNoPostponing
  let μE ← instantiateMVars μE
  let μty ← whnfR (← inferType μE)
  let (isKernel, E, dom?) ←
    if μty.isAppOfArity ``Measure 2 then pure (false, μty.appFn!.appArg!, none)
    else if μty.isAppOfArity ``Kernel 4 then
      let as := μty.getAppArgs
      pure (true, as[1]!, some as[0]!)
    else throwError
      "{tac}: {μE} is neither a measure nor a kernel; it has type{indentExpr μty}"
  -- The measure to extend.
  let PE ← match P? with
    | some P => pure (Expr.fvar (← getFVarId P))
    | none => do
      let mut cands ← measureFVars T₀
      if let .fvar m := μE then cands := cands.erase m
      if let some dom := dom? then
        cands ← cands.filterM fun P ↦ do
          let ty ← whnfR (← inferType (.fvar P))
          isDefEq ty.appFn!.appArg! dom
      match cands with
      | #[P] => pure (Expr.fvar P)
      | #[] => throwError
        "{tac}: the goal mentions no measure on a local space; name one with `using`"
      | _ => throwError
        "{tac}: the goal mentions several measures, {cands.map Expr.fvar}; choose one with `using`"
  let sp ← ProbSpace.ofMeasure PE
  let ΩE := Expr.fvar sp.Ω
  if let some dom := dom? then
    unless ← isDefEq dom ΩE do
      throwError "{tac}: the kernel {μE} is on {dom}, not on {ΩE}"
  -- The product `Ω × E` has to live in the universe of `Ω`.
  let lvlΩ ← getDecLevel ΩE
  let lvlE ← getDecLevel E
  unless ← isLevelDefEq (mkLevelMax lvlΩ lvlE) lvlΩ do
    throwError "{tac}: {E} lives in universe {toString lvlE} and {ΩE} in universe \
      {toString lvlΩ},\nso the product {ΩE} × {E} does not live in the universe of {ΩE}: lift \
      {E} with `ULift`"
  -- Hypotheses the goal depends on that cannot be transported are generalized.
  let deps ← spaceDependents sp
  let mut special : FVarIdSet := {}
  for f in #[sp.Ω, sp.mΩ, sp.P] ++ sp.hP.toArray do special := special.insert f
  let gens ← sortFVarIds (← toGeneralize sp deps special T₀)
  let T ← mkForallFVars (gens.map Expr.fvar) T₀
  -- The motive: the goal on a space `Ω'` with a map `f : Ω' → Ω`.
  let motive ←
    withLocalDecl (.mkSimple "Ω'") .implicit (← inferType ΩE) fun Ω' ↦ do
    withLocalDecl (.mkSimple "mΩ'") .instImplicit (← mkAppM ``MeasurableSpace #[Ω']) fun mΩ' ↦ do
    withLocalDecl (.mkSimple "P'") .default (← mkAppOptM ``Measure #[Ω', mΩ']) fun P' ↦ do
    withLocalDecl (.mkSimple "hP'") .instImplicit
      (← mkAppOptM ``IsProbabilityMeasure #[Ω', mΩ', P']) fun hP' ↦ do
    withLocalDecl `f .default (← mkArrow Ω' ΩE) fun f ↦ do
      let mut xs := #[ΩE, .fvar sp.mΩ, PE]
      let mut vs := #[Ω', mΩ', P']
      if let some h := sp.hP then
        xs := xs.push (.fvar h)
        vs := vs.push hP'
      for x in (Lean.collectFVars {} T).fvarIds do
        if deps.contains x && !special.contains x then
          let ty ← instantiateMVars (← x.getType)
          xs := xs.push (.fvar x)
          vs := vs.push (← transportAlong ΩE Ω' f (.fvar x) ty)
      let T' ← Core.betaReduce (T.replaceFVars xs vs)
      try check T'
      catch e => throwError
        "{tac}: the goal does not survive the change of space:{indentExpr T'}\n\
        {e.toMessageData}"
      mkLambdaFVars #[Ω', mΩ', P', hP', f] T'
  -- Apply the principle.
  let thm := if isKernel then ``RDo.wlog_extend_kernel else ``RDo.wlog_extend
  let c := mkConst thm [lvlΩ, lvlE]
  let cty ← inferType c
  let idx (n : Name) : TacticM Nat := do
    let some i := binderIndex? cty n
      | throwError "{tac}: `{thm}` no longer has the expected shape"
    pure i
  let iTransfer ← idx `transfer
  let (args, bis, concl) ← forallMetaBoundedTelescope cty (iTransfer + 1)
  let assign (n : Name) (e : Expr) : TacticM Unit := do
    unless ← isDefEq args[← idx n]! e do
      throwError "{tac}: cannot use {e} as `{n}` of `{thm}`"
  assign `Ω ΩE
  assign `mΩ (.fvar sp.mΩ)
  assign `P PE
  if let some h := sp.hP then assign `hP (.fvar h)
  assign `motive motive
  assign (if isKernel then `κ else `μ) μE
  unless ← isDefEq concl T do
    throwError "{tac}: the goal does not have the expected shape{indentExpr T}"
  for (a, b) in args.zip bis do
    if b.isInstImplicit && !(← a.mvarId!.isAssigned) then
      a.mvarId!.assign (← synthInstance (← instantiateMVars (← a.mvarId!.getType)))
  g.assign (mkAppN (mkAppN c args) (gens.map Expr.fvar))
  -- The extended goal: introduce the new space and what was generalized.
  let extended := args[← idx `extended]!.mvarId!
  extended.setKind .syntheticOpaque
  extended.setTag `extended
  let nNames := match mode, isKernel with
    | .map, false => 7
    | .map, true => 6
    | _, false => 5
    | _, true => 4
  if given.size > nNames then
    throwError "{tac}: at most {nNames} names may be given"
  let pick (defaults : Array Name) (i : Nat) : Name :=
    if h : i < given.size then given[i] else defaults[i]!
  let intros : Array Name := match mode with
    | .map =>
      let d := #[.mkSimple "Ω'", .mkSimple "P'", `f, `hf, `Z, `hZ, `hind]
      #[pick d 0, `inst, pick d 1, `inst, pick d 2, pick d 3, pick d 4, pick d 5]
        ++ (if isKernel then #[] else #[pick d 6])
    | _ =>
      let d := if isKernel then #[`Z, `hZ, `f, `hf] else #[`Z, `hZ, `hind, `f, `hf]
      let (f, hf) := if isKernel then (pick d 2, pick d 3) else (pick d 3, pick d 4)
      #[.mkSimple "Ω'", `inst, .mkSimple "P'", `inst, f, hf, pick d 0, pick d 1]
        ++ (if isKernel then #[] else #[pick d 2])
  let (fvs, extended) ← extended.introN intros.size intros.toList
  let gensNames ← gens.toList.mapM fun x ↦ do
    let n ← x.getUserName
    pure (match mode with | .map => n.appendAfter "'" | _ => n)
  let (gensNew, extended) ← extended.introN gens.size gensNames
  let extended ← match mode with
    | .map => pure extended
    | _ =>
      let new : NewSpace := ⟨fvs[0]!, fvs[1]!, fvs[2]!, fvs[3]!, fvs[4]!, fvs[5]!, fvs[6]!,
        fvs[7]!, if isKernel then none else some fvs[8]!⟩
      hidePresentation extended sp deps special new gens gensNew
        (if isKernel then some μE else none) (match mode with | .clear => true | _ => false)
  -- The transfer goal, with the original goal as its conclusion rather than `motive Ω P id`.
  let transfer := args[iTransfer]!.mvarId!
  let tty ← instantiateMVars (← transfer.getType)
  -- Only the binders of the theorem's hypothesis: its conclusion may itself be a `∀`.
  let nBinders := forallArity (binderDomain! cty iTransfer)
  let tty' ← forallBoundedTelescope tty (some nBinders) fun xs _ ↦ mkForallFVars xs T
  let transfer' ← mkFreshExprSyntheticOpaqueMVar tty' (tag := `transfer)
  transfer.assign transfer'
  -- Discharge the transfer obligation with the `transfer` tactic when it can; leave it otherwise.
  let rest := (← getGoals).drop 1
  let s ← saveState
  -- `tryCatchRuntimeEx`: a failure inside `measurability` may be a maximum recursion depth error,
  -- which `try … catch` lets through.
  let transferLeft ← tryCatchRuntimeEx
    (do
      setGoals [transfer'.mvarId!]
      evalTactic (← `(tactic| transfer))
      unless (← getUnsolvedGoals).isEmpty do throwError "transfer left goals"
      pure [])
    (fun _ ↦ do
      s.restore
      pure [transfer'.mvarId!])
  setGoals ([extended] ++ transferLeft ++ rest)

/-- `extend_space μ` adds to the probability space `(Ω, P)` of the goal a random variable `Z` with
law `μ`, a probability measure on some `E`, independent of everything defined on `Ω`. The names
are kept: `Ω`, `P`, every random variable `X : Ω → α` and every event `s : Set Ω` now denote
objects on the extended space, hypotheses about them are transported, and the goal reads as
before. The context gains

* `Z : Ω → E`, `hZ : HasLaw Z μ P`, and `hind`, the independence of `Z` from the transported
  random variables, as a tuple;
* the old space and its objects, renamed `Ω₀`, `P₀`, `X₀`, …, with `f : Ω → Ω₀`,
  `hf : MeasurePreserving f P P₀`, and the defining equations `hX_def : ∀ ω, X₀ (f ω) = X ω`.
  A hypothesis that cannot be transported stays about the old space, under its `₀` name.

Two goals may be left: `extended`, the goal on the new space, and `transfer`, the obligation that
the statement pulls back along a measure-preserving map, which makes the replacement sound. The
`transfer` tactic is run on it, and it is only left when that fails.

* `extend_space! μ` also clears the old space, the map and everything mentioning them, except
  what Lean does not let a tactic clear: hypotheses introduced by `variable`.
* `extend_space κ` for a Markov kernel `κ : Kernel Ω E` gives instead a draw with conditional law
  `κ` given the old space, `hZ : HasCondDistrib Z f κ P`, and no `hind`. For `κ.comap X hX` with
  `X` a random variable, `hZ` is stated as `HasCondDistrib Z X κ P`.
* `extend_space μ using P` names the measure to extend rather than reading it off the goal.
* `extend_space μ with Z hZ hind f hf` names what is introduced (`with Z hZ f hf` for a kernel).

The space, its σ-algebra and the measure have to be local hypotheses, since the goal is abstracted
over them, and `E` has to live in the universe of `Ω` or in a smaller one. -/
syntax (name := extendSpaceTac) "extend_space" ppSpace term (" using " ident)?
  (" with " (ppSpace colGt ident)+)? : tactic

@[inherit_doc extendSpaceTac]
syntax (name := extendSpaceClearTac) "extend_space!" ppSpace term (" using " ident)?
  (" with " (ppSpace colGt ident)+)? : tactic

/-- `extend_space_map μ` is the explicit form of `extend_space μ`: nothing is renamed, the goal is
restated on a new space `Ω'` with a measure-preserving map `f : Ω' → Ω`, and the context gains
`hf : MeasurePreserving f P' P`, `Z : Ω' → E`, `hZ : HasLaw Z μ P'` and `hind : IndepFun f Z P'`.
Every random variable `X : Ω → α` of the goal becomes `fun ω ↦ X (f ω)` and every event
`s : Set Ω` becomes `f ⁻¹' s`. Hypotheses about the old space stay as they are and are pulled back
on demand, by `transfer hf at h`, `hX.comp hf.hasLaw` for a law, `hind.comp hX measurable_id` for
the independence of `X ∘ f` and `Z`, or `h.comp_measurePreserving hf` for a conditional law. A
hypothesis the goal itself depends on is generalized and reintroduced under a primed name.

* `extend_space_map κ` for a Markov kernel `κ : Kernel Ω E` gives instead
  `hZ : HasCondDistrib Z f κ P'`, and no `hind`.
* `extend_space_map μ using P` names the measure to extend.
* `extend_space_map μ with Ω' P' f hf Z hZ hind` names what is introduced. -/
syntax (name := extendSpaceMapTac) "extend_space_map" ppSpace term (" using " ident)?
  (" with " (ppSpace colGt ident)+)? : tactic

elab_rules : tactic
  | `(tactic| extend_space $μ $[using $P?]? $[with $names?*]?) =>
    extendSpace .hidden μ P? ((names?.map (·.map (·.getId))).getD #[])
  | `(tactic| extend_space! $μ $[using $P?]? $[with $names?*]?) =>
    extendSpace .clear μ P? ((names?.map (·.map (·.getId))).getD #[])
  | `(tactic| extend_space_map $μ $[using $P?]? $[with $names?*]?) =>
    extendSpace .map μ P? ((names?.map (·.map (·.getId))).getD #[])

end RDo.Tactic

end
