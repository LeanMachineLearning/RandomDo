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

`extend_space μ` replaces the probability space `(Ω, P)` of the goal by one that also carries a
random variable `Z` with law `μ`, independent of everything defined on `Ω`. It is the tactic form
of "without loss of generality, let `Z ~ μ` be independent of the rest". The new space is `Ω × E`
with the product measure, but the goal is stated on an abstract space `Ω'` related to `Ω` by a
measure-preserving map `f : Ω' → Ω`, which is all the extended goal may use.

Every random variable `X : Ω → α` the goal mentions becomes `fun ω ↦ X (f ω)`, every event
`s : Set Ω` becomes `f ⁻¹' s`, and the measure becomes `P'`. Hypotheses about the old space stay
in the context untouched, since they are still true: they are pulled back along `f` on demand
(`hX.comp hf.hasLaw`, `hind.comp hX measurable_id`, `h.comp_measurePreserving hf`, …). A
hypothesis the goal itself depends on, such as a measurability proof inside a `Kernel.comap`, is
generalized and reintroduced under a primed name.

Two goals are left:

* `extended`: the same statement on `(Ω', P')`, with `f`, `hf : MeasurePreserving f P' P`, `Z`,
  `hZ : HasLaw Z μ P'` and `hind : IndepFun f Z P'` in the context;
* `transfer`: the obligation that the statement pulls back along any measure-preserving map. This
  is what makes the replacement sound. The `transfer` tactic discharges it for laws, events,
  integrals, independence and conditional laws, using the `@[transfer]` lemmas of this file, and
  `extend_space` runs it: the goal is only left when the tactic fails. In the extended goal,
  `transfer hf at h` pulls a hypothesis `h` about the old space back to the new one.

`extend_space κ` for a Markov kernel `κ : Kernel Ω E` does the same with a draw whose conditional
law given the old space is `κ`: it provides `hZ : HasCondDistrib Z f κ P'` instead of a law and an
independence. For a draw conditional on a random variable `X`, use `κ.comap X hX` and read the
result through `HasCondDistrib.comp_right`.

Compare `alg_env_trace`: there the new space is not an extension of the old one, only a space with
the same trajectory law, so its `transfer` obligation is about laws and has to be proved
statement by statement. Here the projection `f` is measure preserving, which is a uniform principle.

## Main results

* `RDo.wlog_extend`, `RDo.wlog_extend_kernel`: the principles behind the tactic.
* `MeasureTheory.MeasurePreserving.map_fun_comp`, `hasLaw_fun_comp_iff`, `indepFun_fun_comp_iff`,
  `hasCondDistrib_fun_comp_iff`: pulling statements back along a measure-preserving map.
* `ProbabilityTheory.HasCondDistrib.comp_measurePreserving`: the forward direction, without any
  measurability assumption.
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

end MeasureTheory.MeasurePreserving

/-- A conditional law pulls back along a measure-preserving map. -/
lemma ProbabilityTheory.HasCondDistrib.comp_measurePreserving {Ω Ω' 𝓧 𝓨 : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {m𝓧 : MeasurableSpace 𝓧}
    {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} {P' : Measure Ω'} {f : Ω' → Ω} {X : Ω → 𝓧}
    {Y : Ω → 𝓨} {κ : Kernel 𝓧 𝓨} (h : HasCondDistrib Y X κ P) (hf : MeasurePreserving f P' P) :
    HasCondDistrib (fun ω ↦ Y (f ω)) (fun ω ↦ X (f ω)) κ P' := by
  have hX := h.aemeasurable_fst
  unfold HasCondDistrib at h ⊢
  rw [hf.map_fun_comp hX]
  exact h.comp hf.hasLaw

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
    let mentions (e : Expr) : Bool := e.hasAnyFVar dep.contains
    if mentions d.type || (d.value?.map mentions).getD false then dep := dep.insert d.fvarId
  return dep

/-- Whether a local hypothesis of type `ty` can be transported along `f : Ω' → Ω`: its type has to
be `ι₁ → ⋯ → ιₖ → Ω → α` or `ι₁ → ⋯ → ιₖ → Set Ω`, with `Ω` appearing nowhere else. -/
partial def transportable (Ω : FVarId) (ty : Expr) : Bool :=
  if ty.isAppOfArity ``Set 1 then ty.appArg! == .fvar Ω
  else match ty with
    | .forallE _ d b _ =>
      if d == .fvar Ω then !b.containsFVar Ω
      else !d.containsFVar Ω && transportable Ω b
    | _ => false

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

/-- `extend_space μ` replaces the probability space `(Ω, P)` of the goal by one that also carries
a random variable `Z` with law `μ`, independent of everything defined on `Ω`. `μ` is a probability
measure on some `E`. Two goals are left:

* `extended`: the same statement on a space `(Ω', P')` with a measure-preserving map
  `f : Ω' → Ω`. Every random variable `X : Ω → α` of the goal becomes `fun ω ↦ X (f ω)` and every
  event `s : Set Ω` becomes `f ⁻¹' s`; the context gains `hf : MeasurePreserving f P' P`,
  `hZ : HasLaw Z μ P'` and `hind : IndepFun f Z P'`. Hypotheses about the old space stay as they
  are and may be pulled back along `f`, for instance by `hX.comp hf.hasLaw` for a law,
  `hind.comp hX measurable_id` for independence of `X ∘ f` and `Z`, or
  `h.comp_measurePreserving hf` for a conditional law. A hypothesis the goal itself depends on is
  generalized and reintroduced under a primed name.
* `transfer`: the obligation that the statement pulls back along a measure-preserving map, which is
  what makes the replacement sound. See `MeasurePreserving.map_fun_comp` and the
  `MeasurePreserving.*_fun_comp_iff` lemmas.

* `extend_space κ` for a Markov kernel `κ : Kernel Ω E` gives instead a draw with conditional law
  `κ` given the old space, `hZ : HasCondDistrib Z f κ P'`, and no `hind`.
* `extend_space μ using P` names the measure to extend rather than reading it off the goal.
* `extend_space μ with Ω' P' f hf Z hZ hind` names what is introduced.

The space, its σ-algebra and the measure have to be local hypotheses, since the goal is abstracted
over them, and `E` has to live in the universe of `Ω` or in a smaller one. -/
syntax (name := extendSpaceTac) "extend_space" ppSpace term (" using " ident)?
  (" with " (ppSpace colGt ident)+)? : tactic

elab_rules : tactic
  | `(tactic| extend_space $μ $[using $P?]? $[with $names?*]?) => withMainContext do
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
        "extend_space: {μE} is neither a measure nor a kernel; it has type{indentExpr μty}"
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
          "extend_space: the goal mentions no measure on a local space; name one with `using`"
        | _ => throwError
          "extend_space: the goal mentions several measures, {cands.map Expr.fvar}; choose one \
          with `using`"
    let sp ← ProbSpace.ofMeasure PE
    let ΩE := Expr.fvar sp.Ω
    if let some dom := dom? then
      unless ← isDefEq dom ΩE do
        throwError "extend_space: the kernel {μE} is on {dom}, not on {ΩE}"
    -- The product `Ω × E` has to live in the universe of `Ω`.
    let lvlΩ ← getDecLevel ΩE
    let lvlE ← getDecLevel E
    unless ← isLevelDefEq (mkLevelMax lvlΩ lvlE) lvlΩ do
      throwError "extend_space: {E} lives in universe {toString lvlE} and {ΩE} in universe \
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
          "extend_space: the goal does not survive the change of space:{indentExpr T'}\n\
          {e.toMessageData}"
        mkLambdaFVars #[Ω', mΩ', P', hP', f] T'
    -- Apply the principle.
    let thm := if isKernel then ``RDo.wlog_extend_kernel else ``RDo.wlog_extend
    let c := mkConst thm [lvlΩ, lvlE]
    let cty ← inferType c
    let idx (n : Name) : TacticM Nat := do
      let some i := binderIndex? cty n
        | throwError "extend_space: `{thm}` no longer has the expected shape"
      pure i
    let iTransfer ← idx `transfer
    let (args, bis, concl) ← forallMetaBoundedTelescope cty (iTransfer + 1)
    let assign (n : Name) (e : Expr) : TacticM Unit := do
      unless ← isDefEq args[← idx n]! e do
        throwError "extend_space: cannot use {e} as `{n}` of `{thm}`"
    assign `Ω ΩE
    assign `mΩ (.fvar sp.mΩ)
    assign `P PE
    if let some h := sp.hP then assign `hP (.fvar h)
    assign `motive motive
    assign (if isKernel then `κ else `μ) μE
    unless ← isDefEq concl T do
      throwError "extend_space: the goal does not have the expected shape{indentExpr T}"
    for (a, b) in args.zip bis do
      if b.isInstImplicit && !(← a.mvarId!.isAssigned) then
        a.mvarId!.assign (← synthInstance (← instantiateMVars (← a.mvarId!.getType)))
    g.assign (mkAppN (mkAppN c args) (gens.map Expr.fvar))
    -- The extended goal: introduce the new space, then what was generalized, under primed names.
    let extended := args[← idx `extended]!.mvarId!
    extended.setKind .syntheticOpaque
    extended.setTag `extended
    let given := (names?.map (·.map (·.getId))).getD #[]
    let defaults : Array Name := #[.mkSimple "Ω'", .mkSimple "P'", `f, `hf, `Z, `hZ, `hind]
    let nNames := if isKernel then 6 else 7
    if given.size > nNames then
      throwError "extend_space: at most {nNames} names may be given"
    let pick (i : Nat) : Name := if h : i < given.size then given[i] else defaults[i]!
    let mut intros : Array Name := #[pick 0, `inst, pick 1, `inst, pick 2, pick 3, pick 4, pick 5]
    if !isKernel then intros := intros.push (pick 6)
    let (_, extended) ← extended.introN intros.size intros.toList
    let primed ← gens.toList.mapM fun f ↦ do pure ((← f.getUserName).appendAfter "'")
    let (_, extended) ← extended.introN gens.size primed
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

end RDo.Tactic

end
