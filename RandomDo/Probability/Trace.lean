/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.Probability.Record
public import RandomDo.Tactic.IsMarkov
public import RandomDo.Monad.Instances
public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib

/-!
# Trace semantics for `rdo` programs

An `rdo` program denotes a measure, and a measure alone has no random variables: there is nothing
to condition on and nothing to be independent of. This file adds the missing layer.

To every `rdo` program we attach a *trace*: a measurable space `Ω` recording the value drawn at
each `←` in the program, a Markov kernel `P : Kernel γ Ω` giving the joint law of those draws as
a function of the program's parameters, and a *deterministic* readout `out : γ × Ω → β`
reconstructing the program's result from its parameters and its draws. The defining property is

`(P c).map (fun ω ↦ out (c, ω)) = prog c`,

that is, running the program is the same as drawing a trace and reading the answer off it.
This is `HasTrace prog P out`.

The point of the construction is that `P` is built by `Kernel.compProd`, one factor per `←`
in the program: the *shape of the program is the shape of `P`*. All the probabilistic content
then comes from two facts about `κ ⊗ₖ η`, proved once in the `Coordinates` section below:

* the first component of the trace has law `κ` (`HasLaw.fst_compProd`);
* the second has conditional distribution `η` given the first
  (`hasCondDistrib_snd_compProd`), and is *independent* of it when `η` does not read the
  first (`indepFun_snd_compProd_prodMkRight`).

Iterating those along the nesting of `⊗ₖ` reads the conditional law of every draw given the
draws before it straight off the program text.

## Main definitions

* `RDo.HasTrace prog P out`: `P` and `out` are a trace representation of the program `prog`.

## Main results

* `RDo.HasTrace.bind`: the trace of `let x ← p; q` is the composition-product of the traces of
  `p` and of `q`. This is the rule that turns program structure into kernel structure.
* `RDo.HasTrace.sample`, `RDo.HasTrace.pure`, `RDo.HasTrace.bindPure`: the remaining `rdo`
  constructs.
* `RDo.HasTrace.hasLaw_out`: the program's result, as a random variable on the trace space, has
  the program's law.
* `ProbabilityTheory.HasLaw.fst_compProd`, `ProbabilityTheory.HasCondDistrib.fst_compProd`: laws
  and conditional laws of earlier draws survive appending a further draw.
* `RDo.hasCondDistrib_snd_compProd`, `RDo.indepFun_snd_compProd_prodMkRight`: the conditional law
  of the last draw given all the previous ones, and its independence in the case where the
  program does not look at them.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MeasurableSpacePure MeasurableSpaceBind

namespace RDo

universe u

section Prerequisites

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]

/-- Pushing a measure through a kernel and then through a map, in the form used to peel one `←`
off a program: the first component of the product is the value the rest of the program sees. -/
lemma map_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {g : α × β → δ} (hg : Measurable g) :
    (μ ⊗ₘ κ).map g = μ.bind fun a ↦ (κ a).map fun b ↦ g (a, b) := by
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hg]
  refine Measure.bind_congr_right (.of_forall fun a ↦ ?_)
  rw [Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hg measurable_prodMk_left]
  rfl

/-- `Measure.bind` sees through a `Measure.map` on the left. -/
lemma bind_map (μ : Measure α) {f : α → β} (hf : Measurable f) {k : β → Measure δ}
    (hk : Measurable k) : (μ.map f).bind k = μ.bind fun a ↦ k (f a) := by
  rw [Measure.bind, Measure.bind, Measure.map_map hk hf]
  rfl

end Prerequisites

variable {γ Ω Ω' δ : Type*} {α β : Type u}
  [MeasurableSpace γ] [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]

/-- `HasTrace prog P out` states that the family of measures `prog : γ → Measure β` is realised by
drawing a *trace* `ω : Ω` from the Markov kernel `P` and reading the deterministic value
`out (c, ω)` off it.

`Ω` is meant to be the space of all the values the program draws at its `←`s, and `P` an iterated
`Kernel.compProd`, one factor per `←`. See the module docstring. -/
structure HasTrace (prog : γ → Measure β) (P : Kernel γ Ω) (out : γ × Ω → β) : Prop where
  /-- The readout is deterministic: all the randomness of the program sits in the trace. -/
  measurable_out : Measurable out
  /-- Drawing a trace and reading the answer off it runs the program. -/
  map_eq (c : γ) : (P c).map (fun ω ↦ out (c, ω)) = prog c

/-- The kernel attached to a subprogram known to be Markov. Unlike `IsMarkov.toKernel`, the proof
is an ordinary argument rather than an instance, so `IsMarkovKernel` can be found by unification on
the kernel term alone, whatever the proof is — including while it is still an unsolved goal. This
is what `rdo_trace` emits at the leaves of a program. -/
def markovKernel (prog : γ → Measure α) (h : IsMarkov prog) : Kernel γ α := ⟨prog, h.measurable⟩

@[simp]
lemma markovKernel_apply (prog : γ → Measure α) (h : IsMarkov prog) (c : γ) :
    markovKernel prog h c = prog c := rfl

instance (prog : γ → Measure α) (h : IsMarkov prog) : IsMarkovKernel (markovKernel prog h) :=
  ⟨fun c ↦ h.isProbabilityMeasure c⟩

namespace HasTrace

variable {prog : γ → Measure β} {P : Kernel γ Ω} {out : γ × Ω → β}

/-- The program's result, as a random variable on the trace space, has the program's law. -/
lemma hasLaw_out (h : HasTrace prog P out) (c : γ) :
    HasLaw (fun ω ↦ out (c, ω)) (prog c) (P c) where
  aemeasurable := (h.measurable_out.comp measurable_prodMk_left).aemeasurable
  map_eq := h.map_eq c

/-- A traced program is the kernel obtained by reading `out` off `P`. -/
lemma eq_map [IsSFiniteKernel P] (h : HasTrace prog P out) :
    prog = ⇑((Kernel.id ×ₖ P).map out) := by
  funext c
  rw [← h.map_eq c, Kernel.map_apply _ h.measurable_out, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map h.measurable_out measurable_prodMk_left]
  rfl

/-- A program with a Markov trace is a Markov kernel. This is the `is_markov` property, obtained
for free from the trace. -/
lemma isMarkov (h : HasTrace prog P out) [IsMarkovKernel P] : IsMarkov prog where
  measurable' := by rw [h.eq_map]; exact Kernel.measurable _
  isProbabilityMeasure c := by
    rw [← h.map_eq c]
    exact Measure.isProbabilityMeasure_map
      (h.measurable_out.comp measurable_prodMk_left).aemeasurable

lemma congr {prog' : γ → Measure β} (h : HasTrace prog P out) (h' : ∀ c, prog' c = prog c) :
    HasTrace prog' P out :=
  ⟨h.measurable_out, fun c ↦ (h.map_eq c).trans (h' c).symm⟩

/-- A single draw `let x ← κ`: the trace is the value drawn, and the readout is that value. -/
protected lemma sample (κ : Kernel γ α) : HasTrace (⇑κ) κ Prod.snd :=
  ⟨measurable_snd, fun _ ↦ Measure.map_id⟩

/-- Any subprogram already known to be Markov can be treated as a single atomic draw. This is the
knob controlling how finely a program is traced: stop here and the subprogram's own `←`s stay
hidden inside one coordinate. -/
protected lemma of_isMarkov (prog : γ → Measure α) [IsMarkov prog] :
    HasTrace prog (IsMarkov.toKernel prog) Prod.snd :=
  ⟨measurable_snd, fun _ ↦ Measure.map_id⟩


/-- The leaf rule as `rdo_trace` uses it: a Markov subprogram is one atomic draw, with the
`IsMarkov` proof carried in the kernel so that `IsMarkovKernel` stays available downstream. -/
protected lemma leaf (prog : γ → Measure α) (h : IsMarkov prog) :
    HasTrace prog (markovKernel prog h) Prod.snd :=
  ⟨measurable_snd, fun _ ↦ Measure.map_id⟩

/-- A value marked with `record`: a coordinate of the trace holding a deterministic function of
the parameter — which, inside a program, means of everything drawn before it. The program itself is
unchanged (`RDo.record_bind`); the trace gains a coordinate. -/
protected lemma «record» {f : γ → α} (hf : Measurable f) :
    HasTrace (fun c ↦ RDo.record (f c)) (Kernel.deterministic f hf) Prod.snd :=
  ⟨measurable_snd, fun c ↦ by
    rw [Kernel.deterministic_apply]
    exact Measure.map_id⟩

/-- `return e` draws nothing: its trace space is `PUnit`. -/
protected lemma pure {g : γ → β} (hg : Measurable g) :
    HasTrace (fun c ↦ mPure (g c)) (Kernel.const γ (Measure.dirac PUnit.unit))
      (fun p : γ × PUnit ↦ g p.1) :=
  ⟨hg.comp measurable_fst, fun c ↦ by
    rw [Kernel.const_apply]
    change (Measure.dirac PUnit.unit).map (fun _ : PUnit ↦ g c) = mPure (g c)
    rw [Measure.map_dirac' measurable_const]
    rfl⟩

/-- A program that does not look at its parameter. -/
protected lemma const {μ : Measure β} {Q : Measure Ω} {o : Ω → β} (ho : Measurable o)
    (h : Q.map o = μ) : HasTrace (fun _ : γ ↦ μ) (Kernel.const γ Q) (fun p ↦ o p.2) :=
  ⟨ho.comp measurable_snd, fun _ ↦ h⟩

/-- Weakening: a subprogram that does not read the trace drawn so far, seen as a program over the
enlarged parameter `γ × Ω`. Presenting its trace kernel as `Kernel.prodMkRight` is what makes
`indepFun_snd_compProd_prodMkRight` applicable afterwards. -/
protected lemma prodMkRight (Ω₀ : Type*) [MeasurableSpace Ω₀] {prog : γ → Measure α}
    {R : Kernel γ Ω'} {o : γ × Ω' → α} (h : HasTrace prog R o) :
    HasTrace (fun p : γ × Ω₀ ↦ prog p.1) (Kernel.prodMkRight Ω₀ R)
      (fun q : (γ × Ω₀) × Ω' ↦ o (q.1.1, q.2)) :=
  ⟨h.measurable_out.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd),
    fun p ↦ h.map_eq p.1⟩

/-- Reparametrisation: a traced program read through a measurable change of parameters. -/
protected lemma comp (h : HasTrace prog P out) {g : δ → γ} (hg : Measurable g) :
    HasTrace (fun d ↦ prog (g d)) (P.comap g hg) (fun p ↦ out (g p.1, p.2)) :=
  ⟨h.measurable_out.comp ((hg.comp measurable_fst).prodMk measurable_snd), fun d ↦ by
    rw [Kernel.comap_apply]; exact h.map_eq (g d)⟩

/-- `let x ← p; return f x`: a deterministic tail draws nothing, so it only changes the readout. -/
protected lemma bindPure {prog : γ → Measure α} {P : Kernel γ Ω} {out : γ × Ω → α}
    (h : HasTrace prog P out) {f : γ × α → β} (hf : Measurable f) :
    HasTrace (fun c ↦ prog c >>=ₘ fun a ↦ mPure (f (c, a))) P (fun p ↦ f (p.1, out p)) where
  measurable_out := hf.comp (measurable_fst.prodMk h.measurable_out)
  map_eq c := by
    have hf' : Measurable fun a ↦ f (c, a) := hf.comp (measurable_const.prodMk measurable_id)
    have hout : Measurable fun ω ↦ out (c, ω) := h.measurable_out.comp measurable_prodMk_left
    change (P c).map (fun ω ↦ f (c, out (c, ω)))
      = (prog c).bind fun a ↦ Measure.dirac (f (c, a))
    rw [Measure.bind_dirac_eq_map _ hf', ← h.map_eq c, Measure.map_map hf' hout]
    rfl

/-- `if p c then … else …`. The two branches have to draw in the same space; the trace kernel is
then the piecewise kernel and the readout branches on the same condition. Branches drawing in
different spaces are handled by tracing each into the sum of the two spaces first. -/
protected lemma ite {p : γ → Prop} [DecidablePred p] (hp : MeasurableSet {c | p c})
    {prog₁ prog₂ : γ → Measure β} {P₁ P₂ : Kernel γ Ω} {out₁ out₂ : γ × Ω → β}
    (h₁ : HasTrace prog₁ P₁ out₁) (h₂ : HasTrace prog₂ P₂ out₂) :
    HasTrace (fun c ↦ if p c then prog₁ c else prog₂ c) (Kernel.piecewise hp P₁ P₂)
      (fun q : γ × Ω ↦ if p q.1 then out₁ q else out₂ q) where
  measurable_out := Measurable.ite (measurable_fst hp) h₁.measurable_out h₂.measurable_out
  map_eq c := by
    rw [Kernel.piecewise_apply]
    by_cases hc : p c <;> simp only [Set.mem_ofPred_eq, hc, ite_true, ite_false]
    · exact h₁.map_eq c
    · exact h₂.map_eq c

/-- **The bind rule.** The trace of `let x ← p; q x` is the composition-product of the trace of `p`
with the trace of `q`, the latter being allowed to depend on the whole trace of `p` and not only
on the value `x` that `p` returned.

This is the rule that turns the sequential structure of an `rdo` program into the `⊗ₖ` structure of
its trace kernel, and hence into conditional laws: see `hasCondDistrib_snd_compProd`. -/
protected lemma bind {prog : γ → Measure α} {P : Kernel γ Ω} [IsSFiniteKernel P] {out : γ × Ω → α}
    {cont : γ × α → Measure β} (hcont : Measurable cont)
    {Q : Kernel (γ × Ω) Ω'} [IsSFiniteKernel Q] {out' : (γ × Ω) × Ω' → β}
    (h : HasTrace prog P out) (h' : HasTrace (fun p ↦ cont (p.1, out p)) Q out') :
    HasTrace (fun c ↦ prog c >>=ₘ fun a ↦ cont (c, a)) (P ⊗ₖ Q)
      (fun p : γ × (Ω × Ω') ↦ out' ((p.1, p.2.1), p.2.2)) where
  measurable_out :=
    h'.measurable_out.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  map_eq c := by
    have hg : Measurable fun w : Ω × Ω' ↦ out' ((c, w.1), w.2) :=
      h'.measurable_out.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hcont' : Measurable fun a ↦ cont (c, a) :=
      hcont.comp (measurable_const.prodMk measurable_id)
    have hout : Measurable fun ω ↦ out (c, ω) := h.measurable_out.comp measurable_prodMk_left
    rw [Kernel.compProd_apply_eq_compProd_sectR, map_compProd _ _ hg]
    change (Measure.bind (P c) fun ω ↦ (Kernel.sectR Q c ω).map fun ω' ↦ out' ((c, ω), ω')) = _
    rw [show (fun ω ↦ (Kernel.sectR Q c ω).map fun ω' ↦ out' ((c, ω), ω'))
        = fun ω ↦ cont (c, out (c, ω)) from funext fun ω ↦ h'.map_eq (c, ω), ← h.map_eq c]
    exact (bind_map (P c) hout hcont').symm

end HasTrace


/-! ## Reading the random variables off the trace

The trace kernel of a program is a right-nested `⊗ₖ`, one factor per `←`. This section provides
the single rule needed to exploit that: *peeling* a `⊗ₖ` off a law or a conditional law splits it
into the law of the next draw given the history, and a conditional law for everything after it.
Applying it once per `←` walks down the program, and produces, for the `k`-th draw, its
conditional distribution given the first `k-1` draws — read straight off the program text.

When the peeled kernel does not depend on the history (`Kernel.prodMkRight`, or a constant),
that conditional law is an unconditional law together with an independence statement:
`hasLaw_of_const` and `indepFun_of_const`.
-/

section Peel

variable {Ω α β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace δ] {P : Measure Ω} {W : Ω → α × β}

/-- The first half of a random variable whose law is a composition-product. -/
lemma _root_.ProbabilityTheory.HasLaw.compProd_fst {ν : Measure α} [SFinite ν]
    {η : Kernel α β} [IsMarkovKernel η] (h : HasLaw W (ν ⊗ₘ η) P) :
    HasLaw (fun ω ↦ (W ω).1) ν P where
  aemeasurable := measurable_fst.comp_aemeasurable h.aemeasurable
  map_eq := by
    rw [show (fun ω ↦ (W ω).1) = Prod.fst ∘ W from rfl,
      ← AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable h.aemeasurable, h.map_eq,
      ← Measure.fst, Measure.fst_compProd]

/-- **The peeling rule, unconditional form.** If the joint law of a pair is `ν ⊗ₘ η`, then the
second component has conditional distribution `η` given the first. -/
lemma _root_.ProbabilityTheory.HasLaw.compProd_snd {ν : Measure α} [SFinite ν]
    {η : Kernel α β} [IsMarkovKernel η] (h : HasLaw W (ν ⊗ₘ η) P) :
    HasCondDistrib (fun ω ↦ (W ω).2) (fun ω ↦ (W ω).1) η P := by
  refine ⟨h.aemeasurable, ?_⟩
  rw [h.compProd_fst.map_eq]
  exact h.map_eq

variable {H : Ω → δ} {κ : Kernel δ α} {η : Kernel (δ × α) β} {W : Ω → α × β}

/-- The first half of a random variable whose conditional law is a composition-product. -/
lemma _root_.ProbabilityTheory.HasCondDistrib.compProd_fst [SFinite P] [IsSFiniteKernel κ]
    [IsMarkovKernel η] (h : HasCondDistrib W H (κ ⊗ₖ η) P) :
    HasCondDistrib (fun ω ↦ (W ω).1) H κ P := by
  have := h.fst
  rwa [Kernel.fst_compProd] at this

/-- **The peeling rule.** If, given the history `H`, the rest of the trace has conditional law
`κ ⊗ₖ η`, then the next draw has conditional law `κ` given `H`, and everything after it has
conditional law `η` given `H` *and* that draw. Iterating this walks down an `rdo` program one
`←` at a time. -/
lemma _root_.ProbabilityTheory.HasCondDistrib.compProd_snd [SFinite P] [IsSFiniteKernel κ]
    [IsMarkovKernel η] (h : HasCondDistrib W H (κ ⊗ₖ η) P) :
    HasCondDistrib (fun ω ↦ (W ω).2) (fun ω ↦ (H ω, (W ω).1)) η P :=
  HasCondDistrib.of_compProd (Y := fun ω ↦ (W ω).1) (Z := fun ω ↦ (W ω).2) h

end Peel

section Coordinates

variable {γ Ω Ω' Ω'' : Type*} [MeasurableSpace γ] [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace Ω'']

/-- A section of a composition-product of kernels is the composition-product of the sections.
This is what lets the peeling rule be applied again to the tail of a trace. -/
lemma _root_.ProbabilityTheory.Kernel.sectR_compProd (κ : Kernel (γ × Ω) Ω')
    (η : Kernel ((γ × Ω) × Ω') Ω'') [IsSFiniteKernel κ] [IsSFiniteKernel η] (c : γ) :
    Kernel.sectR (κ ⊗ₖ η) c
      = Kernel.sectR κ c ⊗ₖ η.comap (fun p : Ω × Ω' ↦ ((c, p.1), p.2)) (by fun_prop) := by
  ext ω s hs
  rw [Kernel.sectR_apply, Kernel.compProd_apply hs, Kernel.compProd_apply hs]
  simp [Kernel.comap_apply]

/-- The whole trace of a program whose last construct is a `←`, as a random variable on its own
space: its law is a composition-product, ready for the peeling rule. This is the entry point of
the recursion. -/
lemma hasLaw_id_compProd (P : Kernel γ Ω) (Q : Kernel (γ × Ω) Ω') [IsSFiniteKernel P]
    [IsSFiniteKernel Q] (c : γ) :
    HasLaw (id : Ω × Ω' → Ω × Ω') (P c ⊗ₘ Kernel.sectR Q c) ((P ⊗ₖ Q) c) :=
  ⟨measurable_id.aemeasurable, by
    rw [Measure.map_id, Kernel.compProd_apply_eq_compProd_sectR]⟩

/-- A draw that does not read the history is drawn from a constant kernel. Combined with
`HasCondDistrib.hasLaw_of_const` and `HasCondDistrib.indepFun_of_const`, this turns a conditional
law into a law plus an independence statement. -/
@[simp]
lemma _root_.ProbabilityTheory.Kernel.sectR_prodMkRight_eq_const {R : Kernel γ Ω'} (c : γ) :
    Kernel.sectR (Kernel.prodMkRight Ω R) c = Kernel.const Ω (R c) :=
  Kernel.ext fun _ ↦ by
    rw [Kernel.sectR_apply, Kernel.prodMkRight_apply, Kernel.const_apply]

variable (P : Kernel γ Ω) (Q : Kernel (γ × Ω) Ω') (c : γ)

@[simp]
lemma map_fst_compProd [IsSFiniteKernel P] [IsMarkovKernel Q] :
    ((P ⊗ₖ Q) c).map Prod.fst = P c := by
  rw [← Kernel.fst_apply, Kernel.fst_compProd]

/-- The draws made before the last `←` have the law given by the earlier factor. -/
lemma hasLaw_fst_compProd [IsSFiniteKernel P] [IsMarkovKernel Q] :
    HasLaw (Prod.fst : Ω × Ω' → Ω) (P c) ((P ⊗ₖ Q) c) :=
  ⟨measurable_fst.aemeasurable, map_fst_compProd P Q c⟩

/-- The last draw of a program has conditional distribution `Q` given all the draws before it. -/
lemma hasCondDistrib_snd_compProd [IsSFiniteKernel P] [IsMarkovKernel Q] :
    HasCondDistrib Prod.snd Prod.fst (Kernel.sectR Q c) ((P ⊗ₖ Q) c) :=
  (hasLaw_id_compProd P Q c).compProd_snd

/-- The same statement in the `Kernel.comap` form that the peeling chain keeps: `Kernel.sectR Q c`
*is* `Q.comap (fun ω ↦ (c, ω))`, and every later step produces a `comap` too. -/
lemma hasCondDistrib_snd_compProd_comap [IsSFiniteKernel P] [IsMarkovKernel Q] :
    HasCondDistrib Prod.snd Prod.fst
      (Q.comap (fun ω ↦ (c, ω)) (measurable_const.prodMk measurable_id)) ((P ⊗ₖ Q) c) :=
  hasCondDistrib_snd_compProd P Q c

/-- When a draw does not read the earlier ones, it is independent of them. -/
lemma indepFun_snd_compProd_prodMkRight [IsMarkovKernel P] {R : Kernel γ Ω'} [IsMarkovKernel R] :
    IndepFun (Prod.fst : Ω × Ω' → Ω) Prod.snd ((P ⊗ₖ Kernel.prodMkRight Ω R) c) := by
  have h := hasCondDistrib_snd_compProd P (Kernel.prodMkRight Ω R) c
  rw [Kernel.sectR_prodMkRight_eq_const] at h
  exact h.indepFun_of_const

/-- When a draw does not read the earlier ones, its law is the kernel it was drawn from. -/
lemma hasLaw_snd_compProd_prodMkRight [IsMarkovKernel P] {R : Kernel γ Ω'} [IsMarkovKernel R] :
    HasLaw (Prod.snd : Ω × Ω' → Ω') (R c) ((P ⊗ₖ Kernel.prodMkRight Ω R) c) := by
  have h := hasCondDistrib_snd_compProd P (Kernel.prodMkRight Ω R) c
  rw [Kernel.sectR_prodMkRight_eq_const] at h
  exact h.hasLaw_of_const

end Coordinates

/-! ## Peeling through a reparametrisation

After the first step the tail kernel of the peeling chain is a `Kernel.comap`, and stays one. These
are the lemmas the `rdo_peel` tactic iterates.
-/

section Peel'

variable {Γ Ωk Ωr Ω δ : Type*} [MeasurableSpace Γ] [MeasurableSpace Ωk] [MeasurableSpace Ωr]
  [MeasurableSpace Ω] [MeasurableSpace δ]

/-- Comap distributes over the composition-product. -/
lemma _root_.ProbabilityTheory.Kernel.comap_compProd (κ : Kernel Γ Ωk) (η : Kernel (Γ × Ωk) Ωr)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {ι : δ → Γ} (hι : Measurable ι) :
    (κ ⊗ₖ η).comap ι hι = κ.comap ι hι ⊗ₖ
      η.comap (fun p : δ × Ωk ↦ (ι p.1, p.2)) ((hι.comp measurable_fst).prodMk measurable_snd) := by
  ext d s hs
  rw [Kernel.comap_apply, Kernel.compProd_apply hs, Kernel.compProd_apply hs]
  simp [Kernel.comap_apply]

variable {P : Measure Ω} {H : Ω → δ} {W : Ω → Ωk × Ωr} {κ : Kernel Γ Ωk} {η : Kernel (Γ × Ωk) Ωr}
  {ι : δ → Γ} {hι : Measurable ι} [SFinite P] [IsSFiniteKernel κ] [IsMarkovKernel η]

/-- Peel the next draw off a reparametrised tail. -/
lemma _root_.ProbabilityTheory.HasCondDistrib.comap_compProd_fst
    (h : HasCondDistrib W H ((κ ⊗ₖ η).comap ι hι) P) :
    HasCondDistrib (fun ω ↦ (W ω).1) H (κ.comap ι hι) P := by
  rw [Kernel.comap_compProd] at h
  exact h.compProd_fst

/-- ... and keep the rest of the tail, still a `comap`, for the next step. -/
lemma _root_.ProbabilityTheory.HasCondDistrib.comap_compProd_snd
    (h : HasCondDistrib W H ((κ ⊗ₖ η).comap ι hι) P) :
    HasCondDistrib (fun ω ↦ (W ω).2) (fun ω ↦ (H ω, (W ω).1))
      (η.comap (fun p : δ × Ωk ↦ (ι p.1, p.2))
        ((hι.comp measurable_fst).prodMk measurable_snd)) P := by
  rw [Kernel.comap_compProd] at h
  exact h.compProd_snd

end Peel'

end RDo
