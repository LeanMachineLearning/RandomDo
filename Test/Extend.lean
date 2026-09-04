module

public import Test.Common
public import Mathlib.Probability.Independence.InfinitePi

set_option linter.style.header false

/-!
# The `extend_space` tactic

The first sections pin down what `extend_space` produces: the context after the extension, what
is transported and what is left about the old space, when the `transfer` obligation is closed
automatically and when it is left, and what `extend_space!` clears. Then come the explicit form
`extend_space_map`, a draw with a conditional law, an i.i.d. sequence, and the errors the tactic
reports.

Throughout, `Ω` lives in `Type u` and `E` in `Type`: the tactic lifts the product to the universe
of `Ω`.
-/

open MeasureTheory ProbabilityTheory RDo

@[expose] public section

noncomputable section

namespace Test.Extend

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

include μ

/-! ## The context after `extend_space` -/

/-- The names are kept: `Ω`, `P`, `X`, `A` and `s` now live on the extended space, related to the
old `Ω₀`, `P₀`, `X₀`, … by the map `f` and the defining equations. Hypotheses about them are
transported, and `Z` is independent of the tuple of the random variables. The goal reads as
before, and its `transfer` obligation is discharged. -/
example (X : Ω → ℝ) (A : ℕ → Ω → ℝ) (s : Set Ω) (hX : Measurable X) (hA : ∀ n, Measurable (A n))
    (hs : MeasurableSet s) (ν : Measure ℝ) (c : ENNReal) (h1 : P.map X = ν)
    (h2 : ∀ n, P.map (A n) = ν) (h3 : P s = c) :
    P.map X = ν ∧ (∀ n, P.map (A n) = ν) ∧ P s = c := by
  extend_space μ with Z hZ hind f hf
  guard_hyp hf : MeasurePreserving f P P₀
  guard_hyp hZ : HasLaw Z μ P
  guard_hyp hind : IndepFun (fun ω ↦ (X ω, fun n ↦ A n ω)) Z P
  guard_hyp hX_def : ∀ ω, X₀ (f ω) = X ω
  guard_hyp hA_def : ∀ n ω, A₀ n (f ω) = A n ω
  guard_hyp hs_def : f ⁻¹' s₀ = s
  guard_hyp hX : Measurable X
  guard_hyp hA : ∀ n, Measurable (A n)
  guard_hyp hs : MeasurableSet s
  guard_hyp h1 : P.map X = ν
  guard_hyp h2 : ∀ n, P.map (A n) = ν
  guard_hyp h3 : P s = c
  guard_hyp h1₀ : P₀.map X₀ = ν
  guard_target =ₐ P.map X = ν ∧ (∀ n, P.map (A n) = ν) ∧ P s = c
  exact ⟨h1, h2, h3⟩

/-- Without `with`, the names are `Z hZ hind f hf`. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    P.map X = ν := by
  extend_space μ
  guard_hyp hZ : HasLaw Z μ P
  guard_hyp hind : IndepFun X Z P
  guard_hyp hf : MeasurePreserving f P P₀
  exact hXν.map_eq

/-- A hypothesis nothing transports, here about `Measure.restrict`, stays about the old space,
under its `₀` name. -/
example (s : Set Ω) (hs : MeasurableSet s) (h : P.restrict s Set.univ = 1) :
    P s = 1 := by
  extend_space μ
  guard_hyp h₀ : P₀.restrict s₀ Set.univ = 1
  guard_hyp hs : MeasurableSet s
  rw [← hs_def, hf.measure_preimage hs₀.nullMeasurableSet, ← Measure.restrict_apply_univ]
  exact h₀

/-- A statement `transfer` has no lemma for, here `Measure.restrict`, leaves the obligation. It is
stated for an arbitrary measure-preserving map, with the original goal as its conclusion. -/
example (s : Set Ω) : P.restrict s Set.univ = P s := by
  extend_space μ
  case extended =>
    guard_target =ₐ P.restrict s Set.univ = P s
    exact Measure.restrict_apply_univ _
  case transfer =>
    guard_target =ₐ ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (f : Ω' → Ω), MeasurePreserving f P' P →
      P'.restrict (f ⁻¹' s) Set.univ = P' (f ⁻¹' s) → P.restrict s Set.univ = P s
    intro Ω' _ P' _ f hf h
    exact Measure.restrict_apply_univ _

/-- The goal depends on the measurability proof `hX`: it is generalized along with the goal, and
comes back about the new `X`. The goal mentions no measure, so `using P` says which space to
extend, and `transfer` cannot rewrite under a binder the goal depends on, so the obligation is
left. -/
example (X : Ω → ℝ) (hX : Measurable X) (κ : Kernel ℝ E) [IsMarkovKernel κ] :
    IsMarkovKernel (κ.comap X hX) := by
  extend_space μ using P
  case extended =>
    guard_hyp hX : Measurable X
    guard_hyp hX₀ : Measurable X₀
    guard_target =ₐ IsMarkovKernel (κ.comap X hX)
    infer_instance
  case transfer =>
    intro Ω' _ P' _ f hf h hX
    infer_instance

/-! ## `extend_space!` -/

/-- The old space is cleared: nothing mentions `Ω₀`, `f` or the defining equations any more. The
space is a binder of the statement here rather than a `variable`: Lean does not let a tactic clear
a `variable`, so those would stay. -/
example {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    P.map X = ν := by
  extend_space! μ
  fail_if_success guard_hyp Ω₀ : Type u
  fail_if_success guard_hyp f : Ω → Ω₀
  fail_if_success guard_hyp hX_def : ∀ ω, X₀ (f ω) = X ω
  guard_hyp hZ : HasLaw Z μ P
  guard_hyp hind : IndepFun X Z P
  guard_hyp hXν : HasLaw X ν P
  exact hXν.map_eq

/-! ## Transported hypotheses

Laws, independence, conditional laws, events, integrals and almost-everywhere statements are
transported by the `@[transfer]` lemmas, measurability and the like by the `@[transfer_forward]`
lemmas. -/

/-- Independence. -/
example (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IndepFun X Y P := by
  extend_space μ
  guard_hyp hXY : IndepFun X Y P
  guard_hyp hind : IndepFun (fun ω ↦ (X ω, Y ω)) Z P
  exact hXY

/-- A hypothesis introduced by `have`, whose type may still carry metavariables, is transported
like any other. -/
example (X : Ω → ℝ) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    P.map X = ν := by
  have hXae := hXν.aemeasurable
  extend_space μ
  guard_hyp hXae : AEMeasurable X P
  guard_hyp hXae₀ : AEMeasurable X₀ P₀
  exact hXν.map_eq

/-- A conditional law. -/
example (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (κ : Kernel ℝ ℝ)
    (hXY : HasCondDistrib Y X κ P) :
    HasCondDistrib Y X κ P := by
  extend_space μ
  exact hXY

/-- An event given by a set-builder expression, and its real-valued measure. -/
example (X : Ω → ℝ) (hX : Measurable X) (h : P {ω | 0 < X ω} = 1 / 2)
    (h' : P.real {ω | 0 < X ω} = 1 / 2) :
    P {ω | 0 < X ω} = 1 / 2 ∧ P.real {ω | 0 < X ω} = 1 / 2 := by
  extend_space μ
  guard_hyp h : P {ω | 0 < X ω} = 1 / 2
  exact ⟨h, h'⟩

/-- An integral, with an integrability and an almost-everywhere hypothesis. -/
example (X : Ω → ℝ) (hX : Measurable X) (hint : Integrable X P) (h : ∀ᵐ ω ∂P, 0 ≤ X ω) :
    0 ≤ ∫ ω, X ω ∂P ∧ Integrable X P := by
  extend_space μ
  guard_hyp hint : Integrable X P
  guard_hyp h : ∀ᵐ ω ∂P, 0 ≤ X ω
  exact ⟨integral_nonneg_of_ae h, hint⟩

/-- A Lebesgue integral. -/
example (X : Ω → ℝ) (hX : Measurable X) (c : ENNReal) (h : ∫⁻ ω, ‖X ω‖ₑ ∂P = c) :
    ∫⁻ ω, ‖X ω‖ₑ ∂P = c := by
  extend_space μ
  exact h

/-- An almost-everywhere equality. -/
example (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (h : X =ᵐ[P] Y) : X =ᵐ[P] Y := by
  extend_space μ
  exact h

/-! ## Using the new draw

A statement that does not mention the space has a trivial `transfer` obligation: this is the
existential form of the tactic. -/

/-- Any random variable has an independent companion with any prescribed law, on a larger space:
after the extension, that space is `Ω` itself. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (X' : Ω' → ℝ) (Z : Ω' → E), HasLaw X' ν P' ∧ HasLaw Z μ P' ∧ IndepFun X' Z P' := by
  extend_space μ using P
  exact ⟨Ω, inferInstance, P, inferInstance, X, Z, hXν, hZ, hind⟩

/-- An i.i.d. sequence, by extending with `Measure.infinitePi`: `Z ω : ℕ → E`. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (X' : Ω' → ℝ) (Z : ℕ → Ω' → E), HasLaw X' ν P' ∧ (∀ n, HasLaw (Z n) μ P')
        ∧ iIndepFun Z P' ∧ IndepFun X' (fun ω n ↦ Z n ω) P' := by
  extend_space Measure.infinitePi (fun _ : ℕ ↦ μ) using P
  have hZn (n : ℕ) : HasLaw (fun ω ↦ Z ω n) μ P :=
    (measurePreserving_eval_infinitePi _ n).hasLaw.comp hZ
  exact ⟨Ω, inferInstance, P, inferInstance, X, fun n ω ↦ Z ω n, hXν, hZn,
    (iIndepFun_iff_hasLaw_Pi_infinitePi hZn hZ.aemeasurable).2 hZ, hind⟩

/-! ## A draw with a conditional law -/

/-- `extend_space (κ.comap X hX)`: the draw has conditional law `κ` given `X`. -/
example (X : Ω → ℝ) (hX : Measurable X) (κ : Kernel ℝ E) [IsMarkovKernel κ] (ν : Measure ℝ)
    (hXν : HasLaw X ν P) :
    P.map X = ν := by
  extend_space (κ.comap X hX) with Z hZ
  guard_hyp hZ : HasCondDistrib Z X κ P
  exact hXν.map_eq

/-- `extend_space κ` for a kernel on `Ω` itself: the kernel is on the old space, now `κ₀`, and
the conditional law is given the map `f`. -/
example (X : Ω → ℝ) (hX : Measurable X) (κ : Kernel Ω E) [IsMarkovKernel κ] (ν : Measure ℝ)
    (hXν : HasLaw X ν P) :
    P.map X = ν := by
  extend_space κ with Z hZ f hf
  guard_hyp hZ : HasCondDistrib Z f κ₀ P
  exact hXν.map_eq

/-! ## The explicit form, `extend_space_map` -/

/-- Nothing is renamed: the goal is restated on `Ω'`, with `X ∘ f` for `X` and `f ⁻¹' s` for `s`,
and the hypotheses stay about the old space. With the measurability hypotheses around, the
`transfer` obligation is discharged. -/
example (X : Ω → ℝ) (A : ℕ → Ω → ℝ) (s : Set Ω) (hX : Measurable X) (hA : ∀ n, Measurable (A n))
    (hs : MeasurableSet s) (ν : Measure ℝ) (c : ENNReal) (h1 : P.map X = ν)
    (h2 : ∀ n, P.map (A n) = ν) (h3 : P s = c) :
    P.map X = ν ∧ (∀ n, P.map (A n) = ν) ∧ P s = c := by
  extend_space_map μ with Ω' P' f hf Z hZ hind
  guard_hyp hf : MeasurePreserving f P' P
  guard_hyp hZ : HasLaw Z μ P'
  guard_hyp hind : IndepFun f Z P'
  guard_hyp h1 : P.map X = ν
  guard_target =ₐ P'.map (fun ω ↦ X (f ω)) = ν ∧ (∀ n, P'.map (fun ω ↦ A n (f ω)) = ν)
    ∧ P' (f ⁻¹' s) = c
  transfer hf at h1 h2 h3
  guard_hyp h1 : P'.map (fun ω ↦ X (f ω)) = ν
  exact ⟨h1, h2, h3⟩

/-- Without `with`, the names are `Ω' P' f hf Z hZ hind`. A hypothesis is pulled back by
`transfer hf at h`, or by hand: `hXν.comp hf.hasLaw` for a law, `hind.comp hX measurable_id` for
independence. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    P.map X = ν := by
  extend_space_map μ
  have hXν' : HasLaw (fun ω ↦ X (f ω)) ν P' := hXν.comp hf.hasLaw
  have hind' : IndepFun (fun ω ↦ X (f ω)) Z P' := hind.comp hX measurable_id
  transfer hf at hX
  guard_hyp hX : Measurable fun ω ↦ X (f ω)
  exact hXν'.map_eq

/-- The goal depends on `hX`: it is generalized and reintroduced as `hX'`, about `X ∘ f`, while
`hX` itself stays. -/
example (X : Ω → ℝ) (hX : Measurable X) (κ : Kernel ℝ E) [IsMarkovKernel κ] :
    IsMarkovKernel (κ.comap X hX) := by
  extend_space_map μ using P
  case extended =>
    guard_hyp hX : Measurable X
    guard_hyp hX' : Measurable fun ω ↦ X (f ω)
    guard_target =ₐ IsMarkovKernel (κ.comap (fun ω ↦ X (f ω)) hX')
    infer_instance
  case transfer =>
    intro Ω' _ P' _ f hf h hX
    infer_instance

/-- A draw with a conditional law: `HasCondDistrib.comp_right` reads `hZ` given `X ∘ f`. -/
example (X : Ω → ℝ) (hX : Measurable X) (κ : Kernel ℝ E) [IsMarkovKernel κ] (ν : Measure ℝ)
    (hXν : HasLaw X ν P) :
    P.map X = ν := by
  extend_space_map (κ.comap X hX) with Ω' P' f hf Z hZ
  guard_hyp hZ : HasCondDistrib Z f (κ.comap X hX) P'
  have hZ' : HasCondDistrib Z (fun ω ↦ X (f ω)) κ P' := hZ.comp_right
  transfer hf at hXν
  exact hXν.map_eq

/-! ## Universes -/

/-- `Ω` and `E` in the same universe. -/
example {E' : Type u} [MeasurableSpace E'] (μ' : Measure E') [IsProbabilityMeasure μ']
    (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) : P.map X = ν := by
  extend_space μ'
  exact hXν.map_eq

/-! ## Errors -/

/--
error: extend_space: the goal mentions no measure on a local space; name one with `using`
-/
#guard_msgs in
example (X : Ω → ℝ) : X = X := by
  extend_space μ

/--
error: extend_space: the goal mentions several measures, [P, Q]; choose one with `using`
-/
#guard_msgs in
example (Q : Measure Ω) (X : Ω → ℝ) : P.map X = Q.map X := by
  extend_space μ

/--
error: extend_space: E' lives in universe u + 1 and Ω in universe u,
so the product Ω × E' does not live in the universe of Ω: lift E' with `ULift`
-/
#guard_msgs in
example {E' : Type (u + 1)} [MeasurableSpace E'] (μ' : Measure E') [IsProbabilityMeasure μ']
    (X : Ω → ℝ) : P.map X = P.map X := by
  extend_space μ'

end Test.Extend

end

end
