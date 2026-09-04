/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.Probability.Extend
public import Mathlib.Probability.Independence.InfinitePi

set_option linter.style.header false

/-!
# Tests and examples for `extend_space` and `transfer`

The first section pins down what `extend_space` produces: which hypotheses appear, what the goal
becomes, when the `transfer` obligation is closed automatically and when it is left, and how
hypotheses the goal depends on are handled. The next ones show `transfer` at work on laws,
independence, conditional laws, events, integrals and almost-everywhere statements, both on the
obligation and to pull hypotheses back to the new space; then a draw with a conditional law, an
i.i.d. sequence, and the errors the tactics report.

Throughout, `Ω` lives in `Type u` and `E` in `Type`: the tactic lifts the product to the universe
of `Ω`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RDo

noncomputable section

namespace RDo.Example.Extend

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

include μ

/-! ## The shape of the goals -/

/-- Random variables, families of random variables and events are transported along `f`, and the
measure becomes `P'`. With the measurability hypotheses around, the `transfer` obligation is
discharged by `extend_space` itself, and only the extended goal is left. -/
example (X : Ω → ℝ) (A : ℕ → Ω → ℝ) (s : Set Ω) (hX : Measurable X) (hA : ∀ n, Measurable (A n))
    (hs : MeasurableSet s) :
    P.map X = P.map X ∧ (∀ n, P.map (A n) = P.map (A n)) ∧ P s = P s := by
  extend_space μ with Ω' P' f hf Z hZ hind
  guard_hyp hf : MeasurePreserving f P' P
  guard_hyp hZ : HasLaw Z μ P'
  guard_hyp hind : IndepFun f Z P'
  guard_target =ₐ P'.map (fun ω ↦ X (f ω)) = P'.map (fun ω ↦ X (f ω))
    ∧ (∀ n, P'.map (fun ω ↦ A n (f ω)) = P'.map (fun ω ↦ A n (f ω)))
    ∧ P' (f ⁻¹' s) = P' (f ⁻¹' s)
  exact ⟨rfl, fun _ ↦ rfl, rfl⟩

/-- A statement `transfer` has no lemma for, here `IsProbabilityMeasure P`: the obligation is left.
It is stated for an arbitrary measure-preserving map, with the original goal as its conclusion.
Without `with`, the names are `Ω' P' f hf Z hZ hind`. -/
example : IsProbabilityMeasure P := by
  extend_space μ
  case extended =>
    guard_hyp hf : MeasurePreserving f P' P
    guard_hyp hZ : HasLaw Z μ P'
    guard_hyp hind : IndepFun f Z P'
    infer_instance
  case transfer =>
    guard_target =ₐ ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (f : Ω' → Ω), MeasurePreserving f P' P →
      IsProbabilityMeasure P' → IsProbabilityMeasure P
    intro Ω' _ P' _ f hf h
    infer_instance

/-- An operation `transfer` has no lemma for, here `Measure.restrict`: the obligation is left. -/
example (s : Set Ω) : P.restrict s Set.univ = P s := by
  extend_space μ
  case extended =>
    guard_target =ₐ P'.restrict (f ⁻¹' s) Set.univ = P' (f ⁻¹' s)
    exact Measure.restrict_apply_univ _
  case transfer =>
    intro Ω' _ P' _ f hf h
    exact Measure.restrict_apply_univ _

/-- The goal depends on the measurability proof `hX`: it is generalized and reintroduced as `hX'`,
now about `X ∘ f`, while `hX` itself stays. The goal mentions no measure, so `using P` says which
space to extend. `transfer` cannot rewrite under a binder the goal depends on, so the obligation
is left. -/
example (X : Ω → ℝ) (hX : Measurable X) (κ : Kernel ℝ E) [IsMarkovKernel κ] :
    IsMarkovKernel (κ.comap X hX) := by
  extend_space μ using P with Ω' P' f hf Z hZ hind
  case extended =>
    guard_hyp hX : Measurable X
    guard_hyp hX' : Measurable fun ω ↦ X (f ω)
    guard_target =ₐ IsMarkovKernel (κ.comap (fun ω ↦ X (f ω)) hX')
    infer_instance
  case transfer =>
    intro Ω' _ P' _ f hf h hX
    infer_instance

/-! ## Transferring statements

`extend_space` closes the `transfer` obligation, and `transfer hf at h` pulls a hypothesis about
the old space back to the new one. Both rewrite with the `@[transfer]` lemmas, whose side
conditions are measurability statements found by `assumption`, `fun_prop` or `measurability`. -/

/-- A law. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    P.map X = ν := by
  extend_space μ with Ω' P' f hf Z hZ hind
  transfer hf at hXν
  guard_hyp hXν : HasLaw (fun ω ↦ X (f ω)) ν P'
  exact hXν.map_eq

/-- The same with `HasLaw` as the goal, and the hypothesis pulled back by hand. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    HasLaw X ν P := by
  extend_space μ
  exact hXν.comp hf.hasLaw

/-- Independence. -/
example (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IndepFun X Y P := by
  extend_space μ
  transfer hf at hXY
  guard_hyp hXY : IndepFun (fun ω ↦ X (f ω)) (fun ω ↦ Y (f ω)) P'
  exact hXY

/-- A conditional law. -/
example (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (κ : Kernel ℝ ℝ)
    (hXY : HasCondDistrib Y X κ P) :
    HasCondDistrib Y X κ P := by
  extend_space μ
  transfer hf at hXY
  exact hXY

/-- An event, given by a set-builder expression: `measurability` proves it measurable. -/
example (X : Ω → ℝ) (hX : Measurable X) (h : P {ω | 0 < X ω} = 1 / 2) :
    P {ω | 0 < X ω} = 1 / 2 := by
  extend_space μ
  transfer hf at h
  guard_hyp h : P' {ω | 0 < X (f ω)} = 1 / 2
  exact h

/-- The real-valued measure of an event. -/
example (s : Set Ω) (hs : MeasurableSet s) (r : ℝ) (h : P.real s = r) : P.real s = r := by
  extend_space μ
  transfer hf at h
  exact h

/-- An integral, with an almost-everywhere hypothesis. -/
example (X : Ω → ℝ) (hX : Measurable X) (h : ∀ᵐ ω ∂P, 0 ≤ X ω) : 0 ≤ ∫ ω, X ω ∂P := by
  extend_space μ
  transfer hf at h
  guard_hyp h : ∀ᵐ ω ∂P', 0 ≤ X (f ω)
  exact integral_nonneg_of_ae h

/-- A Lebesgue integral. -/
example (X : Ω → ℝ) (hX : Measurable X) (c : ENNReal) (h : ∫⁻ ω, ‖X ω‖ₑ ∂P = c) :
    ∫⁻ ω, ‖X ω‖ₑ ∂P = c := by
  extend_space μ
  transfer hf at h
  exact h

/-- An almost-everywhere equality. -/
example (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (h : X =ᵐ[P] Y) : X =ᵐ[P] Y := by
  extend_space μ
  transfer hf at h
  guard_hyp h : (fun ω ↦ X (f ω)) =ᵐ[P'] fun ω ↦ Y (f ω)
  exact h

/-- `transfer hf` on a goal, outside of `extend_space`: the goal is moved to the new space and
closed by the hypothesis. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) {Ω' : Type u} [MeasurableSpace Ω']
    {P' : Measure Ω'} (f : Ω' → Ω) (hf : MeasurePreserving f P' P)
    (h : HasLaw (fun ω ↦ X (f ω)) ν P') :
    HasLaw X ν P := by
  transfer hf

/-! ## Using the new draw

A statement that does not mention the space has a trivial `transfer` obligation: this is the
existential form of the tactic. -/

/-- Any random variable has an independent companion with any prescribed law, on a larger space:
`X ∘ f` and `Z`. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (X' : Ω' → ℝ) (Z : Ω' → E), HasLaw X' ν P' ∧ HasLaw Z μ P' ∧ IndepFun X' Z P' := by
  extend_space μ using P with Ω' P' f hf Z hZ hind
  exact ⟨Ω', inferInstance, P', inferInstance, fun ω ↦ X (f ω), Z, hXν.comp hf.hasLaw, hZ,
    hind.comp hX measurable_id⟩

/-- An i.i.d. sequence, by extending with `Measure.infinitePi`: `Z ω : ℕ → E`. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (hXν : HasLaw X ν P) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (X' : Ω' → ℝ) (Z : ℕ → Ω' → E), HasLaw X' ν P' ∧ (∀ n, HasLaw (Z n) μ P')
        ∧ iIndepFun Z P' ∧ IndepFun X' (fun ω n ↦ Z n ω) P' := by
  extend_space Measure.infinitePi (fun _ : ℕ ↦ μ) using P with Ω' P' f hf Z hZ hind
  have hZn (n : ℕ) : HasLaw (fun ω ↦ Z ω n) μ P' :=
    (measurePreserving_eval_infinitePi _ n).hasLaw.comp hZ
  exact ⟨Ω', inferInstance, P', inferInstance, fun ω ↦ X (f ω), fun n ω ↦ Z ω n,
    hXν.comp hf.hasLaw, hZn, (iIndepFun_iff_hasLaw_Pi_infinitePi hZn hZ.aemeasurable).2 hZ,
    hind.comp hX measurable_id⟩

/-! ## A draw with a conditional law -/

/-- `extend_space κ` for a kernel on `Ω`: the draw has conditional law `κ` given the old space, and
there is no independence hypothesis. For a law conditional on `X`, extend with `κ.comap X hX` and
read `hZ` through `HasCondDistrib.comp_right`. -/
example (X : Ω → ℝ) (hX : Measurable X) (κ : Kernel ℝ E) [IsMarkovKernel κ] (ν : Measure ℝ)
    (hXν : HasLaw X ν P) :
    P.map X = ν := by
  extend_space (κ.comap X hX) with Ω' P' f hf Z hZ
  guard_hyp hZ : HasCondDistrib Z f (κ.comap X hX) P'
  have hZ' : HasCondDistrib Z (fun ω ↦ X (f ω)) κ P' := hZ.comp_right
  transfer hf at hXν
  exact hXν.map_eq

/-! ## Universes -/

/-- `Ω` and `E` in the same universe. -/
example {E' : Type u} [MeasurableSpace E'] (μ' : Measure E') [IsProbabilityMeasure μ']
    (X : Ω → ℝ) (hX : Measurable X) : P.map X = P.map X := by
  extend_space μ'
  rfl

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

/--
error: transfer: the goal is not a `transfer` obligation. It should have the form
  ∀ Ω' [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (f : Ω' → Ω), MeasurePreserving f P' P → T' → T
but is
  True
-/
#guard_msgs in
example : True := by
  transfer

end RDo.Example.Extend

end

end
