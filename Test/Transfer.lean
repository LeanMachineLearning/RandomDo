module

public import RandomDo.Probability.MeasurePreserving
public import RandomDo.Probability.Transfer

set_option linter.style.header false

/-!
# The `transfer` tactic on its own

`transfer` is mostly run by `extend_space` and `alg_env_trace` on the obligations they leave, and
is tested with them. Here it is used directly, in each of its forms: on the goal, on hypotheses,
where the rewriting by the `@[transfer]` lemmas and the fallback on the `@[transfer_forward]`
lemmas both show, on both at once, and on a `transfer` obligation. Then come the errors: a target
about the old space that the tactic cannot move is an error, not a silent no-op.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

noncomputable section

namespace Test.Transfer

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {Ω' : Type u} [MeasurableSpace Ω']
  {P' : Measure Ω'} {f : Ω' → Ω}

section Map

variable (hf : MeasurePreserving f P' P)
include hf

/-! ## On the goal -/

/-- `transfer hf` on a goal: the goal is moved to the new space and closed by the hypothesis. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (h : HasLaw (fun ω ↦ X (f ω)) ν P') :
    HasLaw X ν P := by
  transfer hf

/-- The side conditions are discharged by `fun_prop`, here the strong measurability of a product.
Once rewritten, the two sides agree and `simp` closes the goal. -/
example (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    ∫ ω, X ω * Y ω ∂P = ∫ ω, X (f ω) * Y (f ω) ∂P' := by
  transfer hf

/-- Events: an event `X ⁻¹' t` given by a random variable becomes `(fun ω ↦ X (f ω)) ⁻¹' t`, as
`extend_space` writes it, and a set-builder event has the map pushed inside. -/
example (X : Ω → ℝ) (hX : Measurable X) (t : Set ℝ) (ht : MeasurableSet t) (c c' : ENNReal)
    (h : P' ((fun ω ↦ X (f ω)) ⁻¹' t) = c) (h' : P' {ω | 0 < X (f ω)} = c') :
    P (X ⁻¹' t) = c ∧ P {ω | 0 < X ω} = c' := by
  transfer hf
  guard_target =ₐ P' ((fun ω ↦ X (f ω)) ⁻¹' t) = c ∧ P' {ω | 0 < X (f ω)} = c'
  exact ⟨h, h'⟩

/-! ## On hypotheses -/

/-- `transfer hf at h` rewrites with the `@[transfer]` lemmas when it can, and falls back on the
`@[transfer_forward]` lemmas otherwise. -/
example (X : Ω → ℝ) (hX : Measurable X) (s : Set Ω) (hs : MeasurableSet s) (h : P s = 1) :
    P' (f ⁻¹' s) = 1 ∧ MeasurableSet (f ⁻¹' s) ∧ Measurable fun ω ↦ X (f ω) := by
  transfer hf at hX hs h
  guard_hyp hX : Measurable fun ω ↦ X (f ω)
  guard_hyp hs : MeasurableSet (f ⁻¹' s)
  guard_hyp h : P' (f ⁻¹' s) = 1
  exact ⟨h, hs, hX⟩

/-- Independence, rewritten with the measurability hypotheses as side conditions. -/
example (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IndepFun (fun ω ↦ X (f ω)) (fun ω ↦ Y (f ω)) P' := by
  transfer hf at hXY
  exact hXY

/-- A definition is transported as itself. Without measurability hypotheses no `@[transfer]` lemma
rewrites a conditional law, and the `@[transfer_forward]` lemma that transports it is the one about
`HasCondDistrib`, not the one about the `HasLaw` it unfolds to. -/
example (X Y : Ω → ℝ) (κ : Kernel ℝ ℝ) (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ Y (f ω)) (fun ω ↦ X (f ω)) κ P' := by
  transfer hf at h
  guard_hyp h : HasCondDistrib (fun ω ↦ Y (f ω)) (fun ω ↦ X (f ω)) κ P'
  exact h

/-- A hypothesis with binders is transported under them, whether by rewriting or by a
`@[transfer_forward]` lemma. -/
example (A : ℕ → Ω → ℝ) (hA : ∀ n, Measurable (A n)) (ν : Measure ℝ)
    (h : ∀ n, HasLaw (A n) ν P) :
    ∀ n, HasLaw (fun ω ↦ A n (f ω)) ν P' := by
  transfer hf at h hA
  guard_hyp hA : ∀ n, Measurable fun ω ↦ A n (f ω)
  guard_hyp h : ∀ n, HasLaw (fun ω ↦ A n (f ω)) ν P'
  exact h

/-- Mutual independence of a family. -/
example (A : ℕ → Ω → ℝ) (hA : ∀ n, Measurable (A n)) (h : iIndepFun A P) :
    iIndepFun (fun n ω ↦ A n (f ω)) P' := by
  transfer hf at h
  exact h

/-! ## On the goal and hypotheses at once

The goal goes first: transporting `hX` destroys the measurability of `X`, which the side condition
of the goal needs. -/

example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (h : HasLaw (fun ω ↦ X (f ω)) ν P') :
    P.map X = ν := by
  transfer hf at hX ⊢
  guard_hyp hX : Measurable fun ω ↦ X (f ω)
  guard_target =ₐ P'.map (fun ω ↦ X (f ω)) = ν
  exact h.map_eq

/-- `transfer hf at *` transfers what it can and leaves alone what is not about the old space: a
hypothesis about the new space, the map itself, a hypothesis about neither. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) (h : HasLaw X ν P) (Z : Ω' → ℝ)
    (hZ : HasLaw Z ν P') (n m : ℕ) (hn : n < m) :
    P.map X = ν ∧ HasLaw Z ν P' ∧ n < m := by
  transfer hf at *
  guard_hyp hX : Measurable fun ω ↦ X (f ω)
  guard_hyp h : HasLaw (fun ω ↦ X (f ω)) ν P'
  guard_hyp hZ : HasLaw Z ν P'
  guard_hyp hf : MeasurePreserving f P' P
  guard_hyp hn : n < m
  guard_target =ₐ P'.map (fun ω ↦ X (f ω)) = ν ∧ HasLaw Z ν P' ∧ n < m
  exact ⟨h.map_eq, hZ, hn⟩

end Map

/-! ## The obligation of `extend_space` -/

/-- `transfer` alone: the new space, the map and the statement on the new space are introduced,
the goal is transferred and closed with that statement. -/
example (s : Set Ω) (hs : MeasurableSet s) :
    ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (f : Ω' → Ω),
      MeasurePreserving f P' P → P' (f ⁻¹' s) = 1 → P s = 1 := by
  transfer

/-! ## Errors -/

/--
error: transfer: the goal is not a `transfer` obligation. It should have the form
  ∀ Ω' [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (f : Ω' → Ω), MeasurePreserving f P' P → T' → T
but is
  True
-/
#guard_msgs in
example : True := by
  transfer

/--
error: transfer: could not close the goal after transferring it:
  P' (f ⁻¹' s) = 1
with the statement on the new space:
  P' (f ⁻¹' s) = 2
-/
#guard_msgs in
example (s : Set Ω) (hs : MeasurableSet s) :
    ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (f : Ω' → Ω),
      MeasurePreserving f P' P → P' (f ⁻¹' s) = 2 → P s = 1 := by
  transfer

/--
error: transfer: `at` needs the map to transfer along, as in `transfer hf at h`
-/
#guard_msgs in
example : True → True := by
  intro _h
  transfer at _h

-- A hypothesis about the old space that nothing transfers is an error, not a silent no-op.
/--
error: transfer: nothing transfers the hypothesis h :
  (P.restrict s) Set.univ = 1
No `@[transfer]` lemma rewrites it and no `@[transfer_forward]` lemma transports it.
A side condition, such as the measurability of a random variable, may not have been discharged.
-/
#guard_msgs in
example (s : Set Ω) (h : P.restrict s Set.univ = 1) (hf : MeasurePreserving f P' P) : True := by
  transfer hf at h

-- Without the measurability of `X`, the side condition fails and the goal cannot be rewritten:
-- an error, and nothing the discharger tried leaks into the messages.
/--
error: transfer: no `@[transfer]` lemma rewrites the goal
  HasLaw X ν P
A side condition, such as the measurability of a random variable, may not have been discharged.
-/
#guard_msgs in
example (X : Ω → ℝ) (ν : Measure ℝ) (hf : MeasurePreserving f P' P) : HasLaw X ν P := by
  transfer hf

/--
error: transfer: nothing to transfer
-/
#guard_msgs in
example (hf : MeasurePreserving f P' P) (n m : ℕ) (hn : n < m) : n < m := by
  transfer hf at *

end Test.Transfer

end

end
