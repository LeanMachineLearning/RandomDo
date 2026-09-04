module

public import Test.Common

set_option linter.style.header false

/-!
# The `transfer` tactic on its own

`transfer` is mostly run by `extend_space` and `alg_env_trace` on the obligations they leave, and
is tested with them. Here it is used directly: on a goal, and on hypotheses, where the rewriting
by the `@[transfer]` lemmas and the fallback on the `@[transfer_forward]` lemmas both show.
-/

open MeasureTheory ProbabilityTheory RDo

@[expose] public section

noncomputable section

namespace Test.Transfer

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- `transfer hf` on a goal: the goal is moved to the new space and closed by the hypothesis. -/
example (X : Ω → ℝ) (hX : Measurable X) (ν : Measure ℝ) {Ω' : Type u} [MeasurableSpace Ω']
    {P' : Measure Ω'} (f : Ω' → Ω) (hf : MeasurePreserving f P' P)
    (h : HasLaw (fun ω ↦ X (f ω)) ν P') :
    HasLaw X ν P := by
  transfer hf

/-- `transfer hf at h` rewrites with the `@[transfer]` lemmas when it can, and falls back on the
`@[transfer_forward]` lemmas otherwise. -/
example (X : Ω → ℝ) (hX : Measurable X) (s : Set Ω) (hs : MeasurableSet s) (h : P s = 1)
    {Ω' : Type u} [MeasurableSpace Ω'] {P' : Measure Ω'} (f : Ω' → Ω)
    (hf : MeasurePreserving f P' P) :
    P' (f ⁻¹' s) = 1 ∧ MeasurableSet (f ⁻¹' s) ∧ Measurable fun ω ↦ X (f ω) := by
  transfer hf at hX hs h
  guard_hyp hX : Measurable fun ω ↦ X (f ω)
  guard_hyp hs : MeasurableSet (f ⁻¹' s)
  guard_hyp h : P' (f ⁻¹' s) = 1
  exact ⟨h, hs, hX⟩

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

end Test.Transfer

end

end
