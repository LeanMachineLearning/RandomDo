module

public import Test.Common

set_option linter.style.header false

/-!
# The `MeasurableSpaceMonad` laws at `Measure`

`Measure` is the one `LawfulMeasurableSpaceMonad` instance the library provides. Each law is
guarded by measurability hypotheses, which is what makes the Giry monad fit the class at all, so
these tests also record the exact shape each law is stated in.
-/

open MeasureTheory ProbabilityTheory MeasurableSpacePure MeasurableSpaceBind
  MeasurableSpaceFunctor

@[expose] public section

namespace Test.MonadLaws

variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

example (a : α) {f : α → Measure β} (hf : Measurable f) : (mPure a : Measure α) >>=ₘ f = f a :=
  LawfulMeasurableSpaceMonad.mPure_mBind a hf

example (μ : Measure α) : μ >>=ₘ mPure = μ := mBind_mPure μ

example (μ : Measure α) {f : α → Measure β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) :
    μ >>=ₘ f >>=ₘ g = μ >>=ₘ fun a ↦ f a >>=ₘ g :=
  LawfulMeasurableSpaceMonad.mBind_assoc μ hf hg

example {f : α → β} (hf : Measurable f) (μ : Measure α) :
    μ >>=ₘ (fun a ↦ mPure (f a)) = f <$>ₘ μ :=
  LawfulMeasurableSpaceMonad.mBind_mPure_comp hf μ

example {f : α → β} (hf : Measurable f) (a : α) :
    f <$>ₘ (mPure a : Measure α) = mPure (f a) := mMap_mPure hf a

example (μ : Measure α) : id <$>ₘ μ = μ := LawfulMeasurableSpaceFunctor.id_mMap μ

example (μ : Measure α) : (fun a ↦ a) <$>ₘ μ = μ := id_mMap' μ

example {f : α → β} (hf : Measurable f) (μ : Measure α) :
    f <$>ₘ μ = μ >>=ₘ fun a ↦ mPure (f a) := mMap_eq_mPure_mBind hf μ

/-! `mPure` and `mBind` are themselves measurable, which is what lets the laws compose. -/

example : Measurable (mPure : α → Measure α) := LawfulMeasurableSpaceMonad.measurable_mPure

example {f : α → Measure β} (hf : Measurable f) : Measurable fun μ : Measure α ↦ μ >>=ₘ f :=
  LawfulMeasurableSpaceMonad.measurable_mBind hf

end Test.MonadLaws

end
