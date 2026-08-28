module

public import RandomDo.Tactic.Elab
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.Algorithm
public import Mathlib.Topology.Separation.CompletelyRegular

set_option linter.style.header false

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

/- # Term decomposition -/

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

def test1 : Measure ℝ := rdo
  let x ← μ
  return x

example : IsProbabilityMeasure (test1 μ) := by
  unfold test1
  infer_instance

def test2 : Measure ℝ := rdo
  let x ← μ
  let y ← μ
  return x + y

example : IsProbabilityMeasure (test2 μ) := by
  unfold test2
  apply isProbabilityMeasure_of_isMarkov
  refine IsMarkov.mBind ?_ ?_
  · apply IsMarkov.const
    infer_instance
  · refine IsMarkov.mBind ?_ ?_
    · apply IsMarkov.const
      infer_instance
    · apply IsMarkov.mPure_comp
      fun_prop

def test3 (c : ℝ) : Measure ℝ := rdo
  let x ← μ
  let y ← μ
  return x + y + c

example : IsMarkov (test3 μ) := by
  unfold test3
  refine IsMarkov.mBind ?_ ?_
  · apply IsMarkov.const
    infer_instance
  · refine IsMarkov.mBind ?_ ?_
    · apply IsMarkov.const
      infer_instance
    · apply IsMarkov.mPure_comp
      fun_prop

/- # The `is_markov` tactic -/

example : IsProbabilityMeasure (test1 μ) := by is_markov

example : IsProbabilityMeasure (test2 μ) := by is_markov

example : IsMarkov (test3 μ) := by is_markov

example (ν : Measure ℝ) : IsMarkov (test3 ν) := by
  is_markov
  sorry

def test4 (f : ℝ → ℝ) {n : ℕ} (hist : Vector ℝ n) : Measure ℝ := rdo
  let mut S := 0
  for r in hist rdo
    S := S + r
  S := S / n
  let x ← gaussianReal S 1
  return f x

example (f : ℝ → ℝ) {n : ℕ} : IsMarkov (test4 f (n := n)) := by
  is_markov
  sorry

example {f : ℝ → ℝ} (hf : Measurable f) {n : ℕ} : IsMarkov (test4 f (n := n)) := by
  is_markov

def test5 : Measure ℝ := rdo
  for _ in List.range 10 rdo
    let x ← gaussianReal 0 1
    if x > 0 then
      return x
  return 0

example : IsProbabilityMeasure test5 := by
  is_markov

/- # Thompson sampling -/

def thompson {K n : ℕ} (hK : 0 < K) (hist : Vector (Fin K × ℝ) n) :
    Measure (Fin K) := rdo
  let mut N : Fin K → ℝ := fun _ ↦ 1
  let mut S : Fin K → ℝ := fun _ ↦ 0
  for (a, r) in hist rdo
    N := fun j ↦ if j = a then N j + 1 else N j
    S := fun j ↦ if j = a then S j + r else S j
  let mut θ : Fin K → ℝ := fun _ ↦ 0
  for j in List.finRange K rdo
    let z ← gaussianReal (S j / N j) (Real.toNNReal (1 / N j))
    θ := fun k ↦ if k = j then z else θ k
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  return argmax θ

variable {K n : ℕ} (hK : 0 < K)

attribute[fun_prop] Measurable.ite

instance : IsMarkov (thompson (n := n) hK) := by
  is_markov
  /- · refine ForInStep.measurable_yield.comp ?_
    refine Measurable.prodMk ?_ ?_
    · refine measurable_pi_lambda _ fun k ↦ ?_
      fun_prop (disch := measurability)
      refine Measurable.ite (by measurability) ?_ ?_
      · fun_prop
      · fun_prop
    · refine measurable_pi_lambda _ fun k ↦ ?_
      refine Measurable.ite (by measurability) ?_ ?_
      · fun_prop
      · fun_prop
  · intro i hi
    refine ForInStep.measurable_yield.comp ?_
    refine measurable_pi_lambda _ fun k ↦ ?_
    refine Measurable.ite (by measurability) ?_ ?_
    · fun_prop
    · fun_prop -/

--#check (thompson (n := n) hK).algorithm

instance : IsMarkovKernel <| IsMarkov.toKernel (thompson (n := n) hK) := inferInstance

def Vector.v_equiv {α : Type*} [MeasurableSpace α] {n : ℕ} : (Finset.Iic n → α) ≃ᵐ Vector α n := by
  sorry

open Learning in
example : Algorithm (Fin K) ℝ where
  policy n :=
    (IsMarkov.toKernel (thompson (n := n) hK)).comap Vector.v_equiv (by fun_prop)
  p0 := IsMarkov.toKernel (thompson (n := 0) hK) #v[]

variable {κ : Kernel ℝ ℝ} {s : Set ℝ} (hs : MeasurableSet s)

attribute[fun_prop] ProbabilityTheory.Kernel.measurable_coe

example : Measurable fun a => κ a s := by
  fun_prop (disch := measurability)

end
