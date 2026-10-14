module

public import RandomDo
public meta import RandomDo.DifferentialPrivacy.Programs
import Mathlib.Tactic

set_option linter.style.header false

open DifferentialPrivacy MeasureTheory ProbabilityTheory
open scoped NNReal

@[expose] public section

namespace Test.DifferentialPrivacy

-- Insertion works in the middle of a sequence and keeps multiplicities.
example : Dataset.AddRemove ([1, 2, 2] : Dataset ℕ) [1, 7, 2, 2] :=
  Or.inl ⟨[1], [2, 2], 7, rfl, rfl⟩

example : Dataset.AddRemove ([1, 7, 2, 2] : Dataset ℕ) [1, 2, 2] :=
  Dataset.AddRemove.symm (Or.inl ⟨[1], [2, 2], 7, rfl, rfl⟩)

example : Dataset.AddRemove ([] : Dataset ℕ) [3] := Or.inl ⟨[], [], 3, rfl, rfl⟩

example : ¬ Dataset.AddRemove ([1, 2] : Dataset ℕ) [1, 3] := by
  intro h
  rcases h.length with h | h <;> norm_num at h

example : Dataset.ReplaceOne ([1, 2] : Dataset ℕ) [1, 3] :=
  ⟨[1], [], 2, 3, rfl, rfl⟩

example : empiricalMean (id : ℝ → ℝ) [1, 2, 3] = 2 := by norm_num [empiricalMean]

-- A diameter bound alone cannot protect the jump from an empty dataset to a translated domain.
example : ¬ HasSensitivity Dataset.AddRemove (empiricalMean (fun _ : Unit ↦ (100 : ℝ))) 0 := by
  intro h
  have h' := h (x := []) (y := [()]) (Or.inl ⟨[], [], (), rfl, rfl⟩)
  norm_num at h'

/-- A concrete bounded domain for the end-to-end privacy examples. -/
theorem unitInterval_diameter : HasDiameter (fun x : Set.Icc (0 : ℝ) 1 ↦ (x : ℝ)) 1 := by
  intro a b
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [a.property.1, a.property.2, b.property.1, b.property.2]

-- Privacy of the actual scalar rdo program, including epsilon > 1.
example : ApproxDP (Dataset.AtLeast 10 Dataset.AddRemove) 2 (1 / 100)
    (Mechanism.ofMeasure
      (gaussianMeanRealProgram (m := Measure) (fun x : Set.Icc (0 : ℝ) 1 ↦ (x : ℝ)) 1
        (gaussianNoiseMultiplier 2 (1 / 100)) 10) (fun _ ↦ inferInstance)) :=
  gaussianMeanRealProgram_approxDP_addRemove unitInterval_diameter (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [div_le_iff₀])

example {α : Type*} {d : ℕ} (f : α → EuclideanSpace ℝ (Fin d)) {D ε δ : ℝ≥0}
    (hD : HasDiameter f D) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast 10 Dataset.ReplaceOne) ε δ
      (Mechanism.ofMeasure
        (gaussianMeanProgram (m := Measure) (fun a ↦ ⇑(f a)) D
          (gaussianNoiseMultiplier ε δ) 10) (fun _ ↦ inferInstance)) :=
  gaussianMeanProgram_approxDP_replaceOne hD (by norm_num) hε hδ hδ1

-- Zero diameter is supported by calibration, without requiring positive Gaussian variance.
example : ApproxDP (Dataset.AtLeast 1 Dataset.AddRemove) 1 (1 / 100)
    (Mechanism.ofMeasure
      (gaussianMeanRealProgram (m := Measure) (fun _ : Unit ↦ (100 : ℝ)) 0
        (gaussianNoiseMultiplier 1 (1 / 100)) 1) (fun _ ↦ inferInstance)) := by
  apply gaussianMeanRealProgram_approxDP_addRemove
  · intro a b; simp
  all_goals norm_num [div_le_iff₀]

example (ε δ : ℝ≥0) : gaussianStddev 0 ε δ = 0 := by simp [gaussianStddev]

example (D ε δ : ℝ≥0) : gaussianStddev (2 * D) ε δ = 2 * gaussianStddev D ε δ := by
  simp only [gaussianStddev]
  ring

example {X : Type*} (adj : X → X → Prop) (μ : ProbabilityMeasure ℝ) :
    PureDP adj 0 (fun _ ↦ μ) := ApproxDP.const adj μ

example {X : Type*} {adj : X → X → Prop} {ε δ : ℝ≥0} {M : Mechanism X ℝ}
    (h : ApproxDP adj ε δ M) : ApproxDP adj ε δ (M.postprocess (fun x ↦ x + 1) (by fun_prop)) :=
  h.postprocess (by fun_prop)

-- The recursive program is a product law, including zero output dimensions.
example {d : ℕ} (center : Fin d → ℝ) (σ : ℝ≥0) :
    gaussianCoordinates (m := Measure) center σ =
      Measure.pi (fun i ↦ gaussianReal (center i) (σ ^ 2)) :=
  gaussianCoordinates_real center σ

-- The full program has the certified law, for arbitrary record embeddings and dataset lengths.
example {α : Type*} (f : α → ℝ) (D c : ℝ≥0) (n : ℕ) (xs : Dataset α) :
    gaussianMeanRealProgram (m := Measure) f D c n xs =
      (gaussianMeanReal f D c n xs : Measure ℝ) :=
  gaussianMeanRealProgram_eq_mechanism f D c n xs

example {α : Type*} (f : α → ℝ) (c : ℝ≥0) (n : ℕ) (xs : Dataset α) :
    gaussianMeanRealProgram (m := Measure) f 0 c n xs = Measure.dirac (empiricalMean f xs) := by
  rw [gaussianMeanRealProgram_eq_mechanism]
  simp [gaussianMeanReal]

example : IsProbabilityMeasure
    (gaussianMeanProgram (m := Measure) (id : (Fin 0 → ℝ) → Fin 0 → ℝ)
      (0 : ℝ≥0) 1 1 [Fin.elim0]) :=
  inferInstance

example : gaussianMeanRealProgram (m := Measure) (id : ℝ → ℝ) (2 : ℝ≥0) 3 2 [1, 3] =
    gaussianReal 2 9 := by
  rw [gaussianMeanRealProgram_eq_mechanism]
  norm_num [gaussianMeanReal, gaussianMechanismReal, Mechanism.ofMeasure, empiricalMean]

-- These commands only run the same rdo definitions with the project's existing sampling backend.
-- The algorithms themselves never depend on IO or on a particular random-number generator.
open NumLean

run_cmd do
  let actual ← IO.runRandPCGWith (m := IO) 42
    (gaussianMeanRealProgram (m := RandM) (id : Float → Float) (2 : Float) 3 2 [1, 3])
  let noise ← IO.runRandPCGWith (m := IO) 42 (NumLean.normal' 0 9)
  unless actual == 2 + noise do throwError "incorrect scalar mean or Gaussian variance"
  -- The actual private size changes the mean, but not the public noise scale.
  let larger ← IO.runRandPCGWith (m := IO) 42
    (gaussianMeanRealProgram (m := RandM) (id : Float → Float) (2 : Float) 3 2 [1, 3, 1, 3])
  unless larger == actual do throwError "noise scale depends on private dataset size"
  let doubled ← IO.runRandPCGWith (m := IO) 42
    (gaussianMeanRealProgram (m := RandM) (id : Float → Float) (4 : Float) 3 2 [1, 3])
  unless (doubled - (2 + 2 * noise)).abs < 1e-12 do
    throwError "noise scale is not proportional to public diameter"
  let halved ← IO.runRandPCGWith (m := IO) 42
    (gaussianMeanRealProgram (m := RandM) (id : Float → Float) (2 : Float) 3 4 [1, 3, 1, 3])
  unless (halved - (2 + noise / 2)).abs < 1e-12 do
    throwError "noise scale is not inversely proportional to public minimum size"
  let noNoise ← IO.runRandPCGWith (m := IO) 42
    (gaussianMeanRealProgram (m := RandM) (id : Float → Float) (0 : Float) 3 2 [7, 7])
  unless noNoise == 7 do throwError "zero diameter added noise"

run_cmd do
  let actual ← IO.runRandPCGWith (m := IO) 42
    (gaussianMeanProgram (m := RandM) (id : (Fin 2 → Float) → Fin 2 → Float)
      (5 : Float) 2 2 [![0, 0], ![3, 4]])
  let expected ← IO.runRandPCGWith (m := IO) 42 do
    let x ← NumLean.normal' 0 25
    let y ← NumLean.normal' 0 25
    pure (1.5 + x, 2 + y)
  unless actual 0 == expected.1 && actual 1 == expected.2 do
    throwError "vector mean must use independent Gaussian coordinates in index order"
  let _ ← IO.runRandPCGWith (m := IO) 42
    (gaussianMeanProgram (m := RandM) (id : (Fin 0 → Float) → Fin 0 → Float)
      (5 : Float) 2 2 [Fin.elim0, Fin.elim0])

end Test.DifferentialPrivacy
